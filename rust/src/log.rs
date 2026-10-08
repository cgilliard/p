//! Logging: timestamped lines to a file (with rotation) and/or standard
//! output, from any thread.
//!
//! ```text
//! [2026-10-05 16:00:01:012] received block #12 from 10.0.0.7:7701
//! ```
//!
//! Timestamps are UTC, to the millisecond. The level (`(INFO)`) and the
//! source location (`[src/net.rs:141]`) can be added to each line
//! (`Config::show_level`, `Config::show_location`); both are off by
//! default.
//!
//! Log through the macros -- `trace!`, `debug!`, `info!`, `warn!`,
//! `error!`, `fatal!` -- which take `format!`-style arguments, skip all
//! formatting when the level is filtered out, and record where they were
//! called from. They go to the global logger, set up once with `init`;
//! until then (in tests, say) lines go to standard output.
//!
//! # Rotation
//!
//! When the file reaches `max_size_bytes`, or has been in use for
//! `max_age_ms`, it's renamed with the time it was rotated --
//! `node.log` becomes `node.2026-10-05_16-00-01-012.log` -- and a fresh
//! `node.log` started. Rotated names sort by age, and only the newest
//! `max_rotated_files` are kept. Rotation happens as part of logging a
//! line (checked before each write), or on demand with `Logger::rotate`.
//!
//! # Design
//!
//! Adapted from the `bmw` project's logger (`bmw/log`), condensed into
//! one module and reworked:
//!
//! - One logger shared by every thread behind one mutex, rather than a
//!   per-thread clone of a file handle: each line is written whole, with
//!   one `write_all`, so lines from different threads never interleave
//!   or tear, and size and age are tracked in one place -- with
//!   per-thread clones, a rotation by one thread left the others writing
//!   into the renamed file, each with its own idea of the size.
//! - Source locations come from `file!()`/`line!()` in the macros, not
//!   a backtrace walked on every call (slow, and in release builds
//!   reduced to symbol names).
//! - Plain typed configuration fields; the minimum level is a runtime
//!   setting (`set_level`) rather than a constant per scope.
//! - Old rotated files are pruned, and the log's age survives a restart
//!   (it's taken from the file's creation time).
//! - No dependencies: UTC dates are computed here (`civil`).

#![allow(dead_code)]

use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};

/// How important a line is; lines below the logger's level are dropped.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Level {
    Trace = 0,
    Debug = 1,
    Info = 2,
    Warn = 3,
    Error = 4,
    Fatal = 5,
}

impl Level {
    const ALL: [Level; 6] = [Level::Trace, Level::Debug, Level::Info, Level::Warn, Level::Error, Level::Fatal];

    pub fn name(self) -> &'static str {
        match self {
            Level::Trace => "TRACE",
            Level::Debug => "DEBUG",
            Level::Info => "INFO",
            Level::Warn => "WARN",
            Level::Error => "ERROR",
            Level::Fatal => "FATAL",
        }
    }

    /// A level by name, case-insensitively (`"info"`, `"WARN"`, ...).
    pub fn parse(name: &str) -> Option<Level> {
        Level::ALL.into_iter().find(|l| l.name().eq_ignore_ascii_case(name))
    }

    fn from_u8(v: u8) -> Level {
        Level::ALL[(v as usize).min(5)]
    }

    /// The ANSI color for this level on a terminal.
    fn color(self) -> &'static str {
        match self {
            Level::Trace | Level::Debug => "\x1b[35m",
            Level::Info => "\x1b[32m",
            Level::Warn => "\x1b[33m",
            Level::Error | Level::Fatal => "\x1b[31m",
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(Clone, Debug)]
pub struct Config {
    /// The log file, created (with its directory) if missing and appended
    /// to if not. `None`: no file.
    pub file: Option<PathBuf>,
    /// Also write every line to standard output.
    pub stdout: bool,
    /// Color the level on standard output (never in the file).
    pub colors: bool,
    /// The minimum level logged.
    pub level: Level,
    /// Include `(LEVEL)` in each line.
    pub show_level: bool,
    /// Include `[file:line]` in each line.
    pub show_location: bool,
    /// Rotate once the file reaches this many bytes (0: never by size).
    pub max_size_bytes: u64,
    /// Rotate once the file has been in use this long (0: never by age).
    pub max_age_ms: u64,
    /// How many rotated files to keep, newest first (0: keep them all).
    pub max_rotated_files: usize,
    /// A line written at the top of every new log file.
    pub header: Option<String>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            file: None,
            stdout: true,
            colors: false,
            level: Level::Info,
            show_level: false,
            show_location: false,
            max_size_bytes: 10 * 1024 * 1024,
            max_age_ms: 24 * 60 * 60 * 1000,
            max_rotated_files: 10,
            header: None,
        }
    }
}

/// The open file and what rotation needs to know about it.
struct Active {
    file: File,
    size: u64,
    /// When this file was started (Unix milliseconds).
    started_ms: u64,
}

pub struct Logger {
    config: Config,
    level: AtomicU8,
    active: Mutex<Option<Active>>,
}

/// Milliseconds since the Unix epoch, now.
pub fn now_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64)
}

/// A Unix time in milliseconds as UTC calendar fields: `(year, month,
/// day, hour, minute, second, millisecond)`. The date part is Howard
/// Hinnant's `civil_from_days` (a well-known closed form,
/// http://howardhinnant.github.io/date_algorithms.html), so no time zone
/// database or dependency is needed.
pub fn civil(unix_ms: u64) -> (i64, u32, u32, u32, u32, u32, u32) {
    let millis = (unix_ms % 1000) as u32;
    let secs = unix_ms / 1000;
    let (days, rem) = ((secs / 86_400) as i64, secs % 86_400);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    let year = yoe + era * 400 + i64::from(month <= 2);
    (year, month, day, (rem / 3600) as u32, (rem % 3600 / 60) as u32, (rem % 60) as u32, millis)
}

/// `2026-10-05 16:00:01:012`.
pub fn format_time(unix_ms: u64) -> String {
    let (y, mo, d, h, mi, s, ms) = civil(unix_ms);
    format!("{y:04}-{mo:02}-{d:02} {h:02}:{mi:02}:{s:02}:{ms:03}")
}

/// `2026-10-05_16-00-01-012`: a timestamp safe in a file name, sorting by
/// time.
fn file_stamp(unix_ms: u64) -> String {
    let (y, mo, d, h, mi, s, ms) = civil(unix_ms);
    format!("{y:04}-{mo:02}-{d:02}_{h:02}-{mi:02}-{s:02}-{ms:03}")
}

/// `(stem, extension)` of a log file name: `("node", ".log")`, or
/// `("node", "")` with no extension.
fn split_name(path: &Path) -> (String, String) {
    let stem = path.file_stem().map_or_else(|| "log".into(), |s| s.to_string_lossy().into_owned());
    let ext = path.extension().map_or_else(String::new, |e| format!(".{}", e.to_string_lossy()));
    (stem, ext)
}

impl Logger {
    /// A logger for `config`, opening (or creating) its file.
    pub fn new(config: Config) -> io::Result<Logger> {
        let active = match &config.file {
            Some(path) => Some(Self::open(path, &config, now_ms())?),
            None => None,
        };
        Ok(Logger {
            level: AtomicU8::new(config.level as u8),
            config,
            active: Mutex::new(active),
        })
    }

    fn open(path: &Path, config: &Config, now: u64) -> io::Result<Active> {
        if path.is_dir() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "the log file path is a directory"));
        }
        if let Some(dir) = path.parent().filter(|d| !d.as_os_str().is_empty()) {
            fs::create_dir_all(dir)?;
        }
        let mut file = OpenOptions::new().create(true).append(true).open(path)?;
        let metadata = file.metadata()?;
        let mut size = metadata.len();
        // An existing file keeps its age across restarts.
        let started_ms = if size == 0 {
            now
        } else {
            metadata
                .created()
                .ok()
                .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
                .map_or(now, |d| d.as_millis() as u64)
        };
        if size == 0
            && let Some(header) = &config.header
        {
            let line = format!("{header}\n");
            file.write_all(line.as_bytes())?;
            size = line.len() as u64;
        }
        Ok(Active { file, size, started_ms })
    }

    pub fn level(&self) -> Level {
        Level::from_u8(self.level.load(Ordering::Relaxed))
    }

    pub fn set_level(&self, level: Level) {
        self.level.store(level as u8, Ordering::Relaxed);
    }

    /// Whether a line at `level` would be logged.
    pub fn enabled(&self, level: Level) -> bool {
        level >= self.level()
    }

    /// Log one line (what the macros call).
    pub fn log(&self, level: Level, file: &str, line: u32, args: fmt::Arguments) {
        self.log_at(now_ms(), level, Some((file, line)), args);
    }

    /// `log` at a given time -- the clock is a parameter so rotation by
    /// age can be tested.
    fn log_at(&self, now: u64, level: Level, location: Option<(&str, u32)>, args: fmt::Arguments) {
        if !self.enabled(level) {
            return;
        }
        let mut prefix = format!("[{}] ", format_time(now));
        let mut level_text = String::new();
        if self.config.show_level {
            level_text = format!("({level}) ");
        }
        if self.config.show_location
            && let Some((file, line)) = location
        {
            prefix = format!("{prefix}{level_text}[{file}:{line}] ");
            level_text.clear();
        }
        let message = args.to_string();

        let mut active = self.active.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(a) = active.as_mut() {
            if self.due(a, now)
                && let Err(e) = self.rotate_locked(&mut active, now)
            {
                eprintln!("log rotation failed: {e}");
            }
            if let Some(a) = active.as_mut() {
                let line = format!("{prefix}{level_text}{message}\n");
                match a.file.write_all(line.as_bytes()) {
                    Ok(()) => a.size += line.len() as u64,
                    Err(e) => eprintln!("log write failed ({e}): {}", line.trim_end()),
                }
            }
        }
        if self.config.stdout {
            let level_text = if self.config.colors && !level_text.is_empty() {
                format!("{}{level_text}\x1b[0m", level.color())
            } else {
                level_text
            };
            // Under the same lock as the file, so the two agree on order.
            let _ = writeln!(io::stdout().lock(), "{prefix}{level_text}{message}");
        }
    }

    fn due(&self, a: &Active, now: u64) -> bool {
        (self.config.max_size_bytes > 0 && a.size >= self.config.max_size_bytes)
            || (self.config.max_age_ms > 0 && now.saturating_sub(a.started_ms) >= self.config.max_age_ms)
    }

    /// Rotate now: rename the current file aside and start a new one.
    pub fn rotate(&self) -> io::Result<()> {
        let mut active = self.active.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        self.rotate_locked(&mut active, now_ms())
    }

    fn rotate_locked(&self, active: &mut Option<Active>, now: u64) -> io::Result<()> {
        let Some(path) = &self.config.file else {
            return Ok(());
        };
        // Close the current file first (required on some platforms).
        *active = None;
        let (stem, ext) = split_name(path);
        let dir = path.parent().filter(|d| !d.as_os_str().is_empty()).unwrap_or(Path::new("."));
        let stamp = file_stamp(now);
        let mut rotated = dir.join(format!("{stem}.{stamp}{ext}"));
        let mut n = 1;
        while rotated.exists() {
            rotated = dir.join(format!("{stem}.{stamp}_{n:03}{ext}"));
            n += 1;
        }
        let renamed = fs::rename(path, &rotated);
        // Whatever happened, keep logging.
        *active = Some(Self::open(path, &self.config, now)?);
        renamed?;
        self.prune(dir, &stem, &ext);
        Ok(())
    }

    /// The rotated files of this log, oldest first.
    fn rotated_files(dir: &Path, stem: &str, ext: &str) -> Vec<PathBuf> {
        let prefix = format!("{stem}.");
        let mut files: Vec<PathBuf> = fs::read_dir(dir)
            .into_iter()
            .flatten()
            .flatten()
            .map(|e| e.path())
            .filter(|p| {
                p.file_name().map(|n| n.to_string_lossy()).is_some_and(|n| {
                    n.starts_with(&prefix)
                        && n.ends_with(ext)
                        && n.len() > prefix.len() + ext.len()
                        && n[prefix.len()..].starts_with(|c: char| c.is_ascii_digit())
                })
            })
            .collect();
        files.sort();
        files
    }

    fn prune(&self, dir: &Path, stem: &str, ext: &str) {
        let keep = self.config.max_rotated_files;
        if keep == 0 {
            return;
        }
        let files = Self::rotated_files(dir, stem, ext);
        for old in files.iter().take(files.len().saturating_sub(keep)) {
            if let Err(e) = fs::remove_file(old) {
                eprintln!("failed to remove old log {}: {e}", old.display());
            }
        }
    }
}

static LOGGER: OnceLock<Logger> = OnceLock::new();

/// Set up the global logger. Fails if it's already set up (or was
/// already used, which sets up a default one) or the file can't be
/// opened.
pub fn init(config: Config) -> io::Result<()> {
    let logger = Logger::new(config)?;
    LOGGER
        .set(logger)
        .map_err(|_| io::Error::new(io::ErrorKind::AlreadyExists, "the logger is already set up"))
}

/// The global logger: as set up by `init`, else one writing to standard
/// output only.
pub fn logger() -> &'static Logger {
    LOGGER.get_or_init(|| Logger::new(Config::default()).expect("a logger without a file always opens"))
}

/// Log at `level` through the global logger (the level macros' common
/// body). Arguments aren't formatted unless the level is enabled.
#[macro_export]
macro_rules! log_at {
    ($level:expr, $($arg:tt)+) => {{
        let logger = $crate::log::logger();
        if logger.enabled($level) {
            logger.log($level, file!(), line!(), format_args!($($arg)+));
        }
    }};
}

#[macro_export]
macro_rules! trace {
    ($($arg:tt)+) => { $crate::log_at!($crate::log::Level::Trace, $($arg)+) };
}

#[macro_export]
macro_rules! debug {
    ($($arg:tt)+) => { $crate::log_at!($crate::log::Level::Debug, $($arg)+) };
}

#[macro_export]
macro_rules! info {
    ($($arg:tt)+) => { $crate::log_at!($crate::log::Level::Info, $($arg)+) };
}

#[macro_export]
macro_rules! warn {
    ($($arg:tt)+) => { $crate::log_at!($crate::log::Level::Warn, $($arg)+) };
}

#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => { $crate::log_at!($crate::log::Level::Error, $($arg)+) };
}

#[macro_export]
macro_rules! fatal {
    ($($arg:tt)+) => { $crate::log_at!($crate::log::Level::Fatal, $($arg)+) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("log-test-{}-{name}-{n}", std::process::id()));
            let _ = fs::remove_dir_all(&path);
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn file_config(path: &Path) -> Config {
        Config {
            file: Some(path.to_path_buf()),
            stdout: false,
            ..Config::default()
        }
    }

    const T0: u64 = 1_791_216_001_012; // 2026-10-05 16:00:01.012 UTC

    #[test]
    fn timestamps_are_utc_with_milliseconds() {
        assert_eq!(format_time(0), "1970-01-01 00:00:00:000");
        assert_eq!(format_time(T0), "2026-10-05 16:00:01:012");
        assert_eq!(format_time(951_782_400_000), "2000-02-29 00:00:00:000"); // leap day
        assert_eq!(file_stamp(T0), "2026-10-05_16-00-01-012");
    }

    #[test]
    fn lines_have_the_requested_format_and_options_add_level_and_location() {
        let dir = TempDir::new("format");
        let path = dir.0.join("node.log");
        let plain = Logger::new(file_config(&path)).unwrap();
        plain.log_at(T0, Level::Info, Some(("src/net.rs", 141)), format_args!("hello {}", 7));
        let annotated = Logger::new(Config {
            show_level: true,
            show_location: true,
            ..file_config(&path)
        })
        .unwrap();
        annotated.log_at(T0, Level::Warn, Some(("src/net.rs", 141)), format_args!("careful"));
        let text = fs::read_to_string(&path).unwrap();
        assert_eq!(
            text,
            "[2026-10-05 16:00:01:012] hello 7\n[2026-10-05 16:00:01:012] (WARN) [src/net.rs:141] careful\n"
        );
    }

    #[test]
    fn levels_below_the_minimum_are_dropped_and_can_be_changed() {
        let dir = TempDir::new("levels");
        let path = dir.0.join("node.log");
        let logger = Logger::new(file_config(&path)).unwrap();
        logger.log_at(T0, Level::Debug, None, format_args!("hidden"));
        logger.log_at(T0, Level::Info, None, format_args!("shown"));
        logger.set_level(Level::Debug);
        logger.log_at(T0, Level::Debug, None, format_args!("now shown"));
        let text = fs::read_to_string(&path).unwrap();
        assert!(!text.contains("hidden") && text.contains("] shown") && text.contains("now shown"));
        assert_eq!(Level::parse("warn"), Some(Level::Warn));
        assert_eq!(Level::parse("loud"), None);
    }

    #[test]
    fn rotation_by_size_keeps_every_line_and_prunes_old_files() {
        let dir = TempDir::new("size");
        let path = dir.0.join("logs").join("node.log");
        let logger = Logger::new(Config {
            max_size_bytes: 200,
            max_rotated_files: 3,
            header: Some("tabernacle log".into()),
            ..file_config(&path)
        })
        .unwrap();
        for i in 0..40 {
            logger.log_at(T0 + i, Level::Info, None, format_args!("line {i:03}"));
        }
        let rotated = Logger::rotated_files(&dir.0.join("logs"), "node", ".log");
        assert_eq!(rotated.len(), 3, "only the newest rotated files are kept");
        // The kept files and the active one hold the newest lines, in
        // order, each file starting with the header.
        let mut lines = Vec::new();
        for file in rotated.iter().chain([&path]) {
            let text = fs::read_to_string(file).unwrap();
            assert!(text.starts_with("tabernacle log\n"));
            assert!(text.len() <= 200 + 40, "{} is {} bytes", file.display(), text.len());
            lines.extend(text.lines().skip(1).map(|l| l.to_string()));
        }
        let numbers: Vec<u32> = lines.iter().map(|l| l[l.len() - 3..].parse().unwrap()).collect();
        assert!(numbers.windows(2).all(|w| w[1] == w[0] + 1), "{numbers:?}");
        assert_eq!(*numbers.last().unwrap(), 39);
    }

    #[test]
    fn rotation_by_age() {
        let dir = TempDir::new("age");
        let path = dir.0.join("node.log");
        let logger = Logger::new(Config {
            max_age_ms: 60_000,
            ..file_config(&path)
        })
        .unwrap();
        let start = logger.active.lock().unwrap().as_ref().unwrap().started_ms;
        logger.log_at(start + 1_000, Level::Info, None, format_args!("early"));
        logger.log_at(start + 59_000, Level::Info, None, format_args!("still early"));
        assert!(Logger::rotated_files(&dir.0, "node", ".log").is_empty());
        logger.log_at(start + 61_000, Level::Info, None, format_args!("late"));
        let rotated = Logger::rotated_files(&dir.0, "node", ".log");
        assert_eq!(rotated.len(), 1);
        assert!(fs::read_to_string(&rotated[0]).unwrap().contains("still early"));
        assert!(fs::read_to_string(&path).unwrap().contains("late"));
    }

    #[test]
    fn manual_rotation_and_name_collisions() {
        let dir = TempDir::new("manual");
        let path = dir.0.join("node.log");
        let logger = Logger::new(file_config(&path)).unwrap();
        logger.log_at(T0, Level::Info, None, format_args!("a"));
        // Two rotations in the same millisecond get distinct names.
        let mut active = logger.active.lock().unwrap();
        logger.rotate_locked(&mut active, T0).unwrap();
        logger.rotate_locked(&mut active, T0).unwrap();
        drop(active);
        let rotated = Logger::rotated_files(&dir.0, "node", ".log");
        assert_eq!(rotated.len(), 2);
        // ...which sort in the order they were made.
        assert!(rotated[0].to_string_lossy().ends_with("node.2026-10-05_16-00-01-012.log"));
        assert!(rotated[1].to_string_lossy().ends_with("node.2026-10-05_16-00-01-012_001.log"));
    }

    #[test]
    fn reopening_appends() {
        let dir = TempDir::new("reopen");
        let path = dir.0.join("node.log");
        Logger::new(file_config(&path)).unwrap().log_at(T0, Level::Info, None, format_args!("first run"));
        let logger = Logger::new(file_config(&path)).unwrap();
        logger.log_at(T0, Level::Info, None, format_args!("second run"));
        let text = fs::read_to_string(&path).unwrap();
        assert_eq!(text.lines().count(), 2);
        assert_eq!(logger.active.lock().unwrap().as_ref().unwrap().size, text.len() as u64);
    }

    #[test]
    fn a_directory_is_not_a_log_file() {
        let dir = TempDir::new("dir");
        fs::create_dir_all(&dir.0).unwrap();
        assert!(Logger::new(file_config(&dir.0)).is_err());
    }

    /// Many threads at once, with rotation going on: every line arrives
    /// whole, exactly once.
    #[test]
    fn concurrent_lines_never_tear_or_go_missing() {
        let dir = TempDir::new("threads");
        let path = dir.0.join("node.log");
        let logger = Arc::new(
            Logger::new(Config {
                max_size_bytes: 4096,
                max_rotated_files: 0,
                ..file_config(&path)
            })
            .unwrap(),
        );
        let threads: Vec<_> = (0..8)
            .map(|t| {
                let logger = logger.clone();
                std::thread::spawn(move || {
                    for i in 0..300 {
                        logger.log_at(T0, Level::Info, None, format_args!("thread {t} line {i} {}", "x".repeat(i % 17)));
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        let mut seen = std::collections::HashSet::new();
        for file in Logger::rotated_files(&dir.0, "node", ".log").iter().chain([&path]) {
            for line in fs::read_to_string(file).unwrap().lines() {
                let rest = line.strip_prefix("[2026-10-05 16:00:01:012] thread ").expect(line);
                let mut parts = rest.split(' ');
                let (t, i): (usize, usize) = (parts.next().unwrap().parse().unwrap(), parts.nth(1).unwrap().parse().unwrap());
                assert_eq!(parts.next().unwrap_or(""), "x".repeat(i % 17), "{line}");
                assert!(seen.insert((t, i)), "duplicate {line}");
            }
        }
        assert_eq!(seen.len(), 8 * 300);
    }
}
