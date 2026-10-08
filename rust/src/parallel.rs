//! Minimal data parallelism on `std::thread::scope` -- no dependency:
//! split an index range into one contiguous chunk per core, compute each
//! chunk on its own thread, and concatenate the results in order.

#![allow(dead_code)]

/// Below this many items, threads cost more than they save.
const MIN_PARALLEL: usize = 1 << 10;

pub fn threads() -> usize {
    std::thread::available_parallelism().map_or(1, |n| n.get())
}

/// `f` applied to consecutive sub-ranges of `0..n` (in parallel when
/// worthwhile), each returning its range's results in order; the results
/// concatenated. `f` sees whole ranges so it can reuse scratch space.
pub fn map_ranges<T: Send>(n: usize, f: impl Fn(std::ops::Range<usize>) -> Vec<T> + Sync) -> Vec<T> {
    let threads = threads();
    if n < MIN_PARALLEL || threads == 1 {
        return f(0..n);
    }
    let chunk = n.div_ceil(threads);
    let f = &f;
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..n)
            .step_by(chunk)
            .map(|start| scope.spawn(move || f(start..(start + chunk).min(n))))
            .collect();
        let mut out = Vec::with_capacity(n);
        for handle in handles {
            out.extend(handle.join().expect("worker thread panicked"));
        }
        out
    })
}

/// `f(i)` for every `i` in `0..n`, spread across threads whenever there's
/// more than one item -- for a few big items (whole columns, say), where
/// `map`'s minimum batch would keep everything on one thread.
pub fn map_each<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let threads = threads().min(n.max(1));
    if threads <= 1 {
        return (0..n).map(f).collect();
    }
    let chunk = n.div_ceil(threads);
    let f = &f;
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..n)
            .step_by(chunk)
            .map(|start| scope.spawn(move || (start..(start + chunk).min(n)).map(f).collect::<Vec<_>>()))
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("worker thread panicked"))
            .collect()
    })
}

/// `f(i)` for every `i` in `0..n`, in parallel when worthwhile.
pub fn map<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    map_ranges(n, |range| range.map(&f).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn results_come_back_complete_and_in_order() {
        for n in [0, 1, 7, MIN_PARALLEL - 1, MIN_PARALLEL, 100_003] {
            let out = map(n, |i| i * 3);
            assert_eq!(out, (0..n).map(|i| i * 3).collect::<Vec<_>>(), "n = {n}");
        }
    }
}
