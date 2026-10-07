# The American King James Version (AKJV)

`akjv.txt.gz` is the complete text of the American King James Version of
the Bible. It's a consensus constant: proof of work and transaction
signatures are bound to its exact bytes (see `docs/BIBLE.md`), so those
bytes must never change. The file is never re-compressed. Consensus uses
it exactly as it is, in 32-byte blocks.

## Pinned bytes

| File | Size | SHA-256 |
|---|---|---|
| `akjv.txt.gz` (as shipped; consensus) | 1,291,059 bytes | `588e4392bb06bf4bf724ee9bb9404b753f9c9c8a0f5928eac2c9d7d0b670043f` |
| the text it decompresses to | 4,340,917 bytes | `a6ac44bbd5cb664fff1ec9dc0cabaacb2d87edc7c3779163d87b101b4ee6bce4` |

To read it: `gunzip -c data/akjv.txt.gz | less`. It holds 31,102 verses,
all 66 books, UTF-8 with LF line endings.

## Provenance

- **Text:** `formats/txt/AKJV.txt` from
  [scrollmapper/bible_databases](https://github.com/scrollmapper/bible_databases)
  at commit `e1b254cef86d0e65b1a5d1a94b8b112d0f296a2c` (2026-07-10), used
  byte for byte. That repository converts the CrossWire SWORD module
  [AKJV](https://www.crosswire.org/sword/modules/ModInfo.jsp?modName=AKJV)
  (version 2.1, 2023-12-27).
- **Compressed** once, with GNU gzip 1.12: `gzip -9 -n` (`-n`: no name or
  timestamp in the header).

## License

**The text is in the public domain.** Its author, Michael Peter (Stone)
Engelbrite, dedicated it to the public domain:

> I am hereby putting the American King James version of the Bible into
> the public domain on November 8, 1999.
>
> You may use it in any manner you wish: copy it, sell it, modify it, etc.
> You can't copyright it or prevent others from using it. You can't claim
> that you created it, because you didn't.

(As quoted on CrossWire's module page. CrossWire's metadata labels the
module "Copyrighted; Free non-commercial distribution", which conflicts
with the dedication it quotes. The author's dedication governs the text.)

The conversion to plain text is scrollmapper's, under the MIT License:

```
MIT License

Copyright (c) 2024 Scrollmapper

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
