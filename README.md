# zurl

A production WHATWG-URL parser in Zig (0.16), written to be **byte-compatible
with [Ada](https://github.com/ada-url/ada)** (`ada::parse<ada::url_aggregator>`,
with and without a base URL) while beating its `benchdata` benchmark on the
same machine.

## Results (Apple M5, arm64)

Dataset: `ada-url/url-dataset` `out.txt` — 100,025 real-world URLs,
8.69 MB, 86.9 bytes/URL average. Same file, same machine, interleaved runs.
Workload: full parse + normalized href + component offsets
(the `BasicBench_AdaURL_aggregator_href` benchmark).

| parser | ns/URL | throughput |
|---|---|---|
| Ada `url_aggregator` (C++20, Release) | 74.4–82.2 | ~1.1 GB/s |
| **zurl (caller-owned buffers)** | **23.9–24.6** | **3.5+ GB/s** |

**~3.1–3.3x faster than Ada** (same-session A/B; Ada's run-to-run spread is
74–82 ns, zurl's is 24–25). Ada is the fastest known compliant parser; the
widely-cited "188 ns/URL" figure is Ada on slower server hardware — on this
M5 Ada runs at ~74–82 ns/URL, so that is the bar used here. For reference on
the same machine: `ada::url` ~118 ns/URL, `whatwg-url`-C++ ~274 ns/URL,
curl ~686 ns/URL.

## Correctness — zero known divergences from Ada

Differential-tested against a local Ada build (`dump_ada` dumps ground truth;
`zurl dump` / `zurl wpt` are the Zig side). Every suite below currently
reports **0 mismatches**:

| suite | size | what it covers |
|---|---|---|
| url-dataset dump | 100,025 | real-world URLs, href + accept/reject parity |
| WPT `urltestdata.json` with base (`zurl wpt`) | 891 | full base-URL resolution, href **and** origin |
| WPT `ada_extra_urltestdata.json` with base | 28 | Ada's own extra edge cases |
| WPT base-less dump (subset of urltestdata) | 556 | base-less parses |
| WPT `IdnaTestV2` (`zidnatest`) | 2,671 | full UTS-46: mapping, NFC, validity, punycode |
| WPT `toascii` (`zidnatest`) | 87 | percent-decode + forbidden-code-point wrapper |
| hand-written probes | ~200 | IPv4/IPv6, userinfo, ports, dot segments, `/.` rule, tab/newline, drive letters |
| differential fuzzing | 3,028 mutants | 0 accept/reject flips, 0 crashes (also under ReleaseSafe) |

The IDNA implementation is a line-by-line port of Ada's `ada_idna.cpp`
(mapping, uni-algo-style NFC, punycode, ContextJ/bidi validity, the
`unicode::to_ascii` wrapper) with the same 224 KB of UTS-46 tables, sliced at
comptime from `src/idna_tables.bin`.

## API

```zig
const url = @import("url.zig");

var u: url.Url = undefined;
if (url.parse(input, out, scratch, &u)) {
    // u.href, u.protocol(), u.username(), u.password(), u.host(),
    // u.hostname(), u.port(), u.pathname(), u.search(), u.hash(),
    // u.origin(buf, scratch2)  (handles blob: inner-URL origins)
}
var r: url.Url = undefined;
if (url.parseBase(input, &base_url, out, scratch, &r)) { ... }
```

Buffer contract (n = input.len, caller-owned, reusable across parses):

- `out.len     >= 6*n + 96*min(n, 16384) + 2048`  (UTS-46+punycode worst case)
- `scratch.len >= n + 368*min(n, 49152) + 512`    (IDNA workspace worst case)

The parser never allocates. `Url` slices point into `out`; `base` must not
alias `out`/`scratch`. Typical fast paths never touch the IDNA machinery —
the worst-case sizes above only matter for adversarial non-ASCII hosts.

Not yet implemented: component setters (`set_host` & friends, i.e. WPT
`setters_tests.json`), `can_parse` fast path, URLSearchParams, the `ada_c`
C API. Everything `ada::parse` does is otherwise covered.

## Design notes

Single buffer in, single buffer out; no allocator in the hot path.

- `parseFastAbsolute`: a tight single-pass fast path for the dominant shape
  (`http(s)://` + plain lowercase host + plain path [+ plain query]
  [+ plain fragment]). Any deviation falls back to the general parser, which
  re-does the work; every accept condition mirrors the general path's own
  bulk branch, so outputs are identical by construction. ~99.7% of the
  benchmark dataset takes it. On success the href is the input *verbatim*
  (the fast path only accepts already-normalized URLs), so validation and
  the href copy are **fused into one vector loop** — each 16-byte block is
  classified *and* stored in the same pass, and the final partial block is
  handled by an overlapping vector block (idempotent by construction) rather
  than a per-byte scalar tail. Scan results are packed into a single u64
  register; offsets are computed arithmetically.
- Exact byte classification via the simdjson nibble trick:
  `class(c) = lo_tab[c & 15] & hi_tab[c >> 4]`, two `tbl` instructions per
  16 bytes. The hi/lo tables are **built at comptime from the same `cls`/
  `enc` tables the scalar code consults** (hi-nibble rows grouped by their
  plain-lo mask, one bit per distinct row, ≤ 8 groups), so vector and
  scalar decisions are exact by construction. Lane masks are extracted with
  a 2-instruction `cmeq`+`shrn` movemask (not LLVM's 5-instruction
  `<16 x i1>` bitcast lowering); compare-chain classifiers are the portable
  fallback on non-aarch64 targets.
- Dot segments are validated *inside* the vector scan: `.`/`%` stops are
  only slow when they open a segment (`.`/`..`/`%2e` forms at a segment
  start); benign stops (e.g. `segment.html`, `a%20b`) are skipped within
  the current chunk's bit mask — single pass, no rescanning. Dotted file
  names and ordinary percent-encoded paths stay on the fast path.
- `https://` / `http://` detected with one 8-byte integer compare; the
  scheme prefix is written with a single 8-byte store.
- IPv4/IPv6, UTS-46 hosts, userinfo, ports, backslashes, dot segments and
  percent-encoding all fall off to careful slow paths that mirror Ada's code
  exactly; `..` segments can shorten across pre-written base-path segments
  (`parsePathAt`), and the `/.` host-less serializer artifact is resolved
  against the *logical* base path.
- File URLs follow the WHATWG file state machine: empty host, drive letters
  in host position become path, `localhost` elision, drive inheritance for
  absolute paths (`/` against `file:///C:/a/b` → `file:///C:/`).
- Encode sets as a 256-entry bitmask table (C0/fragment/query/special-query/
  path/userinfo in one byte per char); percent-encoding emits uppercase hex.

## Build & run

```sh
zig build --release=fast           # builds zig-out/bin/{zurl,zidnatest}
# or: zig build-exe src/main.zig -OReleaseFast -lc -femit-bin=zurl

./zig-out/bin/zurl bench <urls.txt>   # benchmark (best-of-N passes)
./zig-out/bin/zurl dump <urls.txt>    # one href or INVALID per line
./zig-out/bin/zurl wpt <resolve.tsv>  # base\tinput hex TSV -> href\torigin

# IDNA suites (no Ada needed, oracles checked in):
./zig-out/bin/zidnatest testdata/idnav2.tsv testdata/idnav2.oracle
./zig-out/bin/zidnatest testdata/toascii.tsv testdata/toascii.oracle

# ground truth dumper (from the repo root, after building ada's benchdata):
c++ -std=c++20 -O2 -I include dump_ada.cpp build-bench/src/libada.a -o dump_ada
./dump_ada resolve testdata/wpt_resolve.tsv | diff - testdata/wpt_resolve_ada.txt
# regenerate vectors after a WPT update:
python3 testdata/gen_resolve_vectors.py
```

## License

Dual-licensed under Apache-2.0 or MIT (see `LICENSE-APACHE`, `LICENSE-MIT`),
matching Ada. The UTS-46 tables (`src/idna_tables.bin`) are derived from
Unicode Character Database data (© Unicode, Inc.; unicode.org/license).
