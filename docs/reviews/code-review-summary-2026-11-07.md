# Code reviews, 7 November 2026: what to address

Every crate was reviewed by reading only, on Opus (the first `syntax` review
ran on Sonnet and was repeated on Opus at Matt's request, D2672). Each review
has its own document; this page puts their recommendations in one order.

| Crate | Review | High | Medium | Low | Tickets |
|---|---|---|---|---|---|
| core | [code-review-core.md](code-review-core.md) | 0 | 9 | 10 | SW-1884 to SW-1890 |
| elab: checking and solving | [code-review-elab-checking.md](code-review-elab-checking.md) | 0 | 6 | 12 | SW-1901 to SW-1911 |
| elab: tactics | [code-review-elab-tactics.md](code-review-elab-tactics.md) | 0 | 7 | 10 | SW-1936 to SW-1942 |
| elab: the rest | [code-review-elab-rest.md](code-review-elab-rest.md) | 0 | 7 | 17 | SW-1925 to SW-1935 |
| rt | [code-review-rt.md](code-review-rt.md) | 0 | 4 | 8 | SW-1891 to SW-1898 |
| js, native | [code-review-js-native.md](code-review-js-native.md) | 0 | 4 | 9 | SW-1943 to SW-1947 |
| syntax (Opus) | [code-review-syntax-opus.md](code-review-syntax-opus.md) | 2 | 6 | 9 | SW-1916 to SW-1918 |
| syntax (Sonnet) | [code-review-syntax.md](code-review-syntax.md) | 0 | 3 | 10 | SW-1873 to SW-1881 |
| driver | [code-review-driver.md](code-review-driver.md) | 0 | 2 | 11 | SW-1919 to SW-1923 |
| cli, lsp, web, fmt, bench, small crates | [code-review-cli-lsp-web-fmt.md](code-review-cli-lsp-web-fmt.md) | 1 | 7 | 14 | SW-1948 to SW-1954 |

## The verdict

No review found a way to make a false theorem check. Everything the
elaborator, the tactics and the derivers build goes to the kernel; the only
path that skips it is check-cache replay, which is intended. The kernel is
better encapsulated than at the 1 November review, and most of that review's
findings are fixed: the native backend's unsafe boundary, the runtime in the
test fingerprint, the language server's unbounded proof actions.

What the reviews did find is at the edges: crashes reachable from input,
state that isn't put back, limits that choose instead of failing, natives
bound by name only, and large files.

## In order

### 1. Crashes and freezes users can hit

- **A `"""` text whose `${…}` the two lexer passes end differently panics
  the lexer**, in release, and the language server lexes on its main thread
  (SW-1916, high).
- **A panic in the language server's checker thread freezes the editor**:
  diagnostics stop, nothing restarts it (SW-1948, high; with SW-1820, a
  panic in the search worker).
- **Stack overflows from deep input** outside the parser's depth check:
  long patterns, comparison chains, `exists` (SW-1874), `omega` and `ring`
  readers on deep sums (SW-1936), nested arrays dropped (SW-1892), the
  runtime's compiler on deep bodies (SW-1895).
- **One lexical error drops the whole file from its project**, and its
  importers fail (SW-1873, D2670/D2690).

### 2. Wrong answers possible in principle

- **Check-cache replay's undo leaves native bindings behind**, so a later
  definition under a reused id could run as a native (SW-1925).
- **A session with a custom prelude keys its cache on the standard
  prelude** (SW-1919).
- **Natives bound by name and arity only**: the kernel's Nat natives
  (SW-1885, D2640), and the effect natives and JS rewrites on every backend
  (D2710, same ticket).
- **Native compilation trusts its image** more than it checks (SW-1893,
  D2711).
- **Dot-call failures replayed across re-checks** of one declaration
  (SW-1902); the address-keyed variant is SW-1803.
- **A code action can replace the wrong text** after an edit earlier on
  the line (SW-1949).
- **JS projections out of arrays** may give `undefined` (SW-1943, low
  confidence).

### 3. Limits that choose, and settings not put back (D2543)

Core's marks and `restore` (SW-1886), glue forced back on and the hand-kept
`NO_ETA` (SW-1901), steps not charged for some walks (SW-1887), text and
`replicate` uncharged (SW-1897, SW-1891), the counterexample search stopping
on the clock (SW-1937, D2700). The bounded readback plan covers the rest
(SW-1830 onwards).

### 4. Checks that never run, and tests that miss

The queue's invariant checks are compiled out of every tier (SW-1903,
D2651); the fuzz test barely reaches the parser (SW-1875); `crates/native`
has no array tests (SW-1891); the cache comparison dump omits most builtin
bindings (SW-1925); a unifier-against-kernel property test (SW-1910).

### 5. Maintainability

Files that grew since 1 November: `check.rs` 7,228 lines, `lib.rs`'s
`impl Elaborator` ~3,750, `effects.rs` 5,231, `module.rs` 3,529,
`parser.rs` 8,876, `js/lib.rs` 6,566. Pure-move splits, one at a time when
no lane touches the file (D2652): SW-1904 to SW-1906, SW-1878, SW-1935,
SW-1947, SW-1890. About 25 places choose a path by an error-code string, the
1 November finding grown (design note SW-1908, D2653). Four copies of
"find, abstract, check, transport" (design note SW-1941).

## Decisions these reviews raise

D2640, D2641 (core); D2650 to D2653 (elab checking); D2660, D2661 (rt);
D2670, D2671, D2690 to D2692 (syntax); D2680 (driver); D2700, D2701
(tactics); D2710, D2711 (js, native); D2720, D2721 (elab rest); D2730 to
D2733 (cli, lsp). Each is on its ticket with a recommendation.
