# The toy formatter: final report (SW-3414)

Opus paper lane, 15 November 2026, after stage D. Sources: the toy's plan
([toy-formatter.md](../proposals/toy-formatter.md)), the real plan
([self-hosted-fmt.md](../proposals/self-hosted-fmt.md)),
`tools/toyfmt/NOTES.md`, the performance log (SW-3383, SW-3391), the board's
tickets and the work log. No new measurements: every timing below is one
the lanes took on Speedwell, marked **[measured]**; projections are
**[estimated]**.

## In plain words

**What it showed.** Every part the real Stitchwort formatter needs exists
and works together in one real program: files, fast text, text patterns,
the token parser, a layout engine, the proofs, and a built executable with
exit codes. The two theorems the real plan promises took 15 minutes, not
the 1-2 days it allowed. The whole toy took about 2 lane hours against an
estimate of 13-17.

**What it costs to run.** Natively, the toy formats about 2.2 s per MB, and
4.3 s per MB with its safety check (it parses its own output again). Scaled
to the real formatter's 6.5 MB, that is about 15 s without the check and
28 s with it, against a 20 s target [estimated]. Almost all the time is the
parser library's cost per step, not the printer.

**What it says.** The real formatter is ready to start (D3576, stages 0-2):
nothing it needs is missing. Its parser should stay hand-written, as
self-hosted-fmt.md §3.2 says: the library parser was pleasant but about
7-10 times slower. And the safety check should stay on always, with one
cheap change: skip the re-parse when the output is the same text as the
input. That keeps the theorems and makes the check free on files already
formatted, which is nearly all of them. That is D3617.

## 1. What was built, and what it proved

`tools/toyfmt`: about 3,100 lines of Stitchwort formatting *Sprig*, a
made-up language with Stitchwort's hard shapes (precedence, blocks by
indentation, comments, long lines, unsplittable strings).

| Stage | Ticket | What it built |
|---|---|---|
| A | SW-3340 | Lexer on `Parse Char` with `Text.slice`; keyword and operator tables as text patterns (`nameIsNoKeyword` proved by `cases`); a `Parse.tokens` parser with blocks by indentation (the layout rule is a parameter of the token reader, about ten lines); exact-message tests |
| B | SW-3341 | `Toy.Doc`, the Rust engine's core ported almost line for line (its tests passed first time); rules P1-P10; 12 goldens; a disturber (50 seeds per golden, 600 texts, all format back) |
| C | SW-3342 | The `{Files}` loop (writes only what changes), the command line (now on `Std.Args`), `main`, 13 tests under `Files.simulate`, an end-to-end test on a real folder under `run`, the built and the native executable |
| D | SW-3343 | `lex` checks that its lexemes cover the source; `format` re-parses its output and answers `Stable` only if the tree comes back. Then the proofs below |

**Theorems** (all proved with no extra hypotheses; the audit is clean;
breaking either check makes its proof fail):

- `lexCovers`: the lexemes' slices joined are the source.
- `formatRoundTrip`: a `Stable` output parses to the source's tree.
- `formatIdempotent`: formatting a `Stable` output gives it back.
- The folder theorems, under `Files.simulate`: `formatFileUnchanged`,
  `WouldChange`, `Rewrites`, `RefusedWrite`, `Refused` (a file is written
  only when its formatted text differs, never under `--check` or on a parse
  error), `readAfterWrite`, and `formatFileSettles` (after one run, the
  next writes nothing).

**Exit codes** (after SW-3402/SW-3403, D3616): 0 clean, 1 `--check` found a
file to change, 2 a bad command line or a path it couldn't read or parse,
as `stitchwort fmt` does. The end-to-end test checks all seven cases under
`run` and built.

**Left out, as planned:** byte-for-byte agreement, 94 kinds, the rewrites,
check time on 10,000 lines (the toy's own check time wasn't recorded).

## 2. Cost

From the tickets' model-result lines (minutes of lane time; git timestamps
agree):

| Work | Ticket | Model | Estimate | Actual |
|---|---|---|---|---|
| Plan | SW-3339 | Opus | 90 | 10 |
| Stage A | SW-3340 | Opus | 210 | 19 |
| Stage B | SW-3341 | Opus | 270 | 25 |
| Stage C | SW-3342 | Sonnet | 150 | 30 |
| Stage D | SW-3343 | Sonnet | 210 | ~30 (proofs: 15) |
| **The toy** | | | **930 (15.5 h)** | **~115 (1.9 h)** |
| Profiling | SW-3383 | Opus | 120 | 30 |
| This report | SW-3414 | Opus | 60 | ~40 |

**Fixes the toy's friction caused** (std and language; some, like Args,
were wanted anyway): SW-3371 derived `==` for mutual types (Opus, 40),
SW-3367+3391 std Parse (Sonnet, 45 of 180), SW-3377 Files and Text (Sonnet,
15 of 150), SW-3390 `test FILE` (DeepSeek, 20 of 45), SW-3381 Std.Args
(Sonnet, 75 of 210), SW-3345 exit-status design (Opus, 23), SW-3402/3403
exit status (Sonnet, 20 and 40), SW-3397 constructor clashes (Sonnet, 60),
SW-3411 (Sonnet, 15): about 6 h. Design papers SW-510, SW-3354, SW-3359
not counted.

**Total:** about 3 h for the toy, its profiling and this report, plus about
6 h of follow-up fixes, against 13-17 h planned for the toy alone. Wall
clock 08:09 (D3587) to 14:19 (last fix merged), mostly waiting for fast
text, Files and derived `==`.

The estimates were about 8 times too high. The real plan's 42-59 h was made
the same way, but its hard part, matching the Rust formatter byte for byte,
is what the toy left out, so I would not scale it down by the same factor;
half (20-30 h) is a fair guess [estimated].

## 3. Speed

Native, seconds per MB of Sprig, input generation subtracted [measured,
one machine, medians of 3 except stage A]:

| When | Lex | Parse (beyond lex) | Print | Format | With the check |
|---|---|---|---|---|---|
| Stage A, combinators as first written (load 8-12) | 1.3 | 2.4 | 0.5 | 4.2 | - |
| SW-3383, profiled: precedence climbing, a lexer loop (load 3.5) | 0.73 | 0.98 | 0.34 | 2.05 | - |
| SW-3391, those moved into std (`Parse.operators`, `locatedToEnd`) | 0.73 | 1.07 | 0.35 | 2.15 | - |
| Stage D, before and after the check (load 50) | 0.77 | 1.08 | 0.33 | 2.24 | **4.28** |

`stitchwort run` (not native): 9.7 s/MB at stage A; SW-3383 took its 933 KB run from 9.4 s to 5.2 s.

- **Where the time is.** Not in any function. Three quarters of it was the
  effect runtime and the allocator, about 4,300 instructions per `Parse`
  operation (SW-3383's profile). Printing is a seventh of the format.
- **The check costs one more lex and parse of the output:** +2.0 s/MB,
  +91% of the format (the "+80%" quoted elsewhere is of the timed run,
  which includes 0.3 s of making the input). The lexemes' coverage check is
  5% of lexing, cheap enough to keep always.
- **Projection for the real formatter's 6.5 MB** [estimated, by scaling the
  toy's rate per byte]: about 15 s without the check, 28 s with it, against
  the 20 s target and 30 s ceiling. A bigger grammar costs more per byte,
  so a combinator twin would land at or over the ceiling. The hand-written
  probes in self-hosted-fmt.md §5 lex at 0.11 s/MB and parse a small
  grammar at 0.06-0.13 s/MB more [measured, on toy grammars], about 7-10
  times faster than `Parse` here. The plan's 1.8-3.9 s/MB (12-25 s) assumes
  those.
- **What would close the gap for `Parse`:** operations in place (paused,
  D3430/D3465) for the cost per operation, and D3597's slices (later) for
  the tenth spent on the list of characters. Neither is scheduled.

## 4. Friction

"At scale" marks what matters for the real formatter (94 kinds, a
234-function parser).

| Friction | Ticket | Status | At scale |
|---|---|---|---|
| No `==` on a mutually recursive tree | SW-3371 (SW-3358 duplicate) | fixed; 94 constructors derive in 0.17 s (SW-3370) | yes: the check and the tree-dump gate need it |
| Recursion through `List.map` on a field needs a helper per list | SW-3359 | deferred by Matt (D3611); helpers stay | yes: every traversal of children. The plan already assumes helper pairs, so friction, not a blocker |
| Mutually recursive parsers need fuel by hand | none | accepted | the plan's design (fuel for the parser) |
| Constructors of two types clash where the type is known | SW-510, SW-3397, SW-3411 | fixed as D3615: better errors, `W-CTOR-HIDES`, one meaning per file | yes: keep lexer and printer types in separate files |
| `cases` derives `x = y` but doesn't use it | SW-3344 | open | stage 7 only; worked round by a projection |
| Constructor injectivity by a hand-written projection | SW-3409 | open | stage 7 only |
| A program exits only 0 or 1 | SW-3345, SW-3402, SW-3403 | fixed (D3616) | yes, done |
| `Parse.recursive` takes no argument; `Parse.tokens` has nowhere for trailing comments; the token just read is out of sight | SW-3367 | fixed (`recursiveWith`, `tokensWith`, `lastRead`; no `previous()`) | for Parse users; not for a hand-written twin |
| Precedence by `chainLeft` towers; a handler per lexeme | SW-3391 (SW-3392 stale) | fixed (`Parse.operators`, 7% slower than hand-written; `locatedToEnd`) | classifier variant SW-3400 open |
| Cost per `Parse` operation; reading a list of characters | SW-3393; D3430, D3597 | parked (speed paused, D3465); slices later | decides §3.2 (below) |
| Layout-rejected token reads as a wrong token | SW-3368 | open | Parse users only |
| A check between lexer and parser needs `tokensWith` taken apart | SW-3409 | open | small |
| `import N (..)` doesn't reach a helper-only namespace | SW-3400 (hint) | not a bug; hint open | small |
| Handler over `Files` by hand; `Files.simulate` can't see writes | SW-3377 | fixed (`Files.tracing`, `Disk` records writes) | yes: the harness |
| `test FILE` outside the project; two `main`s; `Text.splitOnce` | SW-3390, SW-3377 | fixed (two mains refused with both named) | small |
| No `Files.walk` | none (F3) | open; the toy's `walkLevels` is the start | stage 0's batch driver |
| No clock | SW-3361 | open (paper) | stage 6's per-phase timings |
| Name shared by a constructor and a field's type; no `List.intersperse`; tuple accumulator needs a type; fmt moves a record with text blocks below `:=` | SW-3360 | open | small |
| `Int.ofNat` note misses `Nat.toInt` | SW-3346 | open | small |
| `Doc.group` recomputes `forcesBreak` (quadratic in nesting) | SW-3416 | not an issue: `Group` caches the flag, construction measured linear (200 to 6,400 levels) | no |
| Text patterns lack "any one character" | SW-3385 | open | lexer only |

## 5. What it says

### D3576: is the real formatter ready to start?

**Yes.** Every gap self-hosted-fmt.md §5 listed is closed: SW-3149 (native
executables start), Files (F1), fast text (T1), text patterns (keywords as
a `match`, not a `Map`), a token parser, derived `==` over 94 constructors.
The toy also retired two risks the plan carried: theorems 1 and 2 by
validation are minutes once `format` checks and the rules read only the
tree, and a layout-sensitive grammar is ordinary code.

**Nothing must land first.** Before stage 0, self-hosted-fmt.md wants a
short refresh (its option C still says `Std.Parse` reads characters only;
SW-3149 and SW-3150 are shown open; the theorem estimates), and the
validation decision (D3617) folded into §3.4 and §7. `Files.walk` (F3)
helps stage 0's driver but the toy's walk will do. The clock (SW-3361)
matters by stage 6, not 0-2. D3577 and D3578 remain open beside D3576.

### §3.2: a hand-written parser, or generic Parse?

**Keep B, hand-written.** The toy is the best case for `Parse`: messages
for free, layout as a parameter, every gap closed in std within hours. But
the twin needs none of what `Parse` gives: it refuses rather than reports
(no messages, no recovery), it must follow the Rust parser function for
function to pass the tree-dump gate, and it looks ahead by index (bracket
partners). What `Parse` costs is 7-10 times the hand-written probes'
speed, and the safety check pays that cost twice. Revisit if operations in
place land; until then `Parse` is the right tool for AoC, configs and
tools where messages matter, and the twin tests plain Stitchwort (arrays,
index loops, fuel).

### Validation: what to do about its cost

| Option | Theorems | Cost on the repo [estimated] | Risk |
|---|---|---|---|
| 1. Always validate, as now | unconditional | +2 s/MB with `Parse` (+13 s); +0.3-1.1 s/MB hand-written (+2-7 s) | none |
| **2. Always, but skip the re-parse when the output is the input's text** | unchanged: if `printed.text = source`, then `parse printed.text = parse source = Ok tree`, one more case in `formatChecked` | about 0 on formatted files (the repo, `--check` in CI, format-on-save); full on files that change | none |
| 3. Validate only under `--check` or tests | about a function nobody runs when writing | saves the cost when writing | wrong way round: `--check` writes nothing, and writing is where a printer bug destroys code |
| 4. Prove the printer, drop the check | `parse (print tree) = tree` from the rules | none at run time | months for the real rules, broken by every style change (plan §7) |
| 5. Validate a sample | none | a fraction | a bug outside the sample silently changes code |

**Recommend 2**, and in the real formatter apply it per declaration (the
twin parses declarations independently, so only declarations whose text
changed are re-parsed). The Rust formatter also checks every run; 2 keeps
that safety and the theorems, and moves the cost onto exactly the files
being rewritten. In the toy it is one line in `format` and a few in
`formatChecked` (Sonnet, about 30 min [estimated]).

## Question for Matt

**D3617: keep the formatter's safety check always on, skipping it only for
files it leaves unchanged?**
*The problem:* the toy's guarantees (formatted output means the same
program; formatting twice changes nothing) come from re-reading its own
output, which nearly doubles its run time: 2.2 to 4.3 s per MB [measured],
about 15 to 28 s for the repo at the real formatter's scale [estimated].
*The change:* when the formatted text is identical to the file as it was,
skip the re-read: it would read the same tree by definition, so the
guarantees still hold, unconditionally. Files that change are still
checked in full; in the real formatter, only the declarations that changed.
*What it should do:* checking an already formatted repo costs about
nothing, so the check never needs a switch to turn it off, and the proofs
stay about the program people run. **[rec: yes]**
