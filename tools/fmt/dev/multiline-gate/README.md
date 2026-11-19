# The multi-line read-back gate

A rerunnable check for the multi-line read-back (`readsBackHung`,
`tools/fmt/src/Syntax/ReadBackHungTop.sw`), from SW-4121's note
(`docs/reviews/SW-4121-multiline-readback.md`, section 4). It generates
slice 1 declarations laid out over lines in ways the printer never would,
and runs two checks on each:

- **Check B, the statement without the printer.** Lex the file, apply
  rule N as the driver does, split into groups. If every group keeps
  `Fmt.hangs`, the layout must parse to the same tree as its tokens
  written on one line (compared by `meaning`'s dump). A failure is a
  counterexample to `readsBackHung`.
- **Check A, the printer's side.** The driver's steps without its one-line
  test. For each accepted file, seven tests of the tidied tree: the tree
  facts, `hung1`, `stood1`, the printed text lexes to `lexed1`, every
  printed group keeps `hangs`, the output reads back to `calmTop`, and
  formatting the output gives it back.

## Running it

From the repo root, with the release binary built:

```
STITCHWORT=$PWD/target/release/stitchwort \
  nix shell nixpkgs#python3 -c tools/fmt/dev/multiline-gate/run.sh 1 /tmp/gate
```

The first argument scales the run: `1` is SW-4121's full run (88 chunks
of 250 files and the 66 hand cases; about 12 minutes of `stitchwort run`
at 4 s a chunk and check, plus a recheck of `tools/fmt` for the copied
module); `0` runs one chunk of each mode and the hand cases, for a quick
look (about 3.5 minutes, most of it the recheck). The second is the work folder for the generated cases and the
results (a fresh temporary folder if left out). Nothing generated is kept
in the repo.

`run.sh` copies `MultilineGate.sw` into `tools/fmt/src` for the run (it
needs the project's namespaces) and deletes it on exit, so don't run a
check or a lane's tests in the same checkout at the same time. It exits
with status 1 if any file fails either check, and prints the counts.

The files:

- `gen.py SEED COUNT MODE OUT.cases`: the generator, with a port of
  `HangState` to choose columns. Modes: `wild` (a share of line starts at
  any column), `legal` (columns the port allows), `long` (long names, so
  the printer breaks for width), `noted` (comments on most breaks),
  `longnoted`.
- `hand.py OUT.cases`: the 66 hand-written sources (D3686's comment
  between a sign and its operand among them).
- `MultilineGate.sw`: `checkA`, `checkB` and their `main`s.
- `tally.py WORK_DIR`: the counts below, from the results.

## Expected counts

At scale 1, as SW-4121 measured them (19 Nov 2026). A different count
with no `FAIL` row means the generator, lexer, parser or printer changed;
a `FAIL` row is a counterexample to read.

Check B, generated files (22,000):

| Outcome | Files |
|---|---|
| one-line form is no slice 1 program | 5,793 |
| hangs, several lines, same tree | 9,096 |
| hangs, one line, same tree | 2,179 |
| **FAIL: hangs, and a different tree or no parse** | **0** |
| breaks hangs, same tree anyway | 2,757 |
| breaks hangs, doesn't parse | 2,119 |
| breaks hangs, parses to another tree | 56 |

Check A, generated files (22,000):

| Outcome | Files |
|---|---|
| not accepted: doesn't parse | 7,912 |
| not accepted: parses outside within1 | 56 |
| accepted, multi lines, all seven tests pass | 11,200 |
| accepted, one line, all seven tests pass | 2,832 |
| **FAIL: accepted, and a test fails** | **0** |

Hand cases (66): check A accepts all 66, 58 printing over several lines,
all seven tests passing; check B finds 64 that keep `hangs` and parse to
the same tree, and two that break `hangs` (a comment right after `->`)
and parse to the same tree anyway.
