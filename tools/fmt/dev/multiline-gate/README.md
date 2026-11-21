# The multi-line read-back gate

A rerunnable check for the multi-line read-back (`readsBackHung`,
`tools/fmt/src/Syntax/ReadBackHungTop.sw`), from SW-4121's note
(`docs/reviews/SW-4121-multiline-readback.md`, section 4). It generates
slice 1 declarations laid out over lines in ways the printer never would,
and runs two checks on each:

- **Check B, the statement without the printer.** Lex the file, apply
  comment placement as the driver does, split into groups. If every group keeps
  `Fmt.hangs`, the layout must parse to the same tree as its tokens
  written on one line (compared by `meaning`'s dump). A failure is a
  counterexample to `readsBackHung`.
- **Check A, the printer's side.** The driver's steps; the gate only labels a
  file `one` or `multi` by where its tokens start lines (`gateOnLine`; the driver no longer tests it). For each accepted file, seven tests of the tidied tree: the tree
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
of 250 files and the 74 hand cases; about 12 minutes of `stitchwort run`
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
- `hand.py OUT.cases`: the 74 hand-written sources (D3686's comment
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

Hand cases (74, eight of them blank lines above comments since D3693):
check A accepts all 74, 65 printing over several lines, all seven tests
passing; check B finds 72 that keep `hangs` and parse to the same tree,
and two that break `hangs` (a comment right after `->`) and parse to the
same tree anyway.

## The element facts' check (SW-4130)

`ElementsGate.sw` checks what `declElements1` (`Fmt.ElementsProofs`) gives through `printedHangs1`: for each
declaration of a source's tidied tree, its tree facts, `settled1` and `homed1` (`homedOfSettled`), whether its
comments are only at the edges (`edgeQuiet1`) and on one line, and whether the printed text keeps `hangs` at
eight widths from 6 to 120. Copy it into `tools/fmt/src`, run `stitchwort run ElementsGate.main < FILE.cases`
from `tools/fmt`, and delete it. On 19 Nov 2026 (the hand cases, and `gen.py` seeds 77 to 80 in modes `noted`,
`longnoted`, `legal` and `wild`): 2,455 declarations with the tree facts, 1,938 of them with comments inside the
type or value, all over several lines; `hangs` held at every width and `homed1` of every one.

SW-4145 added `anyKeys`' check to each line (`keysFailed`, `keysTight`): at every node of the type and the value,
standing where `Expr.el` puts it with every comment written and one waiting before it, the node's document keys its
marks and closer lines at or after its own position. On 19 Nov 2026 (the hand cases and `gen.py` seeds 77 to 80 in
modes `noted`, `longnoted`, `legal` and `wild`, one chunk of 250 each): 855 declarations with the tree facts, 631 with
comments inside; no node failed, and 147 nodes in 72 declarations have a key at exactly their position, so the floor
can't be raised.

## Kept blank lines before items (SW-4153)

An item with no comments but a kept blank line before it leads with `[BreakParent, LineStart, Blank]`. Two checks:

- `BlankGate.sw`: prints each declaration with the tree facts at the eight widths, with and without the `LineStart` of
  every such item, and compares the texts; the same text means every such item was entered right after a line
  break. Inputs: `gen.py` seeds 77 to 80 in modes `noted`, `longnoted`, `legal` and `wild` (250 each) and the hand
  cases, each passed through `blankify.py IN OUT SEED` (the mode's seed; 1 for the hand cases). On 19 Nov 2026:
  858 declarations with the tree facts, 157 of them with 939 such items in all; the text was the same in every one.
- `BlankMid.sw` with `blank-mid.cases`: what `Lays` also allows, the separator before such an item laid as a space,
  printed by hand: the `LineStart` then breaks to two right of the line, and an undisplaced tuple, list or chain
  item keeps its later lines at the indentation, so `hangs` fails at width 8; displaced, every case keeps `hangs`.
  Since SW-4155 the rules displace such an item (`Word.displaces`), as they do one with comments above it.

Run either as `ElementsGate.sw` is run (copy into `tools/fmt/src`, `stitchwort run BlankGate.main < FILE.cases`
from `tools/fmt`, delete).

## Comments above a chain's operator or right operand (SW-4149)

`ChainGate.sw` counts, at each chain node of each declaration with the tree facts, operators with own-line comments
above them (`opNoted`), operators with a comment after them, and right operands with comments above their first
token (`rightNoted`); and for each such operator and operand, whether its element keeps `hangs` laid after `A -> `,
which glues the fold (`opGluedFails`, `gluedFails`). `LinkFacts` before SW-4149 asked `HangsAt`, so from every seat,
the glued one among them, of every operator and of every right operand that is no chain of its level; a failure here
is a parse for which that was false. Run it as `ElementsGate.sw` is run. On 19 Nov 2026 (the hand cases, the SW-4149
cases and `gen.py` seeds 77 to 80 in modes `noted`, `longnoted`, `legal` and `wild`, 250 each): 866 declarations
with the tree facts and 5,240 chain nodes; 186 operators in 140 declarations and 147 right operands in 116 have
comments above them, and every one of them fails `hangs` after `->`. `Links` and `RunFacts` now ask for those that
they start the line after their comments (`startFor`).

## CmpGate: printed output unchanged

`CmpGate.sw` prints every declaration's slice 1 and slice 5a documents at eight widths. To show a rules change leaves printed text byte-identical, run it on copies of `tools/fmt` before and after the change (copy it into `src`, `stitchwort run CmpGate.main < cases`) and `diff` the outputs. The first run is cold (2-3 min). In tools/fmt/src, Syntax/LexProofs, LexReadsProofs, ParseCarriesDecl and ParseWalk take over 90 s each; skip them. Used by SW-4155.
