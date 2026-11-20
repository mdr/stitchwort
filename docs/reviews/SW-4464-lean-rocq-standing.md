# Where we stand against Lean and Rocq (SW-4464)

Sonnet paper lane, 20 Nov 2026, for Matt's question of the same day. It
redoes the count of [SW-4222](SW-4222-lean-rocq-comparison.md) on today's
`main` (f8a466210). Nothing was built or run besides reading and counting.

Marks: **[measured]** counted today by the method in section 1;
**[read]** taken from a file, commit or board ticket named; **[estimated]**
my judgement.

## In plain words

**Where we were.** On 19 Nov the same 21 theorems took 302 lines of proof
in Stitchwort, 159 in Lean and 125 in Rocq: we were about 1.9 times Lean
and 2.4 times Rocq.

**Where we are.** 217 lines **[measured]**: 28% fewer than on 19 Nov, now
about 1.4 times Lean and 1.7 times Rocq. Nearly all of the saving is two
things: the new walk step (the comma-list proof went from 53 lines to 9,
shorter than Lean's 16 and Rocq's 22) and induction along a function (rule N
from 29 lines to 14, level with Lean's 15).

**Kinds we now match or beat Lean on:** list helpers, the comma list, rule N
(and two-run is within 4 lines). **Kinds still behind:** the small parser
walks and plain-tree facts (57 lines against 29 in Lean), the printer (85
against 48, partly because Stitchwort proves 26 document forms where the
port has 8), and the dispatchers (13 against 7).

**What is left.** The one feature the report recommended that nobody has
built is the closer that uses facts in scope and a standard set of lemmas
(like Lean's `grind`): it is in the backlog. I estimate it, with the
remaining walk conversion (W4, running), could take 35 to 45 of the 58
lines between us and Lean **[estimated]**; Rocq's 125 is harder to reach.

## 1. Method

The count is SW-4222's: statement plus proof, as laid out in the file,
from the `theorem` line to the next blank line, leaving out doc comments
(`--|`) and attributes. I checked that this reproduces SW-4222's
Stitchwort numbers by running the same script on `909e34ccc`, the commit
SW-4222 read: it gives 3, 13, 9, 12, 8, 13, 53 (comma list with
`commaEnd`), 2, 7, 8, 18, 29, 60, 7, 11, 13 for the theorems of the
table, exactly SW-4222's figures **[measured]**. The script then ran on
`main`. The Lean and Rocq figures are SW-4222's (the sample files have not
changed) **[read]**.

Where a theorem moved or was deleted, the table says where, and counts it
as 0 in the formatter. I did not run `check`: the proofs are read from
`main`, whose own checks are Overmind's.

## 2. Results

Lines per theorem, Stitchwort on 19 Nov (`909e34ccc`), Stitchwort now
(`main`), Lean, Rocq. All Stitchwort figures **[measured]**.

### Kind 1, dispatchers

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `signSymbolic` | 3 | 3 | 2 | 2 |
| `closerNotComma` (the `Tok` one, `cases`) | 1 | 1 | 2 | 2 |
| `endedWeaker` | 9 | 9 | 3 | 2 |
| **Total** | **13** | **13** | **7** | **6** |

Nothing has changed, and nothing built so far reaches it. `endedWeaker`
is four arms with different shapes, so or-patterns (SW-4236) do not join
them; Lean's `rcases … <;> simp_all` and Rocq's `intuition` do. This is
the gap that a closer using the hypotheses (section 3, 6.3) would close.
(`closerNotComma` has a second, `Text` version in `Fmt/JoinProofs.sw`: 6
lines then, 4 now; it is not the sample's.)

### Kind 2, list helpers

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `allAppendB` | 6 | 0 (deleted; `List.allAppendAnd` in std, `crates/elab/src/std/List/Zip.sw`) | 2 | 2 |
| `itemsParsed` | 10 | 10 | 9 | 8 |
| **Total** | **16** | **10** | **11** | **10** |

SW-4218 (92 generic theorems lifted from `tools/fmt` into std, 11 replaced
by facts std already had) removed `allAppendB` (commit `1601e8f1c`)
**[read]**. This is the "library effect" SW-4222 named: the lemma exists
and the proof names it. `itemsParsed` is plain induction and stays level.

### Kind 3, parser walks (the small ones)

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `givesExpect` | 13 | 13 | 4 | 7 |
| `givesTupleClose` | 9 | 5 | 3 | 2 |
| `parenParsed` | 8 | 12 | 5 | 2 |
| `tupleParsed` | 13 | 13 | 6 | 7 |
| `givesParenClose` | 10 | 6 | 5 | 2 |
| `givesTupleEnd` | 12 | 8 | 6 | 4 |
| **Total** | **65** | **57** | **29** | **24** |

What moved: `givesTupleClose`, `givesParenClose` and `givesTupleEnd` lost
their hand-written `[p := …] [j := …]` arguments, from the walk baseline
and the unspelling sweeps (SW-4245, SW-4256, SW-4259, SW-4353 W0; then
SW-4287 and SW-4324, which made std's lemmas take them implicitly) **[read:
commit log]**. They are still chains of `Parse.givesThen`, not
`byWalking`: what is left is mostly the statement (3 to 5 lines of
hypotheses) and one or two lines of proof. `parenParsed` went *up* by four
lines, from the formatter laying out a record (`InSlice`, SW-4214's
`a73a074fe`), not from any change to the proof. `givesExpect` is a leaf
that uses the lexer's guarantee and has not changed; W4 registers some of
its neighbours with `@[walk]` (section 5). The remaining gap here is
the proofs about the tree (`parenParsed`, `tupleParsed`: 25 lines against
11 in Lean): a closer, not a walk.

### Kind 4, the longer walk (comma list, fuel loop)

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `givesCommaListFrom` | 46 | 9 | 16 (with the lemma its proof uses) | 22 (same) |
| `commaEnd` | 7 | 0 (std's `List.allConsReverse`, 6 lines, `List/Zip.sw`) | | |
| **Total** | **53** | **9** | **16** | **22** |

The biggest change in the study. The proof is now one line,
`byWalking [reads0Peek modes, givesBump] then List.allConsReverse …`,
under an 8-line statement. Three things did it: the walk step W1 (SW-4239:
the pilot took the proof from 20 lines to 1) **[read: its commit
`74088b969`]**; SW-4353 (W0), which merged the four comma-list functions
(`commaListFrom`, `commaListOn`, `commaListComma`, `commaListAfter`) back
into one with its `match` and `if`s inline, which the walk can now step
through; and SW-4218, which lifted `commaEnd` into std as
`List.allConsReverse`. Counting `List.allConsReverse` (6 lines) in
std, the total is 15, level with Lean's 16, and shorter than Rocq's.

### Kind 5, two runs (`Parse.Follows`)

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `followsPeek` | 2 | 2 | 11 | 5 |
| `followsBump` | 7 | 7 | 11 | 5 |
| `followsExpect` + `followsExpectOn` | 8 | 6 | 8 | 6 |
| `followsParenClose` + `alikeParen` | 18 | 14 | 3 | 6 |
| **Total** | **35** | **29** | **33** | **22** |

`followsExpectOn` is now `byWalking [followsFail]` (3 lines, was 5) and
`followsParenClose` is `byWalking [] then alikeParen …` (5 lines, was 9):
the two-run walk, W3 (SW-4240; the pilot in `FollowsBase.sw` is commit
`17038385a`) and the Follows twin of the walk for the formatter's syntax
(SW-4427). `followsExpect` still applies `followsThenEq` by hand (3 lines)
and `followsBump` is by hand: it is a primitive (`followsNext`) plus a
match on the result, which the walk does not take as the lemmas stand.
`alikeParen`'s 9-line `calc` is the relation's constructor fact.
We are now under Lean's total and 7 over Rocq's.

### Kind 6, rule N

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `allTokensWithout` | 29 | 14 | 15 | 12 |

Functional induction: `match induct (withoutR behind rest) with`, three
cases, no "nop" lemmas, no re-done split (SW-4264, the formatter pilot of
SW-4260 to SW-4263; the guard arrives as `c = True` hypotheses after
SW-4341, D3699) **[read: commit `ab74e9f92`]**. This is the number SW-4222
predicted (15 and 12) and we reach it.

### Kind 7, printer

| Theorem | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| `joinsWeaker` + `writeWeaker` + `sepWeaker` (26 forms in Stitchwort, 8 in the ports) | 60 | 54 | 30 | 17 |
| `passesCons` | 7 | 7 | 4 | 3 |
| `joinsAllAppend` | 11 | 11 | 8 | 6 |
| `passesAppend` | 13 | 13 | 6 | 3 |
| **Total** | **91** | **85** | **48** | **29** |

The 6 lines saved in `joinsWeaker` and `softWeaker` are or-patterns
joining arms with the same body (`Doc.Nothing | BreakParent | Blank`):
SW-4251, using SW-4236 (std's `Doc/Joins.sw`, commit `cc14a319d`)
**[read]**. The printer lemmas' arguments were made implicit
(SW-4230, SW-4275, SW-4282, SW-4283), which shortened their *uses*, not
these statements, so the sample's lines do not move; the explicit
`(Follows kinds) front back edge next` in `passesAppend`'s proof is
still there. This kind is not fair by lines (SW-4222's own note): per
form, 54 lines for 26 forms is 2.1 against Lean's 30 for 8, 3.8.

### Totals

| | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| 1 Dispatchers | 13 | 13 | 7 | 6 |
| 2 List helpers | 16 | 10 | 11 | 10 |
| 3 Parser walks | 65 | 57 | 29 | 24 |
| 4 Comma list | 53 | 9 | 16 | 22 |
| 5 Two runs | 35 | 29 | 33 | 22 |
| 6 Rule N | 29 | 14 | 15 | 12 |
| 7 Printer | 91 | 85 | 48 | 29 |
| **All 21** | **302** | **217** | **159** | **125** |
| Against Lean / Rocq | 1.90 / 2.42 | 1.36 / 1.74 | 1 | 1 |

All **[measured]** (Lean and Rocq as SW-4222). Without the printer's
`joinsWeaker` group (not comparable): 163 against 129 and 108, about 1.26
and 1.51.

Other figures from SW-4222 §3.6 **[measured]**:

| | 19 Nov | Now | Lean | Rocq |
|---|---|---|---|---|
| Parser functions for the sample | 10 | 7 (comma list 4 to 1; `expect`/`expectOn` and `tupleClose`/`tupleCloseAfter` still split) | 5 | 5 |
| Theorems for the same content (the sample's 30) | 30 | 28 (`allAppendB`, `commaEnd` now std's) | 23 | 26 |

Check time and writing time were not re-measured; the walk's own
timing against hand proofs is SW-4421's 1.5x bar.

## 3. SW-4222 §6, one by one

| Recommendation | State | Tickets (board status) |
|---|---|---|
| 6.1 a walk step | **Built, part (a) and most of (b)**; conversion of the rest is running | design SW-4231 and review SW-4238 (done); W0 baseline SW-4245, SW-4353 (done); W1 SW-4239 (done); W2 review SW-4354 (done); W3 two-run SW-4240 (done); formatter syntax SW-4427 (done); W4 SW-4421 (**doing**) |
| 6.2 induction along a function | **Built** | SW-4260 (B1, guide), SW-4261 (G1 guarded arms), SW-4262 (G2 non-tail match), SW-4263 (or-patterns, dot form, `?` hole), SW-4264 (formatter pilot): all done; SW-4341 (D3699 Bool guards) done; follow-ups SW-4280 (backlog) |
| 6.3a default lemma sets for `rewrite repeatedly` | **Not built** | SW-4241 (backlog), on SW-3631 (backlog) |
| 6.3b a closer chaining hypotheses (`grind`-like) | **Not built**, not designed | SW-4242 (backlog, a Fable paper lane to measure what it would close) |
| "remaining cases likewise", SW-4219 | **Partly built** | note done (`docs/proposals/proof-match-likewise.md`); or-patterns that bind built as SW-4236 (D3694, done); sweeps SW-4251, 4252, 4253 (done) |
| SW-4220, hand-given arguments | **Built, by other means** | SW-4220 itself found that no std change helps and sent two causes on: SW-4305 (unifier, done), SW-4324 (`followsMap` order, done); W0 and the unspell sweeps SW-4245, 4256, 4259, 4287 (done); SW-4325 (a pure-value step, backlog) |
| SW-4047, a guard a `match` arm does not refine | **Built** | SW-4047 (done), and SW-4341 gives the guard as `c = True` / `c = False` |
| A library that already has the lemma | **Built for this sample** | SW-4218 (92 lifted, done); the consolidation lanes SW-4281 to 4292, SW-4308 (done) |
| Implicit arguments in printer statements | **Built** | SW-4230, SW-4275, SW-4282, SW-4283 (done) |

Notes on the less obvious rows:

- **6.1.** The walk follows an `if` and `match` inside a body (the "path
  cap" of SW-4239), which is part (b); the comma list shows it working
  (four functions merged, 53 lines to 9). But `expect`/`expectOn` and
  `tupleClose`/`tupleCloseAfter` are still two functions each, so (b) is
  used where the parser was merged and not yet where it is split.
  The walk is not yet the form of most proofs of the sample: three of
  the 21 sample theorems use `byWalking` (`givesCommaListFrom`,
  `followsExpectOn`, `followsParenClose`) **[measured]**.
- **SW-4219.** It was a design note whose recommendation was or-patterns
  that bind and *no new splitting keyword*: 72% of repeated arms in
  `tools/fmt` bind nothing the body uses and a catch-all is already
  checked per case **[read: the note]**. So what is built is or-patterns,
  which join arms with the **same body** (the printer's 6 lines, 33 arms to
  6 in `spellsNotComment`). What is **not** built is Lean's `<;>` /
  `all_goals`: one text applied to arms that differ in shape
  (`endedWeaker`, kind 1). The self-hosted formatter does not yet accept
  or-patterns (SW-4258, backlog), so the formatter's own source can use
  them only because the Rust formatter handles it.
- **SW-4220.** It closed as a finding, not a feature; the effect on the
  sample is in kind 3 and kind 5.
- **`<;>`, `all_goals`:** no ticket asks for them. SW-4222 counts 8 uses
  of `<;>` or `all_goals` in 21 proofs. SW-4242's measurement would cover
  the case if it includes them.
- **Finite kinds** (SW-4221): ahead already, nothing to do.

## 4. The remaining gap

217 against 159 (Lean) and 125 (Rocq). **[estimated]** closing, from the
sample, by feature; these overlap and are ranges.

| Gap against Lean | Lines now / Lean | Closes it | Could remove [estimated] |
|---|---|---|---|
| Parser walks, kind 3 | 57 / 29 (+28) | a closer for the tree facts (`parenParsed`, `tupleParsed`, 25 lines against 11, and `givesExpect`'s 13 against 4): 6.3a and 6.3b. The other three (19 lines, mostly statements) by W4 converting to `byWalking` | 12 to 18 from the closer; 2 to 4 from W4 |
| Printer, kind 7 | 85 / 48 (+37) | not by lines: 54 of these lines are 26 forms against 8. For the other 31 lines (+18): explicit `(Follows kinds) front back edge next` arguments at uses and the statements' hypotheses; a closer | 4 to 8; the 54-line part not comparable |
| Dispatchers, kind 1 | 13 / 7 (+6) | `endedWeaker` and `signSymbolic`: `<;>`/all-goals or a closer that uses the hypotheses | 4 to 6 |
| Two runs, kind 5 | 29 / 33 (-4), 22 for Rocq (+7) | W4 does not touch these; `followsBump` and `followsExpect` by walk | 2 to 4 |
| Others | level or ahead | | 0 |

So about 25 to 40 of the 58 lines against Lean, taking the printer's
non-comparable 54 lines off the denominator: **mostly the closer (6.3)**,
then the leaf walks (W4). That leaves us at about 180 to 190, **1.1 to 1.2
times Lean**. Rocq's 125 includes one-liners for the leaf facts
(`auto`, `intuition`, `lia`) that I would not expect Stitchwort to reach:
**1.4 to 1.5 times Rocq** after the closer **[estimated]**. The estimate
rests on 21 theorems, as SW-4222's did; the closer's effect is the one
I am least sure of, since it is not designed (SW-4242 is the paper lane
that would measure it).

What lines do not say: Lean's walk tool is still being renamed
(SW-4222 §4); our walk's proofs are checked by the kernel as chains of
named lemmas. Check time and the usability of error messages are not
in these numbers.

## 5. What W4 (SW-4421, running) will change

Read from `git diff main...lane/SW-4421` at the time of writing
**[read]**: so far it converts proofs in `FollowsStatements.sw`,
`ParseWalkOutside.sw` and `ParseWalkOthers.sw` (66 lines added, 217
deleted), none of them a sample theorem, and adds `@[walk]` to
`givesBump`, `givesLeft`, `givesAt`, `givesPeek`, `givesFail`,
`givesFatal` (new) and `givesFailName` in `ParseProofs.sw`/`ParseWalk.sw`.
No sample theorem's text changes yet.

What may change when it is merged, so that the numbers can be redone:

- `givesCommaListFrom` (9 lines): `givesBump` and `reads0Peek` are the
  list it passes; with `givesBump` registered, the list may shrink.
  `givesBump` is itself one of the walk's leaf lemmas outside the sample's
  21.
- `givesTupleClose`, `givesParenClose`, `givesTupleEnd`, `givesExpect`
  (kind 3) and `followsExpect`, `followsBump`, `followsPeek` (kind 5): these
  live in `ParseWalk.sw` and `FollowsBase.sw`, which W4's "ParseWalk\*,
  Follows\*" scope names and which the branch has not reached yet.
- Unaffected: kinds 1, 2, 6, 7.

To redo after it merges: run the script in section 1 (the awk in this
lane's scratchpad, `sw4464/all.sh`, takes a revision) on the new `main`,
for the 10 theorems above, and update kinds 3, 4 and 5 and the totals;
also `grep -c byWalking` for the count of sample theorems that use the walk.

## 6. Findings

- The sample's printer line counts are not comparable and so are 85 of 217
  lines of the total. A future recount might drop `joinsWeaker` and give
  per-form figures.
- `parenParsed` grew by 4 lines from a layout change (`InSlice`); a
  line-count metric will always wobble this way. Not a ticket.
- The self-hosted formatter does not accept or-patterns yet (SW-4258,
  backlog), although `tools/fmt`'s own proofs now use them (SW-4252).
  The brief's "formatters behave the same" rule makes this a known
  state, not a new finding.
