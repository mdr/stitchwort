# Slice 1 against Lean 4 and Rocq: a stratified sample (SW-4537, stage 1)

**Status:** Fable lane, 21 November 2026, against `main` at `110e3e3fc`.
Stage 1 of two: the method, the sample, the porting rules, a pilot of
three theorems, and the batches for three port lanes. No Stitchwort code
changed; nothing in Stitchwort was built or checked. The pilot's Lean and
Rocq files were compiled.

Marks: **[measured]** counted or compiled today; **[read]** taken from the
file named; **[estimated]** my judgement.

## In plain words

**The problem.** The earlier comparisons (SW-4222, SW-4464) ported 21
theorems chosen by hand, all from the parser and a little of the printer.
Nothing compared the 37,000 lines about pure functions, and a hand-picked
sample gives no error bar.

**The change.** Slice 1's 5,422 theorems are split into eight parts by
what they prove. A script draws 30 of them at random (seed 4537), more
from the bigger parts, each theorem's chance in proportion to its length.
Each is ported to Lean 4 and Rocq under written rules and compiled. The
ratios are then scaled up by each part's size, with a bootstrap interval.

**What it should do.** Give one figure, "slice 1's theorems in Lean take
about x times our lines, 90% between y and z", and the same per part, so
the shortening work can aim at the parts that are furthest behind. With
30 theorems I expect the whole-slice interval to be about ±0.15 to ±0.25
wide **[estimated]**; per part it will be rough (2 to 11 theorems each).

**The pilot.** Three drawn theorems, 34 lines in Stitchwort, took 26 in
Lean and 23 in Rocq **[measured]**. Three theorems say nothing about the
whole; they were for testing the rules.

## 1. Strata

`SW-4537/sample.py` files each theorem counted by SW-4519's `count.py`
(theorems outside `Tests/`; statement lines to the `:=`, proof lines
non-blank and non-comment after it). A theorem whose conclusion (the text
after its last `):`) names a parser relation goes by that relation, as in
SW-4519 §2.2; the rest go by file.

| Stratum | What it is | Theorems | Statement lines | Proof lines | Both | Share | Draws |
|---|---|---|---|---|---|---|---|
| walk | concludes `Parse.Gives`, `ReadsAt`, `ReadsIn`, `Reads0` | 757 | 2,885 | 4,147 | 7,032 | 9.8% | 2 |
| two-run | concludes `Parse.Follows` | 618 | 3,009 | 3,841 | 6,850 | 9.5% | 2 |
| readback | concludes `Parse.Runs`, `RunsFrom` or a `…Reads` record, or is in `Syntax/ReadBack*` | 522 | 2,463 | 7,836 | 10,299 | 14.3% | 4 |
| tree | other facts in `Syntax/`: `Deaf`, alike, kept, carried, `Parsed` | 726 | 2,393 | 4,642 | 7,035 | 9.8% | 2 |
| lexer | `Syntax/Lex*`, `Fmt/FileLex`, `PrintLex`, `Token`, `SourcePlain` | 316 | 1,059 | 2,516 | 3,575 | 5.0% | 3 |
| settle | `Syntax/Settle*`, `OnceUnreturned`, `Fmt/Settle*`, `Unreturned`, `Split`, `Mark`, `Finish` | 527 | 1,853 | 5,930 | 7,783 | 10.8% | 3 |
| printer | everything else in `Fmt/`: `Doc` layout, hang, join, calm, touch, spell, told, elements | 1,813 | 7,619 | 19,890 | 27,509 | 38.3% | 11 |
| top | top theorems and drivers: `Accepts1`, `Driver1`, `TopStatements`, `TopReadBack`, `Grammar1`, `OutputStatements`, `ReadBackFile`, `CommentsKeptProof`, `MeaningProofs`, `Predicates`, `TriviaStatements` | 143 | 445 | 1,258 | 1,703 | 2.4% | 3 |
| **all** | | **5,422** | **21,726** | **50,060** | **71,786** | | **30** |

All **[measured]**; the totals match SW-4531's table for today. The file
lists are by file name and the files' headers, not by reading every
theorem, so a few theorems sit in a neighbouring stratum (a pure lemma in
a `ReadBack` file counts as read-back; SW-4519 noted the same of the
conclusion test). That costs a little sharpness per stratum and nothing
for the whole-slice figure, which only needs each theorem in exactly one
stratum.

The median theorem is 7 to 9 lines in every stratum; the weight is in the
tail (the 199 proofs over 40 lines hold 29% of proof lines, SW-4519).

## 2. Sample design

- **Size:** 30 theorems, 3 of them the pilot.
- **Allocation:** in proportion to a stratum's lines (statement plus
  proof), at least 2 each, largest remainders.
- **Draw:** inside a stratum, with replacement, each theorem's chance in
  proportion to its own lines (`random.Random(4537).choices`, theorems in
  file then line order). Three reserves per stratum are drawn in the same
  call, after the main draws.
- **Why by length:** a plain random draw would be mostly 7-line theorems
  and would miss where the lines are. Drawing by length makes the plain
  mean of the drawn theorems' ratios an unbiased estimate of the stratum's
  line ratio (Hansen-Hurwitz), and long proofs appear as often as their
  lines deserve. The price: the sample has five proofs of 60 to 260 lines.
- **Estimate:** stratum ratio = mean over its draws of (port lines /
  Stitchwort lines); slice ratio = the strata's ratios weighted by the
  "Both" column. `SW-4537/estimate.py` does it for lines and for
  non-blank characters, for Lean and Rocq.
- **Interval:** bootstrap, 10,000 resamples of the ratios with replacement
  inside each stratum, 5th and 95th percentiles of the slice ratio. With 2
  or 3 draws in a stratum the bootstrap understates that stratum's spread;
  the report should also give the range of ratios seen per stratum.
- **A trivial theorem** (a one-line proof) is ported as drawn. It is part
  of the population, and drawing by length already makes it rare.
- **A theorem drawn twice** counts twice (the draw is with replacement).
- **An unportable theorem** is set aside only by rule, never by taste:
  (a) no compiling proof in one of the systems after 45 minutes of agent
  time on that theorem, or (b) its cut-down support would pass 300 lines.
  The stratum's next reserve takes its place, in order. Set-asides are
  listed, and the estimate is given twice: with the replacements, and
  with each set-aside counted at the largest ratio seen in its stratum.
  Set-asides will be the long proofs, so the first figure leans in the
  ports' favour and the second against.

What the figure will and won't mean:

- It compares **the same theorems, proved again**. A Lean or Rocq
  developer might not state many of them at all (automation, `variable`
  sections, a different architecture). A theorem-by-theorem port can't
  see that, so the ratio is an upper bound on what those systems need.
  SW-4222 §3.6 counted 23 and 26 theorems for Stitchwort's 30.
- Definitions (the programs) and the standard library's lemmas aren't
  counted on either side.
- Layout matters: Stitchwort's formatter wraps at 120 columns and puts
  long calls one argument a line; the ports wrap at 100. So every figure
  is also given in non-blank characters.

### The sample

Main draws, in draw order. Lines are statement + proof **[measured]**.

| Stratum | # | Theorem | Where | Lines | Port |
|---|---|---|---|---|---|
| walk | 1 | `readsAtAtValue` | `Syntax/ParseCarriesDecl.sw:43` | 3 + 4 | pilot |
| walk | 2 | `readsBlockResult` | `Syntax/ParseCarriesLadder.sw:1098` | 3 + 13 | A |
| two-run | 1 | `followsParenAtom` | `Syntax/FollowsBase.sw:633` | 10 + 1 | A |
| two-run | 2 | `followsListPatternStep` | `Syntax/FollowsFormsPatterns.sw:803` | 9 + 8 | A |
| readback | 1 | `runsBlockOneLine` | `Syntax/ReadBackProofs.sw:120` | 10 + 23 | A |
| readback | 2 | `openWithin` | `Syntax/ReadBackHungFrameLemmas.sw:193` | 4 + 1 | A |
| readback | 3 | `unaryHung` | `Syntax/ReadBackHungApp.sw:499` | 11 + 145 | A |
| readback | 4 | `runsWalkHere` | `Syntax/ReadBackRuns.sw:1882` | 3 + 9 | A |
| tree | 1 | `argumentMinusDeaf` | `Syntax/DeafProofs.sw:201` | 1 + 3 | B |
| tree | 2 | `walkAttributesAlike` | `Syntax/FollowsDecl.sw:187` | 3 + 8 | B |
| lexer | 1 | `itemsShapesOfKinds1` | `Fmt/SourcePlainProofs.sw:160` | 5 + 6 | pilot |
| lexer | 2 | `headerResult1` | `Fmt/SourcePlainProofs.sw:353` | 1 + 36 | B |
| lexer | 3 | `plainOfShapes` | `Fmt/SourcePlainProofs.sw:508` | 3 + 9 | B |
| settle | 1 | `endsQuietJoin` | `Fmt/SettleOutputProofs.sw:912` | 1 + 6 | B |
| settle | 2 | `settledHomed` | `Syntax/SettleProofs.sw:1695` | 5 + 45 | B |
| settle | 3 | `homeStands` | `Fmt/SettleOutputProofs.sw:323` | 9 + 258 | B |
| printer | 1 | `closerFitsOf` | `Fmt/BracketHangProofs.sw:560` | 7 + 9 | pilot |
| printer | 2 | `heldItemSeat` | `Fmt/BracketHangProofs.sw:157` | 5 + 6 | C |
| printer | 3 | `stepsIfBroken` | `Fmt/TouchSteps.sw:335` | 4 + 1 | C |
| printer | 4 | `parenInnerKept` | `Fmt/CalmProofs.sw:526` | 4 + 3 | C |
| printer | 5 | `exprBlanks` | `Fmt/TraverseFail.sw:41` | 3 + 92 | C |
| printer | 6 | `refinesAppend` | `Fmt/ToldDeclProofs.sw:34` | 4 + 5 | C |
| printer | 7 | `notedCloserHangs` | `Fmt/HangProofs.sw:2061` | 13 + 19 | C |
| printer | 8 | `anyHangsOf` | `Fmt/ElementsProofs.sw:72` | 4 + 2 | C |
| printer | 9 | `blankItemHangs` | `Fmt/ElementsBlank.sw:212` | 16 + 97 | C |
| printer | 10 | `placedSteps` | `Fmt/TouchProofs.sw:483` | 4 + 3 | C |
| printer | 11 | `statementsWalk` | `Fmt/BlankProofs.sw:125` | 3 + 5 | C |
| top | 1 | `wordsCalmKeep` | `Fmt/CommentsKeptProof.sw:276` | 4 + 61 | C |
| top | 2 | `firstThreeKeepMeaning` | `Fmt/MeaningProofs.sw:436` | 2 + 1 | C |
| top | 3 | `witnessUnreturned` | `Fmt/TopStatements.sw:586` | 2 + 7 | C |

Reserves, used in this order when a main draw is set aside:

| Stratum | Reserves |
|---|---|
| walk | `readsTupleRest` (`Syntax/ParseKept.sw:693`, 10 + 32); `readsPrefixAtom` (`Syntax/ParseWalk.sw:714`, 8 + 29); `givesLambdaParam` (`Syntax/ParseWalkBinders.sw:262`, 4 + 10) |
| two-run | `followsUnfoldingClauseOf` (`Syntax/FollowsDeclBinders.sw:516`, 5 + 10); `followsAlternativeLinksOn` (`Syntax/FollowsFormsPatterns.sw:301`, 14 + 14); `followsExprWalk` (`Syntax/FollowsFormsBlocks.sw:225`, 4 + 3) |
| readback | `runsItems` (`Syntax/LexProofs.sw:242`, 8 + 12); `runsTupleClose` (`Syntax/ReadBackRuns.sw:540`, 4 + 10); `listStepsHung` (`Syntax/ReadBackHungAtoms.sw:555`, 15 + 73) |
| tree | `alikeFunctionType` (`Syntax/FollowsDeclHeaders.sw:427`, 5 + 5); `implicitBinderAheadDeaf` (`Syntax/DeafProofs.sw:178`, 2 + 9); `alikeData` (`Syntax/FollowsDeclArms.sw:809`, 10 + 24) |
| lexer | `wordyOperator` (`Syntax/LexReadsProofs.sw:259`, 3 + 3); `parsedSourcePlain1` (`Fmt/SourcePlainProofs.sw:750`, 6 + 10); `utf8OfAsciiRun` (`Syntax/LexProofs.sw:323`, 3 + 6) |
| settle | `arrowsFromTokens` (`Syntax/SettleProofs.sw:117`, 2 + 25); `lastArgumentFinishes` (`Fmt/FinishProofs.sw:203`, 4 + 32); `homeStands` again (if it is the one set aside, stop at two reserves) |
| printer | `appFromSpells` (`Fmt/SpellProofs.sw:935`, 7 + 75); `blankLeafHangs` (`Fmt/ElementsBlank.sw:56`, 20 + 27); `textPasses` (`Fmt/JoinProofs.sw:436`, 3 + 9) |
| top | `declsAll` (`Fmt/TopStatements.sw:265`, 13 + 17); `leavesWords` (`Fmt/CommentsKeptProof.sw:131`, 4 + 35); `sourceComments` (`Fmt/CommentsKeptProof.sw:488`, 7 + 41) |

The machine-readable list is `SW-4537/sample.json`. To redo the draw:

```
python3 docs/reviews/SW-4519/count.py tools/fmt/src /tmp/t.json
cd docs/reviews/SW-4537 && python3 sample.py ../../../tools/fmt/src /tmp/t.json --draw
```

The draw depends on the tree: it was made at `110e3e3fc`. The port lanes
read the theorems at that commit (`git show 110e3e3fc:tools/fmt/src/…`)
if `main` has moved.

## 3. Porting rules

For every port lane, so the batches compare.

**Statements**

1. The same statement: same hypotheses, same conclusion, same binders in
   the same order. Don't strengthen, weaken, generalise or reorder.
2. Translate encodings into the system's idiom, nothing more:
   `(a <= b) = True` on numbers becomes `a ≤ b` (`a <= b` in Rocq); a
   Stitchwort function that returns `Bool` stays a `Bool` function and
   its hypothesis stays `f x = true`; `∧`, `∃` and records of facts stay
   as they are. Rocq may put hypotheses after the colon as arrows or
   before it as named binders, as its users do.
3. Names stay, except where the system forces a change (Rocq's flat
   record field names: the pilot renamed binders `key` and `marked`).

**Definitions (uncounted, but reported)**

4. Cut down faithfully. Keep every constructor, field and function clause
   the proof's case analysis or computation goes through. Drop
   constructors, fields and clauses it never reaches, and say which in a
   comment (`Cut down from …: floor dropped`).
5. A function the Stitchwort proof unfolds or computes with is a real
   definition. A function it uses only through named lemmas may be
   opaque (`axiom`/`opaque` in Lean, `Parameter` in Rocq).
6. A lemma the Stitchwort proof names, other than the drawn theorem, is
   stated as an axiom with the same statement, uncounted, on both sides
   alike. Std's lemmas are the system's own library where it has them,
   and axioms or proved support where it doesn't. The port doesn't have
   to use them: if `simp` or `lia` closes the goal without the lemma,
   that is the port.
7. An axiom must be true of what it talks about. State lemma axioms over
   opaque functions or over real definitions they hold of; never over a
   stand-in that makes them false (the pilot's first Lean try made `Expr`
   a record of three fields with an axiom relating them: unsound, and
   replaced). In Lean, definitions over axioms go in a
   `noncomputable section`.
8. A theorem drawn from a mutually recursive group is ported alone: the
   other members are axioms (rule 6), and the port says so. Each member
   had its own chance of being drawn.
9. The parser (batch A) is a state monad over the mark that fails with a
   message, as in SW-4222's samples and the pilot. `Parse.ReadsAt`,
   `Gives`, `Follows` and `Runs` are defined over it, cut down from std's
   (the pilot drops `Honest`, the offset bookkeeping, which slice 1's
   proofs only pass along). Batch A writes one shared prelude with these
   and std's combinator lemmas (bind, done, weaken, peek, bump), proved
   or as axioms, uncounted: they are std in Stitchwort. A general tactic
   or `simp` set or hint database for the monad, written once, is also
   prelude (Stitchwort's `byWalking` is the language's). Anything written
   for one sampled theorem is counted with it.
10. Report the support's size per theorem (lines of definitions and
    axioms), so the cut-down's weight is visible.

**Proofs**

11. Idiomatic: what a competent user of the system would write and leave
    in a code base. Use the ordinary automation. Lean: `simp`,
    `simp_all`, `omega`, `decide`, `cases`/`induction`/`rcases`/`obtain`,
    `split`, `<;>`, `grind` and `fun_induction` (both in core at 4.35, checked).
    Rocq: `lia`, `auto`/`eauto`, `intuition`, `inversion`, `destruct` with
    patterns, `now`, `congruence`, `firstorder`, ssreflect (it ships with
    Rocq, in Corelib, checked), `Function`/`Equations` only if in Stdlib.
12. Not golfed: no proof that a reviewer would send back. One tactic per
    line in Lean except `<;>` chains; Rocq sentences may share a line as
    in SW-4222's `Sample.v`, and a one-sentence proof may be
    `Proof. … Qed.` on one line. Wrap at 100 columns. No `sorry`,
    `admit` or `Admitted` in a counted theorem.
13. Not transliterated either: don't follow the Stitchwort proof step by
    step where the system has a shorter ordinary route. Read the
    Stitchwort proof for the idea, then prove it as the system's user
    would.
14. No Mathlib and no other library: Lean core and `Std`, Rocq with
    Stdlib 9.0. Where a Mathlib tactic or lemma the porter knows would
    have shortened a proof, add a comment `-- mathlib: <what>, about n
    lines`, so stage 2 can report the bias as a count instead of a guess.
    In the pilot nothing wanted one **[measured, 3 theorems]**; SW-4222's
    21 ports didn't use it either **[read]**. I expect the bias to be
    small for this material (lists, naturals, case splits), a few per
    cent at most **[estimated]**.
15. Every port compiles with the commands in §5, with no errors. The lane
    runs them and pastes the last lines.
16. Time: at 45 minutes on one theorem in one system without a compiling
    proof, set it aside (§2) and take the reserve.

**Counting**

17. Each counted theorem follows a marker line, `-- sample: name` in Lean
    and `(* sample: name *)` in Rocq, and runs to the next blank line, so
    no blank lines inside it. `SW-4537/count_ports.py` counts statement
    and proof separately, in lines and in non-blank characters, for all
    three systems: SW-4464's count (statement plus proof, no doc
    comments), with the split added. In Rocq `Proof.` and `Qed.` lines
    count as proof, as SW-4222 and SW-4464 counted them.
18. A helper lemma written for one sampled theorem, and not a port of a
    Stitchwort lemma, is counted with that theorem: put it under the same
    marker name with a suffix the script can be taught, and say so in the
    lane's report. (None arose in the pilot.)

## 4. The pilot

The first draw of three strata: walk, lexer, printer. Files:
[`SW-4537/Pilot.lean`](SW-4537/Pilot.lean) and
[`SW-4537/Pilot.v`](SW-4537/Pilot.v). Both compile **[measured]**: Lean
4.35.0, Rocq 9.1.1 with Stdlib 9.0.0, from Nix.

Lines, statement + proof **[measured, `count_ports.py`, in `pilot.csv`]**:

| Theorem | Stratum | Stitchwort | Lean | Rocq |
|---|---|---|---|---|
| `readsAtAtValue` | walk | 3 + 4 = 7 | 3 + 4 = 7 | 3 + 1 = 4 |
| `itemsShapesOfKinds1` | lexer | 5 + 6 = 11 | 3 + 6 = 9 | 3 + 5 = 8 |
| `closerFitsOf` | printer | 7 + 9 = 16 | 7 + 3 = 10 | 7 + 4 = 11 |
| **Total** | | **15 + 19 = 34** | **13 + 13 = 26** | **13 + 10 = 23** |

Non-blank characters, statement + proof **[measured]**:

| Theorem | Stitchwort | Lean | Rocq |
|---|---|---|---|
| `readsAtAtValue` | 173 + 195 | 161 + 200 | 158 + 61 |
| `itemsShapesOfKinds1` | 203 + 228 | 200 + 231 | 193 + 156 |
| `closerFitsOf` | 314 + 354 | 303 + 122 | 276 + 162 |
| **Total** | **690 + 777 = 1,467** | **664 + 553 = 1,217** | **627 + 379 = 1,006** |

Ratios to Stitchwort on these three: Lean 0.76 by lines and 0.83 by
characters; Rocq 0.68 and 0.69. Three theorems of 34 lines are no
estimate of anything: `estimate.py` on them prints 0.71 and 0.67 with a
zero-width interval, which shows only that the script runs.

What each showed:

- **`readsAtAtValue`** (the parser asks "is the next token `wanted`?").
  Stitchwort chains three std lemmas. Lean unfolds the monad: the proof
  is 4 lines, two of them a list of twelve `StateT` internals for `simp`,
  which a prelude's simp set would remove (rule 9). Rocq, with its own
  two-line monad, is `inversion ran; subst. now exists [].` The model
  matters here: dropping `Honest` is what makes the direct route this
  short, and std's lemmas carry it for the Stitchwort proof. So the
  parser strata's ratios depend on rule 9's prelude more than on the
  porter, which is why one batch owns all of them.
- **`itemsShapesOfKinds1`** (a comma list's shapes are its kinds'
  shapes). One of a mutual pair with the same fact about expressions;
  ported alone (rule 8). The three proofs are the same proof: split the
  list, split the `&&`, rewrite with the two lemmas. Stitchwort's extra
  lines are the statement laid out one hypothesis a line.
- **`closerFitsOf`** (where a closing bracket's own line lands).
  Stitchwort: a nested match on the mark and a guard, plus two helper
  lemmas (`leftOfLower`, `closerAtMost`). Lean: take the mark apart,
  unfold, then `cases block <;> cases least <;> simp_all [leftOf] <;>
  split <;> omega`: no helper lemmas needed. Rocq the same with
  `destruct` and `lia`. This is SW-4222's "dispatcher" pattern again, on
  the printer's side: arithmetic case splits are where both systems are
  clearly ahead (3 and 4 proof lines against 9).

Costs **[measured]**: the three theorems took about 4 minutes of clock
time to read, port to both systems and compile; Rocq compiled first
time, Lean on the second (rule 7's mistake, and the code generator
refusing definitions over axioms). Support was the bulk of the files: 134
of `Pilot.lean`'s 160 lines and 133 of `Pilot.v`'s 156 are definitions,
axioms, comments and blank lines, about 45 lines a theorem. These were three short
theorems with shallow definitions; the long ones in the batches will not
go at this rate.

Rules changed by the pilot: 2 (comparisons become propositions), 3
(forced renames), 7 (true axioms only, `noncomputable section`), 8
(mutual groups), 9 (the parser prelude and what counts as library).

## 5. The batches

27 theorems, three Opus port lanes, split by stratum so each lane builds
one set of definitions. Each lane writes `SW-4537/BatchX.lean` and
`SW-4537/BatchX.v`, one namespace or module per theorem (as the pilot),
and reports per theorem: lines by `count_ports.py`, support lines, time,
set-asides, and `mathlib:` notes.

Commands (from `docs/reviews/SW-4537/`):

```
nix shell nixpkgs#lean4 -c lean BatchX.lean
STD=$(nix build --no-link --print-out-paths nixpkgs#rocqPackages.stdlib)
nix shell nixpkgs#rocq-core -c rocq compile -R $STD/lib/coq/9.1/user-contrib/Stdlib Stdlib BatchX.v
python3 count_ports.py ../../../tools/fmt/src sample.json BatchX.lean BatchX.v
```

Compile the `.v` from a scratch copy: `rocq compile` leaves `.vo`,
`.glob` and `.aux` files beside it, which must not be committed.

| Batch | Strata | Theorems | Stitchwort lines | Definitions it needs | Estimate |
|---|---|---|---|---|---|
| A, the parser | walk 2; two-run 1, 2; readback 1 to 4 | 7 | 250 (156 of them `unaryHung`) | the shared parser prelude (rule 9): mark, monad, `ReadsAt`, `Gives`, `Follows`, `Runs` and their std lemmas, starting from `SW-4222-samples/Sample.lean`/`.v` (monad, `Gives`, `Follows`) and the pilot's `ReadsAt`; cut-down `Tok`, `Item`, `Word`, `Expr`, `Modes`, `Goal`; the read-back's hung-line records for `unaryHung` and `openWithin` | 60 min |
| B, the syntax side | tree 1, 2; lexer 2, 3; settle 1 to 3 | 7 | 388 (267 of them `homeStands`) | `Item` and `Item.stripped`, `argumentMinus`/`argumentPrefix`; attributes and the alike relation; `PlainShape`, header and plain-source functions from `Fmt/SourcePlainProofs.sw`; the settle functions (`Syntax/Settle*.sw`: home, quiet ends) and `Stands` for `homeStands` | 70 min |
| C, the printer and the top | printer 2 to 11; top 1 to 3 | 13 | 370 (113 `blankItemHangs`, 95 `exprBlanks`, 65 `wordsCalmKeep`) | std's `Doc`, `Place`, `Hang`, `Carry` and print state, cut down (the pilot's `OpenMark`, `Carry`, `leftOf`, `CloserFits` carry over); the hang and steps relations (`Hangs`, `Steps`, `Placed`), calm and kept predicates, blanks traversal; for the top three, comments-kept words, the meaning relation and the unreturned witness | 60 min |

Estimates are agent time **[estimated]**, from the pilot (a short
theorem in both systems: 1 to 3 minutes) and an allowance of 15 to 25
minutes for each proof over 60 lines, most of it support definitions.
The five long proofs (`homeStands`, `unaryHung`, `blankItemHangs`,
`exprBlanks`, `wordsCalmKeep`) are 696 of the sample's 1,042 Stitchwort
lines, so they will carry the estimate; each lane should start with its
long ones, so that a set-aside is known early.

Stage 2, after the batches: run `count_ports.py` over the pilot and the
three batches into one `results.csv`, run `estimate.py` on it for lines
and characters, and write the per-stratum table, the whole-slice ratio
with its interval, the set-asides both ways, the statement/proof split,
and the `mathlib:` count.

## 6. Limits

- 30 theorems in 8 strata is thin per stratum: read the per-stratum
  ratios as "ahead, level, behind", not as numbers.
- Long proofs dominate, and they are the ones most at risk of being set
  aside. If more than two are set aside, the whole-slice figure should
  be reported as a range between the two imputations, not as a point.
- The sample measures today's text. It doesn't measure check time,
  error messages, or how long the proofs took to write.
- Three port lanes are three writers. Batches are whole strata, so a
  writer's style is confounded with its strata; the rules above are the
  only control. A cheap check, if wanted: one theorem from each batch
  ported again by another lane.
