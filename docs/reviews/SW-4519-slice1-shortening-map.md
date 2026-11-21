# Where slice 1's proof lines are, and what would cut them most

**Status:** paper lane SW-4519 (Opus), 21 November 2026, against `main` at
`21248d169`. Nothing is built or run; no code changes. It feeds the
`parser-proofs` epic's next lanes.

How claims are marked:

- **[measured]**: counted today by the scripts in [`SW-4519/`](SW-4519/)
  (heuristic text scans, so good to a few per cent);
- **[read]**: read in the file named;
- **[estimated]**: my judgement, by hand, of a proof under a tool use not
  tried, mostly from a 24-theorem sample (§3).

## In plain words

**The question.** Slice 1 is proved over its whole grammar. To make
Stitchwort a match for Lean and Rocq the proof should also be short and
clean. Where are its 50,000 proof lines now, and which change cuts the most?

**What I found.**

1. **The walk has done most of what it can reach.** The parser relations
   the walk handles (`Follows`, `Gives`, `ReadsIn`, `ReadsAt`, `Reads0`) hold
   7,816 proof lines, 16% of the total, and 494 theorems already walk in 660
   lines [measured]. 473 hand-written parser steps are left, in 4,296 lines,
   blocked by known gaps (SW-4482, SW-4470, SW-4467, SW-4468, and the 145
   leaves that need a hand `then`) [measured, gaps read from SW-4477's review].
2. **The biggest family nobody walks is the read-back.** Theorems whose
   conclusion is `Parse.Runs`, `Parse.RunsFrom` or a read-back record
   (`AtomReads`, `MulReads`, …): 205 theorems, 4,933 proof lines, no walks
   [measured]. `Parse.Runs` isn't a walk family: its bind lemma fixes the
   split and the value (`runsBind p j first next read rest v value joined …`)
   rather than quantifying over them, so it doesn't fit the walk's
   `walk.then` shape [read].
3. **The single biggest kind of line is an argument on its own line.**
   5,703 proof lines are a bare name or `_`, 10,523 if simple bracketed
   arguments count too: 11% and 21% of all proof lines [measured]. They come
   from lemma calls that pass every argument explicitly, which the formatter
   lays out one per line once a call doesn't fit in 120 columns. In
   `ReadBackRuns.sw`, the biggest file, they are 58% of its lines. About half
   of them are values that unification fixes from the goal or from another
   argument, which proving-guide rule 9 says to write `_` (or make implicit,
   D2422) [estimated, from the sample]; the rest are proofs in scope, which
   `byFacts [lemma]` can supply.
4. **Repeated match arms are the second biggest.** 2,084 proof lines are
   match arms whose text is the same as a sibling arm's up to names
   [measured]: `cases x then t` (SW-4474, merged) can say each once. Another
   1,456 arms are just `=> byComputing` [measured].
5. **`byFacts` matters, but less than its reputation.** 2,808 lines name
   `Bool.andLeft`, `andRight` or `andIntro` [measured]; in the sample it would
   take about 4% of lines, in line with closer.md's "4 to 10%" [estimated].
   SW-4515 is measuring it.
6. **Small or no gain:** families of structurally identical lemmas across
   theorems are only 428 lines in 71 theorems [measured]; slice-parametric
   statements save nothing today, since no slice but 1 has proofs
   [measured]; the names ending in 1 (SW-4463: 106 theorems) are naming
   noise, worth fixing for reading, worth zero lines.

**What it should do.** Done in the order of §5, the five lanes should take
roughly **9,000 to 13,000 proof lines out of 50,167 (18 to 26%)**
[estimated], with no statement changed. The sample's ceiling, everything
I could see going, is 42%.

## 1. How I counted

`count.py` reads every `.sw` file under `tools/fmt/src` and, for each
top-level `theorem`, splits it at the first `:=` outside brackets (strings
and comments skipped). The **statement** is the lines from `theorem` to
that `:=`; the **proof** is the non-blank, non-comment lines after it up
to the next line at column 0, plus one if the proof starts on the `:=`
line. `def`s are not counted, even when they return proofs; doc comments
are not counted. The `Tests/` folders are left out of the figures below
(125 theorems, 125 lines).

Result: **5,422 theorems, 50,167 proof lines, 21,726 statement lines**
[measured]. The theorem count matches the brief's 5,422. The brief's
49,898 counts whole proof files, so the two figures measure different
things.

The proof lines are spread out: the top 10 files hold 25.5%, the top 20
43.1%, the top 40 66.3%, over 137 files [measured]. Of the theorems,
1,571 have a one-line proof, and the 199 longest (over 40 lines) hold 29% of
the lines [measured].

## 2. Ranking

### 2.1 By file

| # | File | Theorems | Proof lines | Statement lines |
|---|---|---|---|---|
| 1 | `Syntax/ReadBackRuns.sw` | 99 | 1,811 | 584 |
| 2 | `Fmt/ToldDeclProofs.sw` | 126 | 1,449 | 508 |
| 3 | `Syntax/LexProofs.sw` | 127 | 1,404 | 537 |
| 4 | `Fmt/SettleOutputProofs.sw` | 87 | 1,332 | 352 |
| 5 | `Fmt/JoinProofs.sw` | 143 | 1,298 | 567 |
| 6 | `Fmt/CalmProofs.sw` | 130 | 1,174 | 427 |
| 7 | `Fmt/TouchProofs.sw` | 79 | 1,148 | 416 |
| 8 | `Syntax/SettleProofs.sw` | 99 | 1,101 | 310 |
| 9 | `Fmt/HangProofs.sw` | 131 | 1,041 | 673 |
| 10 | `Syntax/SettleBareProofs.sw` | 86 | 1,040 | 326 |
| 11 | `Fmt/SpellProofs.sw` | 123 | 987 | 407 |
| 12 | `Syntax/ReadBackLine.sw` | 153 | 942 | 417 |
| 13 | `Fmt/SpeltSlots.sw` | 52 | 915 | 218 |
| 14 | `Fmt/StandsProofs.sw` | 46 | 906 | 182 |
| 15 | `Fmt/Walk.sw` (the tree walk, not `byWalking`) | 82 | 890 | 222 |
| 16 | `Fmt/OutputFileProofs.sw` | 83 | 885 | 341 |
| 17 | `Fmt/ElementsProofs.sw` | 27 | 879 | 217 |
| 18 | `Fmt/TreeJoinProofs.sw` | 65 | 820 | 229 |
| 19 | `Syntax/GoodItemProofs.sw` | 57 | 798 | 176 |
| 20 | `Syntax/FollowsStatements.sw` | 135 | 794 | 683 |

Of these twenty, only `GoodItemProofs` (2) and `FollowsStatements` (43)
have any `byWalking` [measured].

### 2.2 By what the theorem concludes

| Conclusion | Theorems | Proof lines | Walks |
|---|---|---|---|
| Pure functions: printer, settle, lexer, tree facts (no parser relation) | 3,841 | 37,271 | 0 |
| `Parse.Follows` (two runs) | 604 | 3,667 | in these five rows: 494 |
| `Parse.Gives` | 505 | 2,031 | |
| `Parse.ReadsAt` | 105 | 1,241 | |
| `Parse.ReadsIn` | 111 | 792 | |
| `Reads0` | 36 | 85 | |
| `Parse.Runs` (read-back, completeness) | 121 | 2,465 | 0 |
| read-back records (`AtomReads`, `MulReads`, …) | 68 | 2,019 | 0 |
| `Parse.RunsFrom` (lexer read-back) | 16 | 449 | 0 |
| `Kept` | 15 | 147 | 0 |

All [measured]; a theorem is filed by the first of these relations in the
text after its last `):`, so a few with a relation only in a hypothesis
are misfiled.

Three quarters of the proof is about pure functions, where the walk has
nothing to do. The tools that reach it are the general ones: `_` for
arguments, `cases x then t`, `byFacts`.

## 3. The sample

24 theorems drawn at random (seed 4519), each proof line equally likely,
so long proofs come up in proportion to their lines: 837 lines, 1.7% of
the total. For each I estimated what each kind of change would remove.

| Theorem (file) | Lines | `_` / implicit | `cases x then t` | `byFacts` | walk | Other |
|---|---|---|---|---|---|---|
| `argsRunsOf` (ReadBackTree) | 24 | 10 | | | | |
| `hearsSpaces` (HearProofs) | 9 | | | 2 | | |
| `buildDrop` (SettleBareProofs) | 60 | 8 | | 7 | | |
| `runsLeftChain` (ReadBackRuns) | 16 | 12 | | | | |
| `laidMovedStarts` (SettleOnceProofs) | 6 | | | 3 | | |
| `prefixSteps` (TouchProofs) | 97 | 20 | | 5 | | |
| `bracketContentPasses` (JoinProofs) | 68 | 8 | | 2 | | |
| `headerGrammar1Deaf` (DeafProofs) | 36 | | 33 | | | |
| `followsFieldsAt` (FollowsDeclData) | 28 | | | | 20 | |
| `toldAboveExact` (ToldWordProofs) | 7 | | 3 | | | |
| `followsThenBodyOn` (FollowsStatements) | 27 | | | | 15 (SW-4482) | |
| `wordLeafPasses` (JoinProofs) | 24 | 4 | | | | |
| `argumentHung` (ReadBackHungApp) | 43 | 6 | | 6 | | |
| `appFromSpells` (SpellProofs) | 75 | 20 | | | | |
| `runsUnaryPrefix` (ReadBackRuns) | 39 | 27 | | | | |
| `stepsSoft` (TouchSteps) | 5 | | | | | |
| `blankItemHangs` (ElementsBlank) | 134 | 50 | 50 | | | |
| `addAccHung` (ReadBackHungChains) | 95 | 15 | | 10 | | |
| `bitsShapeAppend` (StandsProofs) | 3 | | | | | |
| `bracketBack` (ElementsHomed) | 6 | | | | | 1 |
| `commentedSound` (SpellProofs) | 1 | | | | | |
| `arrowsFromTokens` (SettleProofs) | 25 | 8 | | | | |
| `trailingSilent` (FinishProofs) | 3 | | 2 | | | |
| `fillSteps` (TouchSeq) | 6 | | | | | |
| **All 24** | **837** | **188 (22%)** | **88 (11%)** | **35 (4%)** | **35 (4%)** | **1** |

All [estimated]. The columns don't overlap: where two changes reach the
same line, the line is counted under the one listed first.

What the kinds look like in the sample [read]:

- **Arguments the goal fixes.** `runsUnaryPrefix` is six nested
  `runsLook`, `runsBind` and `runsMap` calls. Each passes the parser, the
  continuation, the read list, the rest and the value, one per line, when
  the goal or the inner lemma's conclusion fixes all of them but the
  continuation. `appFromSpells` restates 15 lines of the program's own
  `Doc` output as an argument that `spellsChoice`'s conclusion fixes.
  `blankItemHangs` passes `blankNodeAt` 17 arguments in each of its
  constructor arms, most of them the same names in every arm.
- **Arms that say the same thing.** `headerGrammar1Deaf` matches eight
  fields one after another, each `Some` arm being `byComputing` and only the
  last arm doing anything (`rewrite exprGrammar1Deaf result`).
  `blankItemHangs`'s `Paren`, `Tuple` and `ListOf` arms are one text with
  the constructor changed.
- **Conjunction plumbing.** `buildDrop` builds `lastPair … = True` by
  `Bool.andIntro isComma (Bool.andIntro isCloser byComputing)`, and
  `laidMovedStarts` reaches a part with `Bool.andRight` four deep.
- **Walks not taken.** `followsFieldsAt` is a chain of `followsThen` and
  `followsThenEq` steps ending in a record of twins. `followsThenBodyOn`
  splits two runs on two related guards, written out in full twice: this is
  SW-4482's gap (1).

Long theorems in the biggest files that I read outside the sample
(`runsTuple`, `elShape`, `runsItemsFrom`) are the same mixture, weighted
towards explicit arguments [read].

## 4. The kinds, across the whole proof

| Kind | Indicator over all 50,167 lines [measured] | Lines saved [estimated] | Tool work first |
|---|---|---|---|
| A. Values the goal or another argument fixes, passed explicitly | 5,703 bare-argument lines (10,523 with simple bracketed ones); 58% of `ReadBackRuns.sw` | 4,000 to 7,000 | none for `_`; for std's `Parse.runs*` and the formatter's own lemmas, implicit binders (D2422) are a signature change, nothing more |
| B. Read-back (`Runs`, `RunsFrom`, read-back records) written by hand | 205 theorems, 4,933 lines, 0 walks | 1,500 to 2,500 beyond A, in those files | a walk family whose `then` lemma fixes the split and value from the callee's lemma instead of quantifying over them: a design note first |
| C. Sibling arms with the same text | 2,084 lines beyond the first of each group, in 536 theorems; 1,456 arms that are just `byComputing` | 1,000 to 1,500 | none (`cases x then t`, SW-4474); more once A has made arms alike |
| D. Conjunctions and records built or taken apart by hand | 2,808 lines name `Bool.and*`; 323 lines are only `let x := Bool.and… h` | 1,500 to 2,500 | none (SW-4488), subject to SW-4515's check-time bar |
| E. Parser steps not yet walked | 473 theorems, 4,296 lines | about 1,500 | SW-4482, SW-4470, SW-4467, SW-4468; `byFacts` as the walk's leaf closer for the 145 leaves that need a hand `then` |
| F. Families of near-identical lemmas | 71 theorems in 17 structural families, 428 lines (the `…Blank` list lemmas, `…Calm` pairs) | about 300 | none: one generic lemma per family |
| G. Slice-parametric statements | no slice but 1 has proofs | 0 today | none: this is for when slice 2 is proved |
| H. Names ending in 1 (SW-4463) | 106 theorems | 0 | none; worth it for reading only |
| I. Statements | 21,726 lines, 30% of theorem text; 418 extra lines in multi-line typed `let`s | not estimated | bundling repeated hypothesis groups into records, as `AtomFacts` and the `facts` of `addAccHung` already do, re-types statements (orchestrator-checked, D2436), and moves lines rather than removing many |

Where kinds meet in a file, the estimates are not additive: A first makes
B, C and D smaller. Summed with that overlap taken out, A to F come to
about **9,000 to 13,000 lines** [estimated]. Each range is good to a factor
of about 1.5: the sample has 24 theorems, and the indicators are text
scans.

Two cautions:

- **Check time.** `_` makes the elaborator solve what it was handed, and
  `cases` as a closer costs 10 to 45 ms where a term costs 2
  (closer.md §2.3). Every lane below keeps D3696's bar (no theorem over 3
  times its hand proof, each namespace within 1.5 times) and reports times.
- **Layout is not the target.** Most of kind A's lines exist because the
  formatter puts one argument per line once a call is too long. Changing that
  rule would shorten the files without making any proof simpler. It would
  also change the formatter's style, which is user-visible and Matt's, and
  it would change slice 1's proved output (D3688, D3704). I don't propose
  it.

## 5. The next five lanes

In order. The estimates are agent time, already scaled by the 0.33
median. No lane changes a statement's meaning or a slice's scope. Every
lane stays out of the 31 theorems SW-4515 is converting, and out of its
files until it merges.

| # | Lane | Model | Estimate | Should save |
|---|---|---|---|---|
| 1 | **Unfixed arguments, pilot.** In `Syntax/ReadBackRuns.sw` and `Fmt/ElementsBlank.sw`, write `_` for every argument that the goal or another argument fixes (proving guide rule 9). Where a lemma in the file is always called with `_` in a position, make that binder implicit instead (D2422). Report proof lines and check time per theorem, against D3696's bar. Then write the rules for which positions take `_`, for a sweep | Sonnet | 35 min | 800 to 1,100 lines in the two files [estimated]; the evidence for kind A |
| 2 | **One text over arms.** `cases x then t` for the top 60 theorems in `arms.py`'s list (`exprBlanks`, `opKind`, `elShape`, `exprRuns`, `elCalm`, `elSpells`, `declBlanks`, `declOk`, …: about 1,100 repeated lines), and the `Deaf` ladders like `headerGrammar1Deaf`. Keep a conversion only within the bar | Sonnet | 40 min | 600 to 900 lines [estimated] |
| 3 | **A walk for the read-back, design note.** How `Parse.Runs`, `Parse.RunsFrom` and the read-back records become walk families: a `then` lemma whose split and value come from the callee's lemma. Whether std's `Parse.runs*` should take its read lists and values as implicits. Three `ReadBackRuns` theorems sketched before and after. In `docs/proposals/`, stopping for decisions | Opus (paper) | 30 min | none itself; prices kind B (4,933 lines at stake) |
| 4 | **Walk W5.** Once SW-4515 reports: `byFacts` as the walk's leaf closer (the 145 leaves that need a hand `then`), SW-4482's related-values split, and SW-4470's missing lemmas; then convert the 473 hand parser steps that now walk | Opus (walk changes are tactic work, D2506); the conversion by Sonnet | 60 min + 40 min | about 1,500 lines [estimated] |
| 5 | **Unfixed arguments, sweep.** Lane 1's rules over the top 40 files by proof lines, if lane 1 met its bar. Two or three Sonnet lanes by area (read-back and lexer; printer; settle), or DeepSeek for the mechanical part, since the rule is mechanical and the kernel checks each proof | Sonnet or DeepSeek | 45 min a lane | 3,000 to 5,000 lines [estimated] |

`byFacts` as a sweep over the printer files (kind D) comes after these, if
SW-4515's bars 1 and 2 hold. It could take lane 5's place if lane 1
disappoints. Kind F (the `…Blank` and `…Calm` families, about 300 lines) is
one well-bounded DeepSeek ticket. SW-4463's renames can run at any time.

### Decisions for Matt

None of the five lanes needs one before it starts. Two could come later:

- If lane 3 proposes new proof syntax for the read-back walk, rather than
  attributes on std lemmas, that syntax is Matt's.
- The formatter's one-argument-per-line rule (§4, second caution) is
  Matt's if anyone wants it changed. My recommendation is no: it doesn't
  simplify any proof.

Nothing here narrows a slice or weakens a theorem (D3688). Lane 1's
implicit binders and any statement re-typing keep each proposition the
same, and are checked statement by statement in review (D2436).

## 6. Findings worth tickets

1. **`Parse.Runs` has no walk family**, and the read-back is 4,933 proof
   lines (lane 3).
2. **Formatter proofs ignore proving guide rule 9**: they pass unfixed
   arguments explicitly, which accounts for up to 21% of proof lines (lanes
   1 and 5). The guide could open its "Before writing the term" list with
   it, for lanes that generate proofs by script.
3. **`Deaf` ladders** (124 theorems, 694 lines) are mostly nested matches
   whose arms are `byComputing`. Lane 2 covers them, or a single
   `cases a, b, … then t` per theorem.
4. **Kind F's families**: `paramsBlank`, `armsBlank`, `scrutineesBlank`,
   `clausesBlank`, `inductArmsBlank` and three more (`FollowsFormsBinders`),
   five in `FollowsDeclArms`, and the `…Calm` and `…Blanks` groups: one
   generic lemma each (DeepSeek).
5. **W4b's lane scripts weren't kept** (SW-4477 review). This lane's are in
   [`SW-4519/`](SW-4519/), so later lanes can re-measure against these
   figures.
