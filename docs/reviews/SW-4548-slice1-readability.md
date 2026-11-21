# Slice 1 against Lean 4 and Rocq: how it reads (SW-4548)

**Status:** Fable paper lane, 21 November 2026. A reading review of the self-hosted formatter's
slice 1 proof (`tools/fmt`), beside the Lean and Rocq ports of SW-4537's 30 sampled theorems
([`SW-4537-results.md`](SW-4537-results.md) measured their size). Nothing was built or checked.
The scores are in [`SW-4548/scores.csv`](SW-4548/scores.csv); `SW-4548/means.py` gives the means.

Marks: **[measured]** counted by a script today, at this branch's `main`; **[scored]** my
judgement against the rubric, one rater, one pass; **[read]** read in the file named;
**[estimated]** a guess from counts.

## In plain words

**Where we stand.** Read as a newcomer would read them, the three systems come out level
overall, for opposite reasons **[scored, 30 theorems]**:

| Out of 5 | Stitchwort | Lean | Rocq |
|---|---|---|---|
| Statement and interface | 3.2 | 3.3 | 3.3 |
| Proof free of noise | **3.1** | 4.1 | 4.1 |
| Proof can be followed | **3.9** | 3.0 | 3.0 |
| Names (the ports copy ours) | 2.7 | 2.7 | 2.7 |
| Says what it is for (ours only; the ports carry no docs) | 2.6 | | |

- **Our proofs are noisier.** On 20 of the 30 the Lean port has less bookkeeping than ours, and
  ours less on 4. The long proofs are the worst: 1.7 against 3.3 and 3.2. This is the same gap
  SW-4537 measured in lines, seen from the reader's side: every case written out, one argument a
  line, `Bool.andLeft` chains.
- **Our proofs are easier to follow.** On 16 of the 30 ours shows which fact closes which case
  better than Lean's, and on 1 worse. The ports get short by `cases x <;> simp_all [twelve
  lemmas]`: quiet, but a reader learns only that it worked. `wordsCalmKeep` is the clearest
  case: 61 lines of ours against 8, and the 8 can't be followed at all.
- **The statements are the same statements**, so they read the same; and the lowest scores of
  all are the two that no port can change: names (2.7) and what a theorem is for (2.6).

So the reading gap with Lean and Rocq is small and is the size gap again. What stands between
slice 1 and clean is mostly not that gap: it is that a newcomer cannot tell what the words
mean. The ports don't fix that; they inherit it.

**The top is good.** The three top theorems and `slice1Formats` can be read cold: each says in
plain words what it claims and how the proof goes. I got lost one step below them.

**The top three things to fix**, none of which changes a statement:

1. **A key to the vocabulary.** 365 named properties, 111 with no description; `Hangs`, `Hung`,
   `Lays`, `Spelt`, `Deaf`, `Calm`, `Stands`, `Quiet`, "rule N" (102 mentions) and P1 to P4 are
   never defined where a reader meets them. Fix: a glossary and a map of the proof from the
   top theorems down, and a line for each of the 111. About 3 Sonnet lanes of 30 min
   **[estimated]**.
2. **Say what each long proof does.** 556 of the 838 proofs over 15 lines have no proof idea;
   12 of the 30 sampled theorems have no description at all, and several that have one give a
   label, not a claim ("A closer with own-line comments."). Fix: proof ideas, longest first: the
   longest 200 cover 55% of the unexplained lines. About 6 Sonnet lanes of 40 min
   **[estimated]**.
3. **Cut the noise in the long proofs.** One-argument-a-line calls (7,457 lines), `Bool.and`
   chains (2,790 lines), `= True` on hypotheses (2,781 statement lines), and facts passed one at
   a time (697 theorems with eight or more binders). The fixes with today's features are the
   ones the stock take already ordered (SW-4530's implicit values, bundling facts in records,
   dropping `= True` where the hash is unchanged). This review adds no new one, only that they
   matter for reading as much as for size.

Kept apart, because they need a tool or language change and I don't recommend building either
on this evidence: automation for case splits (it would buy lines and cost the "can be followed"
lead), and the formatter's one-argument-a-line rule for long calls.

## 1. The rubric

The reader knows what a code formatter does and can read a proof assistant's syntax, but has
never seen this code. Each criterion is 1 to 5.

| | Criterion | 5 | 3 | 1 |
|---|---|---|---|---|
| **S** | **Statement and interface.** Can they say what is claimed from the statement alone? | reads as a sentence; few binders; hypotheses are named facts | readable with effort: six to eight binders, or an encoding in the way (`= True`, a thunk, a lambda for the spec) | more than ten binders, or the claim can't be picked out from the parameters |
| **N** | **Noise.** How much of the proof is not argument? | every line is a step | some bookkeeping: restated terms, taking pairs apart, a lemma bag | mostly bookkeeping or layout: one argument a line, the same arm many times |
| **T** | **Can be followed.** Does the proof show which fact closes which case? | each case and the fact that closes it is visible | the route is visible, some steps are "it computes" | a black box: one tactic line over all cases, or positions with no names |
| **Names** | Do the theorem's name, the hypotheses' names and the predicates say what they are? | all plain | the theorem's name is a fair label, a predicate or two is private | the name says nothing of the claim, or several private words meet |
| **Doc** | Does the description say what is proved, why, and (over 15 lines) the proof's idea? | all three, in words a newcomer has | a true label, or a claim that needs the private words | none |

S, N and T are scored for each system. Names is scored once: the ports keep our names (SW-4537's
rule), so it cannot differ. Doc is scored for Stitchwort only: the ports were written to be
counted, and none carries a description. A fair comparison of signposts would need ports written
to be read, which these were not.

What the rubric leaves out: whether a statement is the *right* one, check time, and how easy a
proof is to change.

## 2. The scores

**How blind.** I read every port (Lean, then Rocq) before opening any Stitchwort original, and
the originals after. I did not write the ports' scores down before reading the originals, so the
ports were read blind but scored knowing all three; and I wrote SW-4531's stock take, so I knew
slice 1's style and had seen SW-4537's line counts and its list of causes. The longest blocks I
read in part: the first 34 lines of the Rocq `unaryHung`, `homeStands` and `settledHomed`, and
the first 30 of the Stitchwort `unaryHung`, `homeStands`, `exprBlanks`, `blankItemHangs`,
`wordsCalmKeep`, `headerResult1`, `runsBlockOneLine`, `settledHomed` and `notedCloserHangs`;
the Lean ports in full. One rater and one pass: read differences of 0.3 or less as level.

The Stitchwort originals are as at this branch's `main`, not the draw (`110e3e3fc`).

| Stratum | Theorem | Names | Doc | SW S N T | Lean S N T | Rocq S N T |
|---|---|---|---|---|---|---|
| walk | `readsAtAtValue` | 3 | 4 | 3 3 4 | 4 2 2 | 4 5 3 |
| walk | `readsBlockResult` | 3 | 4 | 3 3 4 | 3 3 3 | 3 4 2 |
| two-run | `followsParenAtom` | 3 | 1 | 2 5 3 | 2 4 4 | 3 4 4 |
| two-run | `followsListPatternStep` | 3 | 1 | 2 3 4 | 2 4 4 | 2 4 4 |
| readback | `runsBlockOneLine` | 3 | 3 | 2 1 3 | 2 4 3 | 2 4 3 |
| readback | `openWithin` | 3 | 4 | 4 5 4 | 4 5 4 | 4 5 4 |
| readback | `unaryHung` | 2 | 5 | 2 2 4 | 2 3 3 | 2 3 2 |
| readback | `runsWalkHere` | 2 | 1 | 3 2 3 | 4 5 3 | 4 4 3 |
| tree | `argumentMinusDeaf` | 2 | 1 | 4 5 5 | 4 4 3 | 4 5 4 |
| tree | `walkAttributesAlike` | 3 | 1 | 4 3 5 | 4 5 2 | 4 5 2 |
| lexer | `itemsShapesOfKinds1` | 3 | 1 | 3 3 4 | 3 4 3 | 3 4 4 |
| lexer | `headerResult1` | 3 | 3 | 4 1 2 | 4 5 2 | 4 3 2 |
| lexer | `plainOfShapes` | 3 | 2 | 3 3 4 | 3 4 3 | 3 2 3 |
| settle | `endsQuietJoin` | 3 | 1 | 4 4 4 | 4 5 2 | 4 4 3 |
| settle | `settledHomed` | 2 | 4 | 3 3 4 | 3 3 4 | 3 3 4 |
| settle | `homeStands` | 2 | 5 | 2 2 4 | 2 3 3 | 2 3 3 |
| printer | `closerFitsOf` | 3 | 4 | 3 3 4 | 4 5 2 | 4 4 2 |
| printer | `heldItemSeat` | 2 | 2 | 3 3 2 | 3 5 2 | 3 5 2 |
| printer | `stepsIfBroken` | 3 | 1 | 3 4 5 | 3 4 5 | 3 5 4 |
| printer | `parenInnerKept` | 3 | 1 | 4 5 3 | 4 5 2 | 4 4 3 |
| printer | `exprBlanks` | 3 | 4 | 4 1 4 | 4 3 2 | 4 3 2 |
| printer | `refinesAppend` | 4 | 1 | 4 4 5 | 4 5 2 | 4 5 2 |
| printer | `notedCloserHangs` | 2 | 2 | 2 2 3 | 2 3 3 | 2 3 3 |
| printer | `anyHangsOf` | 2 | 1 | 3 5 5 | 3 5 5 | 3 5 4 |
| printer | `blankItemHangs` | 2 | 5 | 2 1 4 | 2 3 4 | 2 4 3 |
| printer | `placedSteps` | 3 | 2 | 3 4 4 | 3 5 4 | 3 4 3 |
| printer | `statementsWalk` | 2 | 1 | 4 5 5 | 4 4 3 | 4 5 4 |
| top | `wordsCalmKeep` | 3 | 5 | 4 2 4 | 4 3 1 | 4 3 1 |
| top | `firstThreeKeepMeaning` | 4 | 4 | 5 4 5 | 5 5 4 | 4 5 4 |
| top | `witnessUnreturned` | 3 | 3 | 3 3 4 | 3 5 4 | 3 5 3 |

Means **[scored; `means.py`]**. These are plain means over the 30 draws; the draw favours long
theorems within each stratum, so the long rows weigh more here than they do in the slice.

| | Names | Doc | SW S | SW N | SW T | Lean S | Lean N | Lean T | Rocq S | Rocq N | Rocq T |
|---|---|---|---|---|---|---|---|---|---|---|---|
| All 30 | 2.7 | 2.6 | 3.2 | 3.1 | 3.9 | 3.3 | 4.1 | 3.0 | 3.3 | 4.1 | 3.0 |
| 21 with a proof of 15 lines or fewer | 2.9 | 2.0 | 3.3 | 3.8 | 4.1 | 3.5 | 4.4 | 3.1 | 3.5 | 4.4 | 3.2 |
| 9 with a longer proof | 2.4 | 4.0 | 2.8 | 1.7 | 3.6 | 2.8 | 3.3 | 2.8 | 2.8 | 3.2 | 2.6 |

Theorem by theorem, Stitchwort ahead, level, behind:

| | against Lean | against Rocq |
|---|---|---|
| Statement and interface | 0, 27, 3 | 1, 25, 4 |
| Noise | 4, 6, 20 | 3, 7, 20 |
| Can be followed | 16, 13, 1 | 19, 10, 1 |

S + N + T sums to 10.2 for Stitchwort, 10.4 for Lean and 10.3 for Rocq: level.

### What the scores show

- **Noise is where we lose, and the long proofs are where it is lost.** Four of the nine long
  proofs score 1: `runsBlockOneLine` (23 lines that are one lemma applied, its arguments one a
  line), `headerResult1` (36 lines of nested `match` to reach one field), `exprBlanks` (the same
  arm about forty times) and `blankItemHangs` (five arms that differ in one argument, each
  spread over a dozen lines). In short proofs the gap is 3.8 against 4.4: small.
- **Following the proof is where we win.** Our case splits name each case; our `let`s name each
  intermediate fact with its type (`settledHomed`, `plainOfShapes`); `rewrite` names what it
  rewrites with. The ports' `simp_all [...]` and `intuition; solve [... | eauto]` hide the route.
  `argumentMinusDeaf`, `statementsWalk`, `refinesAppend` and `walkAttributesAlike` are
  short in all three and plainer in ours.
- **Where a port is quiet and still followable**, it shows what we could be: `settledHomed` in
  Lean reads like ours at half the length; `homeStands` in Lean keeps our case comments ("the
  comma holds the owed comment: it walks back to its word") over `simp` steps. The Lean
  `followsParenAtom` (8 lines, each bind visible) is easier to follow than our one-line
  `byWalking` with four hints, which is why ours scores N 5 but T 3.
- **Statements are level because they are the same.** The three or four where a port is ahead
  are the ones where an encoding of ours shows: `(outside <= marked) = True` in `closerFitsOf`,
  and the `() =>` thunks and `Parse.` prefixes of `readsAtAtValue` and `runsWalkHere`. Rocq is
  behind once, on `firstThreeKeepMeaning`, where our `file.withForall.withoutTrailingCommas...`
  chain reads in order and Rocq's nested calls read inside out. The Rocq ports also rename
  binders to single letters where a field has the name (`e`, `a`, `k`, `w` in `blankItemHangs`
  and `notedCloserHangs`), which I did not mark down but a reader would feel.
- **Doc is 4.0 on long proofs and 2.0 on short ones.** Where D3657's proof idea is present it
  is good (`unaryHung`, `homeStands`, `blankItemHangs`, `wordsCalmKeep` all 5). The sample
  flatters us here: six of its nine long proofs have an idea, against 282 of 838 in the slice
  **[measured]**.

### Where a port reads better only because its definitions are cut down

- **walk and readback** (`readsAtAtValue`, `runsBlockOneLine`, `runsWalkHere`, and part of
  `readsBlockResult`): the ports' parser is a plain state monad with no `Honest` offsets, so
  `inversion ran` or one `simp` sees through it, and the statements lose their thunks. Ours
  threads marks and offsets through std's lemmas. `runsBlockOneLine`'s N 4 against our 1 is
  about half this and half our layout.
- **`closerFitsOf`**: `Carry` without `floor`. Small.
- **`itemsShapesOfKinds1`** and the tree theorems: `Expr` is opaque or has fewer constructors,
  which makes `cases <;> simp_all` cheaper than it would be on ours. It doesn't change how the
  port reads, only how much it would cost at full size.

Setting those four walk and readback theorems aside, noise is 3.3 for Stitchwort against 4.2
for Lean and 4.0 for Rocq: the gap stands.

## 3. Reading as a newcomer

### The top: `Fmt/TopStatements.sw` and `Fmt/Accepts1.sw`

**What works.** The file header of `TopStatements.sw` says what slice 1 covers in one sentence
a user would recognise ("files of `def name: Type := value` with no parameters, ..."). The four
statements can be read cold:

- `formatIdempotent1`: one hypothesis, one conclusion, no private word.
- `formatAccepts1`: the same, and its file header says why the statement is fixed.
- `formatKeepsProgram1`: needs `parse1`, `tidy1`, `calmTop` and `meaning`; the description
  explains `calmTop` and says what the slice excludes.
- `slice1Formats`: eight conjuncts, but the description walks through them and says what "the
  language's own" and "the same program" mean.

Each has a proof idea that names the lemmas, and the proofs are 15 to 25 lines. I would put
these four beside any Lean or Rocq development's top theorems.

**Where I got lost.**

1. **Finding them.** The top theorems start at line 364 of 594, after 300 lines of helpers
   whose descriptions are in the project's shorthand: "P2 is the identity ...", "the stock
   take's row 10", "the stock take's U6". The file has 33 imports, 13
   of them `(..)`, so a name's home can't be read off the top of the file.
2. **One step down.** `formatsOf`, `tidiedFacts`, `printedOf` are fine. Then `declHangs1`:
   five hypotheses `within`, `shaped`, `settled`, `lexical`, `unreturned`, each `= True`, giving
   `hangs decl.leaves = True ∧ (... → decl.stands = True)`. Its description: "A declaration of
   the tree the driver prints hangs as the rules lay it out, over one line or several, and
   stands." I can't tell what *hangs* or *stands* claim without leaving the file, and nothing
   says where to go.
3. **"Rule N" and P1 to P4.** Used in the top theorems' own proof ideas and 102 times across
   the slice. Rule N turns out to be the pass that moves comments to the token they belong to
   (`Syntax/Settle.sw`), and P1 to P4 the four tidy passes; the top file says neither.
4. **The proofs' small change.** `(Bool.falseNotTrue (Bool.andRight inGrammar)).impossible`,
   `Bool.andIntro alphabet plain`: a reader sees the encoding of "the test passed" before the
   argument. In `formatAccepts1` five of the proof's fifteen lines are this. (I am not
   proposing to touch these proofs or statements: D3688.)

### Three proof files drawn at random

Seed 4548, `random.sample` over the 137 files under `tools/fmt/src` that hold a theorem, `Tests/`
and `MustAccept*` left out **[measured]**: `Syntax/ReadBackHungFrameLemmas.sw` (293 lines),
`Fmt/EdgeHangProofs.sw` (104), `Fmt/OutputStatements.sw` (357). I read the second in full and
the first 120 lines of the other two, plus the third's outline.

**`Fmt/EdgeHangProofs.sw`.** Short lemmas, short proofs, about half with a description. Lost at:

- The header: "Trailing-comment facts of a slice 1 expression's tokens (SW-4099)", then a
  section "What an edge-quiet expression trails". *Edge-quiet* is not defined in the file.
- `codedLex`: the description says "A slice 1 expression read back has a token that is no
  closer: its first"; the statement says `Coded expr.words.reverse = True`. The link between
  the two is the definition of `Coded`, in another file, behind `import Fmt.TrailsProofs
  (Coded, ...)`.
- Restated terms: `rewrite List.reverseAppend left.words [operator, ..right.words],
  List.reverseCons operator right.words, List.appendAssoc ...` (`infixTrails`,
  `edgeCloseBefore`). Each list lemma is written with its arguments, so the term being
  rewritten appears three times. Followable, and noisy.
- `lastWithin` and `lastLexical` are the same six lines twice, once for each test; neither has
  a description. A fact about `List.all` and "the last of a non-empty list" would say it once.
- `trailsSwap`: nine binders to carry a fact across an equation. A reader wonders what it is
  for; the description ("An element's facts, its trailing comment named by an equation") doesn't
  say.

**`Syntax/ReadBackHungFrameLemmas.sw`.** The clearest of the three: each step lemma says in
words what a kind of token does to the state ("A closer ends the bracket: the state is the one
outside it"), and the proofs are one or two lines. Lost at:

- The header cites "SW-4142, H3 of SW-4121's plan" and `speltHangs`: a ticket, a plan's label
  and a theorem in another file, and no sentence on what "the line rule" is.
- The five-part test `(kind == Comma || kind.isCloser || kind == ColonEq || kind == Colon ||
  kind.isOpener) = False` is written out in five statements in the first sixty lines. The
  descriptions call it "no bracket, comma, `:=` or `:`", and the theorems' names call it
  *flat*; a reader has to match the three by eye.
- `signIsFlat`, `infixIsFlat`, `wordIsNoArrow`, `flatParts`, `openerParts`, `leavesOfAppend`:
  no description. Each is obvious once the one above it is understood; a section comment would
  do.

**`Fmt/OutputStatements.sw`.** Mostly definitions, and the best prose of the three: each
definition says what it models and why (`operandSpacing`'s is a model of its kind). Lost at:

- **The header is out of date.** It says the file holds what is "stated and not yet proved" and
  that "each open goal is a proof ticket". I found no unproved statement in it **[read; a text
  scan]**: its nine theorems are examples closed by `byComputing`, and its comments say the
  real theorems "are proved in `Fmt.TokenProofs`" and `Fmt.SpacingProofs`. A newcomer reads the
  header and concludes slice 1 has holes.
- The file is named for statements and holds definitions and examples; `SourceFile.calmTop`,
  which the first top theorem's statement names, is defined here, at line 178.
- `Spelt`, `glued`, "rule N", `holdsOn` are used before or without being introduced.

### What the read adds up to

I was never lost *inside* a proof for long: the proofs are explicit. I was lost *between* them:
what a word means, where it is defined, which file comes before which, and whether a header is
still true. That is the same finding as the scores: names 2.7 and doc 2.6 are the low ones.

## 4. What stands between slice 1 and clean, ranked

Counts are over `tools/fmt/src` without `Tests/` and `MustAccept*`: 168 files, 105,963 lines,
5,422 theorems **[measured]**. Lane estimates are in agent time, from the counts and from past
lanes of the kind; none is from a sketch of a proof. Nothing here narrows a slice, changes a top
or acceptance theorem, or changes what any statement says (D3688); where a fix re-types a
statement it is one whose hash is unchanged or whose meaning is checked the same (D2436).

### With features Stitchwort has today

| # | What | Evidence | Cheapest fix | Size of the fix |
|---|---|---|---|---|
| 1 | **A private vocabulary with no key** | 365 definitions of a property (`def ...: Prop`), 111 with no description; the stems most used are *Alike* (45), *Follows* (37), *Kept* (18), and 14 distinct *Hang*/*Hung* properties (`HangsFor`, `HangsAt`, `HangLays`, `FullHungAt`, ...) **[measured]**. "Rule N" 102 times; 195 description lines use a code (P1 to P4, K1, U6, "stock take") and 111 cite a ticket **[measured]**. No glossary in `tools/fmt/NOTES.md` (2,115 lines, a stage diary). Names scored 2.7 **[scored]** | (a) A glossary: each private word, one sentence, where it is defined; and a proof map from the three top theorems down to the layers. (b) A description for each of the 111. (c) Codes in descriptions replaced by the words they stand for | (a) one Sonnet paper lane, 30 min; (b) 111 definitions, one lane, 30 min; (c) 195 lines plus 111, DeepSeek with the glossary as its brief, 30 min **[estimated]** |
| 2 | **Long proofs that don't say what they do** | 556 of 838 proofs over 15 lines have no proof idea, 15,784 lines of proof; the longest 100 hold 5,532 of those lines and the longest 200 hold 8,655 (55%) **[measured]**. 3,492 theorems have no description. In the sample, 12 of 30 have none and Doc is 2.0 on short proofs **[scored]** | Proof ideas for the longest 200, in the glossary's words (so after 1). For short lemmas, a section comment for each family, not a line each | 200 proofs at about 35 a lane: 6 Sonnet lanes of 40 min **[estimated]**; the other 356 only if the first 200 prove worth it |
| 3 | **Descriptions that are labels, or out of date** | In the sample: "A closer with own-line comments." (`notedCloserHangs`), "After a waiting comment, an item that may start there may start." (`heldItemSeat`), a parameter `prev` that the statement doesn't have (`plainOfShapes`). In the read: `OutputStatements.sw`'s header says its goals are open | Fix the header now (a one-line change). The rest falls out of 2 if its brief says "a claim, not a label; check it against the statement" | the header: minutes; otherwise no lane of its own |
| 4 | **Facts passed one at a time** | 697 theorems with eight or more binders by my scan (the stock take's stricter count: 634) **[measured]**; S is 2.8 on long proofs **[scored]**; in the sample `blankItemHangs` (13), `notedCloserHangs` (16), `unaryHung` (14), `homeStands` (12). The ports have the same interfaces, so this is not a gap with them; a native Lean proof would bundle | The stock take's step 1, unchanged: SW-4530's implicit values, then facts about one object in a named record | as the stock take: a 30 min pilot, then three lanes of about 35 min. Its saving was estimated from a sketch; I'd trust the pilot's figure, not that one |
| 5 | **`= True` and `Bool.and` bookkeeping** | 2,781 statement lines end a hypothesis `= True`; 2,790 lines name `Bool.andLeft`, `andRight` or `andIntro` **[measured]**. It is what a reader sees first in the top proofs | Drop `= True` where the hash is unchanged (the stock take's step 3), outside the top and acceptance theorems. The `Bool.and` chains have no cheap fix today: SW-4515's `byFacts` pilot closed 0.25% | one DeepSeek sweep by area, three runs of 30 min **[estimated]**; nothing for the chains |
| 6 | **Repeated tests and twin lemmas** | The five-part "flat" test written out five times in `ReadBackHungFrameLemmas.sw` **[read]**; `lastWithin`/`lastLexical` the same proof twice **[read]**. I counted only what I met in three files, so I can't size it across the slice | Name the test (a `def`, with the lemmas restated through it and checked to mean the same, D2436); a std lemma for the twins. File as small tickets when met; no sweep | minutes each |
| 7 | **Finding your way** | 815 of 1,462 imports are `(..)` **[measured]**; the top theorems begin at line 364 of their file; `calmTop` is defined in a file named for statements | The proof map in 1(a) covers most of it. I would not sweep the imports: explicit lists of forty names read no better | none beyond 1(a) |

In order: 1, then 2 (it needs 1's words), with 3's header fix at once; 4 and 5 are the stock
take's steps 1 and 3 and already ordered. About ten lane-halves of work for 1 to 3, none of it
proof work, none of it changing a hash but for 6.

What I can't promise: that 1 to 3 raise the scores by a stated amount. The nearest evidence is
inside the sample: the six theorems with a proof idea score Doc 4 or 5, and they are the long ones
a reader most needs. A cheap check is to redo this section's newcomer read of one file after 1
and 2 have reached it.

### Would need a tool or language change (not proposed)

| What | Evidence | Why not now |
|---|---|---|
| **Case-split automation** (one line for "split on `x`, each case closes the same way") | SW-4537: about 14% of slice 1's lines; here, the four proofs with N 1 include three of this kind (`headerResult1`, `exprBlanks`, and `blankItemHangs`' arms) | It is the largest single cause of noise, so the evidence for *something* is real. But the ports' version costs them a point of "can be followed" on average, and on `wordsCalmKeep` it drops to 1; and today's record is that savings predicted from sketches came in far lower (`byFacts` 0.25% against 4%). What exists should be measured first: SW-4521's `cases x then byComputing` sweep is after the draw, and `headerResult1` is still 36 lines at this `main` **[read]**, so either it hasn't reached it or it doesn't apply. That is worth one question to the SW-4521 lane before anything is designed |
| **The formatter's layout of long calls** (one argument a line once a call passes the width) | 7,457 proof lines hold a single short argument, 7% of the slice **[measured]**; `runsBlockOneLine`, `blankItemHangs`, `notedCloserHangs` | It is a formatting rule, so it changes both formatters and the slice 1 proof of this very tool, and it is Matt's (user-visible, D3677's freeze). SW-4537 found that over the whole slice lines and characters give the same ratio, so it moves reading, not size. Item 4 shrinks the calls themselves, which may remove most of the need |
| **Naming where a word comes from** (hover or go-to-definition in the reader's editor) | item 7 | Not checked here whether the LSP already does this for `(..)` imports; if it does, item 7 is an editor matter and not the text's |

## 5. Limits

- One rater, one pass, and a rater who knows the code: a real newcomer would likely score names
  and docs lower than I did and might score "can be followed" lower for Stitchwort's own syntax.
- 30 theorems, drawn for line counts and weighted to long ones. The means are not estimates for
  the slice; the direction of each comparison (20 of 30, 16 of 30) is the finding.
- The ports were written to be short and counted, by a model, with no descriptions. A Lean or
  Rocq author writing to be read would comment `simp_all` steps or structure them; so "can be
  followed 3.0" is these ports, not the systems' best.
- The scans are text scans: "has a proof idea" means the description contains "Proof idea" or
  "By induction"; binders are counted by a pattern, which over-counts against the stock take's
  figure by about 10%.
