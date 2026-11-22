# SW-4559: repeated proof shapes in tools/fmt that one lemma could state once

**Status:** Opus lane SW-4559, 21 to 22 November 2026, against `main` at `ea665e267`. Survey by
script over `tools/fmt/src` (Tests/ and MustAccept* left out; ReadBackRuns* and ReadBackHung*
surveyed, but planned elsewhere, so not piloted), two pilots checked and committed.

Marks: **[measured]** counted or checked today; **[estimated]** my judgement from the shape.
Proof lines are by `docs/reviews/SW-4519/count.py` (body lines after `:=`; `def`s and `type`s
not counted, so record instances are counted by hand below).

## In plain words

**The question.** SW-4553 and SW-4556 cut hundreds of lines by stating "traversing a node
rebuilds it from its children" once, as a lemma. Are there more families like that, where many
theorems are proved by the same steps over different constructors, functions or properties?

**What I found.**

1. **Families of identical proofs are used up.** Clustering proof bodies by their text (names
   and numbers blanked) or by their skeleton (local lemmas, recursive calls and arguments
   blanked) finds only small groups: the largest is 41 three-line list inductions (124 lines),
   and everything with three or more members totals about 530 lines [measured]. This matches
   SW-4519's 428 lines, and SW-4556 has already taken the traversal families (`…Ok`,
   `…Twice`, `…Blanks`).
2. **The big family is a matrix: printer function × property.** The printer's rules
   (`bodyAfter`, `appFrom`, `bracketContent`, `cells`, `linkDocs`, …) each have one theorem per
   property of their documents: `…Spells`, `…Shape`, `…Passes`, `…Steps`, `…Hangs`,
   `…Finishes`, `…Keys`, `…Tell`, `…Kept`. Matching theorem names to the 188 rules in
   `Fmt/Rules.sw` gives 34 rules with three or more such theorems, 4,348 proof lines
   [measured]. For the same rule, the `Spells` and `Shape` proofs are the same proof, step for
   step, with `spellsNest` for `isNest` and so on [read: `bodyAfterSpells`/`bodyAfterShape`,
   `appFromSpells`/`appFromShape`].
3. **Pilot 1 states it once and works.** A record `DocHolds r` (what a property must keep
   through the printer's combinators) and one theorem `bodyAfterHolds` for any such property;
   `bodyAfterSpells` and `bodyAfterShape` become instantiations. **81 proof lines become 46,
   and 14 more lines of instances that the next rules reuse**; the two members' steps fall to
   2 and 5% of before, and the shared lemma costs about what one member did [measured].
4. **Pilot 2, a small family in the parser's comment-blindness proofs (`…Deaf`), did not take
   a lemma**: a lemma about "the `match skipGroup …` a scan does" can't be stated, because each
   definition's inline `match` is its own term and the lemma's never unifies with it. An
   or-pattern arm whose proof is generic over the bracket kind did the job instead: **131 lines
   to 95** [measured].
5. **Not piloted (time; machine at load 31):** the matrix's second half (properties indexed
   by seams: `Passes`, `Steps`, `Hangs`), which needs a second record, and `appFrom`, whose
   properties concatenate differently-indexed parts and need the index in the record.

**What it should do.** Rolling `DocHolds` out over the rules where two or more fixed-index
properties are proved should take about **450 lines** net [estimated, from pilot 1's ratio];
a seam-indexed twin perhaps **300** more [estimated, untested]. Both make the members read as
"this rule has this property because its parts do", which they now say in 30 to 80 lines each.

## 1. Method

Scripts in the lane's scratchpad (not committed; they are one-off scans):

- `cluster.py`: proof bodies with local names, constructors and numbers blanked, qualified lemma
  names kept; groups of 3+ identical bodies.
- `skel.py`: coarser, with the theorem's own name as `REC`, any theorem name as `L`, runs of
  arguments collapsed; groups by skeleton.
- `jac.py`: greedy clusters of theorems whose sets of called lemmas overlap by Jaccard ≥ 0.5.
- Name stems and suffixes: theorems grouped by the rule they name (`appFrom…`) and by the
  property (`…Spells`), then the matrix by matching stems against `def` names in `Fmt/Rules.sw`.

5,552 theorems, 48,240 proof lines in all [measured]; the survey's scope (no Tests/, no
MustAccept*) is the same set less 125 one-liners.

## 2. The families, ranked by lines at stake

| # | Family | Members, proof lines | Candidate lemma | After (how known) | Saved | Readability |
|---|---|---|---|---|---|---|
| 1 | Printer rule × fixed-index property (`Spells`, `Shape`/`Is`, `Finishes`, `Keys`, `Tell`) | ~1,450 lines of the matrix's 4,348; rules with 2+ such properties | `DocHolds r` + one `<rule>Holds` per rule (pilot 1) | pilot: pair 81 → 46 (0.57), plus 8 lines of instance per property once | **~450** net [estimated from pilot] | Better: the member says which facts feed the rule; the rule's structure is proved once, with its proof idea |
| 2 | Printer rule × seam-indexed property (`Passes`, `Steps`, `Hangs`) | ~1,230 lines | `DocSeams r` with `r: Doc → pre → post → Prop`; `spaced`/`hardBefore` move the seam | not piloted; `appFromSteps`/`appFromPasses` read alike but thread different seam facts | **~300** [estimated, untested; read as 2x optimistic] | Better if it fits; `Hangs` has many more parameters and may not |
| 3 | `ReadBackRuns` peek-then-bind chains (`runsLook`, `runsPeekOn`, `Parse.runsBind`) | 7+4+4+4+6 theorems in 5 clusters, ~840 lines | a "peek, then run the branch" bind lemma | not piloted (planned elsewhere) | unknown | – |
| 4 | List twins of tree functions (`allWithin1`, `calmAll`, `allShaped`, `itemsWords`): list induction with `andLeft`/`andRight` | 138 theorems, 1,983 lines [measured] | none today: the twins are hand-recursive, so std's `List.all`/`List.map` lemmas don't apply | – | 0 now; most of it if the twins could be `List.all`/`List.map` (finding) | – |
| 5 | Parser `…Deaf` scans: the three bracket arms of a scan that skips a group | 4 theorems, 131 lines | no lemma possible (inline `match` identity); or-pattern arm generic over the bracket | pilot: 131 → 95 (0.73) | **36** (done) | Better: one arm says "skip a group, carry on" instead of three copies |
| 6 | Three-line list congruences (`rewrite pointwise, IH`) | 41 theorems, 124 lines | none: each is over its own recursive function | – | 0 | already minimal |
| 7 | Small identical-body groups (case tables in `CalmProofs`, `ExprHangProofs`; `Fail.toResultAlikeN` list arms) | ~400 lines | `cases … then` or or-patterns (SW-4547 territory) | – | ~1% | – |

## 3. Pilot 1: `DocHolds` for the printer × property matrix

**Shape.** A rule builds a document from its parts with the printer's combinators; a property
is kept by each combinator; so the rule's document has the property when its parts do. Each
property re-proves this for each rule, step for step.

**Lemma** (in `Fmt/SpellProofs.sw`, beside `bodyAfterSpells`):

```
type DocHolds (r: Doc → Prop) = {
  nest: ∀ (indent: Nat) (doc: Doc) => r doc → r (Nest indent doc),
  flatten: ∀ (doc: Doc) => r doc → r (Flatten doc),
  oneLineBelow: ∀ (doc: Doc) => r doc → r (OneLineBelow doc),
  spaced: ∀ (doc: Doc) => r doc → r (Doc.concat [Doc.text " ", doc]),
  hardBefore: ∀ (doc: Doc) => r doc → r (Doc.concat [HardLine, doc]),
  choice: ∀ (first: Doc) (more: List Doc) => List.All r [first, ..more] → r (Choice [first, ..more])
}

theorem bodyAfterHolds ∀ [r: Doc → Prop] (holds: DocHolds r) (value: Expr) (assign: Word) (around: Around) (semi: Bool)
    (within: value.within1 = True)
    (doc: r (value.el around))
    (hug: value.noted = False → ∀ (open: Doc) => value.callHug { around | hoisted = True } = Some open → r open):
    r (bodyAfter value assign around semi).fst ∧ r (bodyAfter value assign around semi).snd
```

Instances `spellsHolds texts` (SpellProofs) and `isHolds shape` (ToldDeclProofs) are `def`s
(a `type` record isn't a proposition, so a `theorem` is refused with E-NOT-A-PROP), each 8
lines, with a 3-line converter from `List.All` to the property's own list form
(`spellsEachOf`, `allIsOf`). Statements of `bodyAfterSpells` and `bodyAfterShape` unchanged.

**Measured** (`check --no-cache --timings=all --only …`):

| Theorem | Lines before | After | Steps before | After |
|---|---:|---:|---:|---:|
| `bodyAfterSpells` | 36 | 4 | 625,955 | 11,380 |
| `bodyAfterShape` | 45 | 6 | 408,601 | 18,791 |
| `bodyAfterHolds` (new, once) | | 30 | | 639,942 |
| `spellsEachOf`, `allIsOf` (new) | | 3 + 3 | | 2,087 + 2,053 |
| `spellsHolds`, `isHolds`, `DocHolds` (defs, not counted by the script) | | 8 + 8 + 8 | | 15,969 + 19,641 + 3,455 |
| Total | 81 | 46 proof (+24 def) | 1,034,556 | 713,318 |

No theorem over 3x; the SpellProofs rows the pilot touched are 1.07x (625,955 → 672,833) and
ToldDeclProofs' 0.09x, so both files are within 1.5x. Net of the one-time defs the pair is
81 → 70; each further rule pays only its `<rule>Holds` and two short members, and the record's
fields grow by one line per new combinator (plus one line per instance).

**Prediction for the rollout.** The generic proof was 30 lines against members of 36 and 45:
about the longer member's 0.67. For a rule with k fitting properties of total L and longest M,
after ≈ 0.67 M + 5 k. Over the rules with two or more of `Spells`, `Shape`, `Finishes`, `Keys`,
`Tell` (about 1,200 of the 1,450 lines), that saves about half, ~550, less ~100 for record
fields and instances: **~450** [estimated]. Caveat from today's evidence (tool predictions ran
3-10x high): `bodyAfter` uses only same-index combinators. Rules that concatenate parts with
different indices (`appFrom`: head ++ front ++ last texts) need the index in the record
(`r: Doc → List t → Prop` with `concat` over a list relation), which is untested; `Finishes`
only looks at a document's end, so it may need its own `concat` field. The next pilot should
be `appFrom` (Spells 75, Shape 83, Finishes 29, Keys 60).

## 4. Pilot 2: the bracket arms of the `…Deaf` scans

**Shape.** A scan over items (`resultArrowAhead`, `lambdaAheadFrom`, `annotatedFrom`,
`lambdaResultType`) skips a bracketed group on `(`, `{` or `[` and carries on after it; the proof
that it reads no comments had three identical five-line arms, one per bracket.

**Lemma tried, and why it fails.** `skippedDeaf` stated "a continuation after `match skipGroup
open rest with | Some after => later after | None => False` is deaf if `later` is". It checks,
but no use of it does: each definition's inline `match` (and `afterGroup`'s) is its own term,
and the lemma's `match` is another, so `E-TYPE-MISMATCH` at every use. A lemma about an inline
match can only be stated about a named helper that the definitions call.

**What worked.** One or-pattern arm, generic over the bracket because it names `item.kind`
rather than the token:

```
| LParen | LBrace | LBracket =>
  rewrite skipGroupDeaf [item.kind] rest then
    match skipGroup [item.kind] rest with
      | Some after => resultArrowAheadDeaf modes more after
      | None => byComputing
```

| Theorem | Lines before | After | Steps before | After |
|---|---:|---:|---:|---:|
| `resultArrowAheadDeaf` | 31 | 21 | 199,556 | 255,509 (1.28x) |
| `lambdaAheadFromDeaf` | 42 | 33 | 218,271 | 246,893 (1.13x) |
| `annotatedFromDeaf` | 28 | 18 | 340,930 | 390,313 (1.14x) |
| `lambdaResultTypeDeaf` | 30 | 23 | 949,667 | 984,779 (1.04x) |
| File (proof lines) | 717 | 685 | | |

## 5. Findings

- **Rule × property matrix:** the next lanes are `DocHolds` rolled over the fixed-index
  properties (start with `appFrom`, which needs the index in the record), then a seam-indexed
  twin for `Passes` and `Steps`. `DocHolds`, `bodyAfterHolds` and the instances belong in their
  own namespace (`Fmt.DocHolds`, importing CalmProofs' `matchedNone` and friends) once there
  are more rules; the pilot put them in SpellProofs because ToldDeclProofs imports it.
- **List twins of tree functions** (`allWithin1`, `calmAll`, `allShaped`, `itemsWords`, …): 138
  theorems, 1,983 lines, re-prove list induction because the twins are hand-written. If nested
  recursion through `items.all Expr.within1` / `items.map (.calm item)` is (or could be)
  accepted in the definitions, std's `List.all`/`List.map` lemmas would close most of them.
  That is a program change, not a proof change, so it is a design question.
- **A lemma can't name a definition's inline `match`.** Where the same branching appears in
  several definitions (`match skipGroup [] items with …`), a shared named helper (as
  `afterGroup` is for one of them) would let one lemma cover all of them.
- **`type` records can't be theorems** (E-NOT-A-PROP): instances of a proof record are `def`s,
  which `count.py` and the stock-take scripts don't count. Worth a line in the proving guide
  next to the `Blanks`/`Keeps` records.
