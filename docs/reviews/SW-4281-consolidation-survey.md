# SW-4281: the next consolidation targets in the slice 1 formatter proof

Fable paper lane, 19 Nov 2026, on `main` at `edce3d149` (after SW-4270 and
SW-4277). Read-only: counts come from scripts over `tools/fmt/src`, and
three claims were checked with single-file probes against the release
binary. Nothing was built and no suite was run.

Every figure is marked **[measured]** (a script counted it),
**[probed]** (a scratch file checked) or **[estimated]**.

## In plain words

**The problem.** After today's sweeps the proof is 114,700 lines in 180
files: 5,418 theorems (77,000 lines, 54,800 of them proof text) and 3,108
definitions. The remaining bulk is not dead code or duplicates. It is
arguments written out by hand that the checker can work out, and the same
few hypotheses repeated on hundreds of statements.

**The change.** Ten targets, ranked below. The first five are the ones
with real value: they remove an estimated 2,300 to 3,300 lines and about
870 `_` placeholders, and make the longest statements and proofs
shorter to read. None changes a top theorem or what the tool accepts.

**What it should do.** `exprOk`, the second-longest proof, goes from 327
lines to about 130 [estimated from a measured count]. The 92 parser
"two runs agree" lemmas that each list 3 to 15 assumptions list one or two.
The 17 theorems named `…A` to `…D` disappear. There are fewer targets of
real size than the 6 to 12 asked for: five solid ones, two for the edit
loop, three small.

## Ranked table

| # | Target | Where | Saving | Risk | Model | Est. |
|---|---|---|---|---|---|---|
| 1 | Printer lemma families read their arguments off the premises (as SW-4230 did for `passes…`) | `hangs…` (48 lemmas, 409 uses), `steps…`, `spells…`, `is…`/`refines…`, `lays…`; 15 files under `Fmt/` | 700 to 1,200 lines [estimated]; 329 argument-only lines and about 2,650 inline arguments [measured] | Low: internal lemmas, precedent today | Sonnet | 2 lanes, 30 to 40 min each |
| 2 | `Fail.toResultSeqN` and `…Then` infer their computations and values | std `Fail/Walk.sw`; 121 uses in `Fmt/Walk.sw` (111) and `Fmt/ReadBackFile.sw` (10) | 424 lines, up to 594 [measured count; inference probed on a toy] | Low: std signatures, one user | Sonnet | 30 min |
| 3 | The two-run walk's assumptions as tiered records, like the shape walk's `Outside…` | `Syntax/Follows{Ladder,Forms,Statements,Decl}.sw`: 92 theorems carry 3 to 15 `…Follows self selfTwin` hypotheses (612 hypothesis lines) | about 500 statement lines [estimated from measured counts], plus the argument runs at about 140 call sites | Medium: restates internal lemmas (same meaning); orchestrator checks statements | Sonnet (Opus if the tiers don't fall out) | 45 to 60 min |
| 4 | One list of slice 1's operators; each per-operator fact by `List.allMember` | 21 staircase theorems, 335 lines, in `ExprHangProofs`, `OutputFileProofs`, `SpeltSlots`, `TreeJoinProofs`, `WordsEdge` | about 250 lines [estimated]; all 17 `…A/B/C/D` names go | Low [probed] | Sonnet | 25 to 30 min |
| 5 | std `Parse` lemmas whose explicit arguments are nearly always `_` | `Parse.readsFatal` (103 of 105 uses), `followsDone` (126 of 225), `readsDone` (47 of 48), `readsAtDone` (54 of 70), `List.consInjectiveHead` (25 of 35); fmt's `followsFatalAny`, `givesFail` | about 870 `_` gone [measured]; few lines | Low, but std signatures used by about 12 AoC days too | Sonnet | 30 min |
| 6 | Split the two largest namespaces by their section comments | `Syntax/FollowsForms.sw` (4,375 lines, 281 theorems, 37 sections), `Syntax/FollowsDecl.sw` (4,152, 281, 29) | Edit loop: SW-4216 measured 13 s to 5 s for the same move | Low: pure move; clashes with target 3, so run it after | DeepSeek | 25 min each |
| 7 | Later slices out of the root namespace `Fmt` | `Fmt/Slice4a.sw` to `Slice6a.sw` and what only they use: 679 of the root's 3,067 declaration lines are unreachable from the slice 1 proofs [measured] | An edit to a later slice stops rechecking all 146 dependent files (5:18 measured in the proving guide) | Low: a move plus imports in `Twin.sw` and tests | DeepSeek | 20 min |
| 8 | A record for the hung-line hypotheses | 13 theorems in 6 `Syntax/ReadBackHung*.sw` files repeat `lineRead`, `lineRest`, `openFirst`, `bound`, `hung`, `deepItems` | about 65 statement lines and 5 arguments at each of the calls (one call passes 17 arguments) [estimated] | Medium: restates internal lemmas | Sonnet | 30 to 40 min |
| 9 | Comments and names left from the process | 59 "lane N" mentions and 158 `SW-…` references in 98 files; 4 files whose namespace is not their file name (`LexProofs.sw` is `Syntax.Proofs`; three files share `Fmt.Proofs`) | Readability; the namespace rename removes a trap the proving guide has to warn about | Low: comments and a rename | DeepSeek | 20 to 30 min |
| 10 | Small std and tidy items, one lane | the lexer's own `Gives` family; about 10 general facts; the `…Blank` list lemmas | about 150 lines [estimated] | Low | DeepSeek or Sonnet | 25 min |

Order to run: 1 and 2 at once (different files), then 4 and 5, then 3,
then 6. Targets 7 to 10 fill slots.

## What was measured

- 180 files, 114,702 lines. 5,418 theorems (77,042 lines: 22,272 of
  statement, 54,770 of proof), 3,108 definitions (14,288 lines), 493 tests.
- Proof lines by proof length: 1 line 1,016; 2 to 5 lines 5,922; 6 to 15
  lines 13,864; 16 to 40 lines 16,761; 41 to 100 lines 11,517; over 100
  lines 5,690 (36 proofs).
- The longest proofs: `atomHung` 415, `exprOk` 327, `declOk` 302,
  `homeStands` 258, `speltSlots` 248, `bitsHeard` 226,
  `bracketContentHangs` 198, `exprRuns` 185, `elShape` 175,
  `followsDefinitionParts` 159.
- The longest statements: `defDocHangs` 41 lines, `alikeHeader` 38,
  `runsItemsFrom` 34, `bracketContentHangs` 33, `commaBracketHangs` 33.
- `_` written as a call argument: 2,305 at 1,129 call sites. By where the
  lemma is defined: std `Parse` 697, `Fmt/TouchSteps.sw` 491, std `Bool`
  198, `Fmt/SpellProofs.sw` 161, std `List` 154, `Fmt/ToldDeclProofs.sw`
  148.
- Explicit arguments a later premise names (so the checker could read
  them off it), times the lemma's call sites: 20,338 across the project.
  This is an upper bound, since naming is not always enough to infer. Top
  files: `HangProofs` 2,224, `TouchSteps` 1,110, `Walk` 696.
- Spelled arguments (`[p := …]`) still present: 392, the ones today's
  script kept as needed.
- Proofs equal up to renaming: 115 groups, 253 theorems, 1,346 lines
  beyond one copy each. Almost all are the same shape over different
  types, not copies (see "Looked at and not recommended").

Scripts: `measure.py`, `m2.py`, `m3.py`, `m4.py` in the scratch folder;
probes `probe2.sw` and `probe4.sw`.

## 1. Printer lemma families infer their arguments

**What.** SW-4230 and SW-4275 made the `passes…` lemmas read `kinds`, the
documents and the edge predicates off their premises, and `JoinProofs.sw`
lost 662 lines for 19 lemmas. The sibling families were not done. Today:

```
theorem hangsCons ∀ (kinds: Text → Tok) (doc: Doc) (docs: List Doc) (indent: Nat) (pre middle post: Place → Hang → Prop)
    (first: HangLays kinds doc indent pre middle)
    (rest: HangLaysAll kinds docs indent middle post):
```

against `passesCons ∀ [kinds: Text → Tok] [doc: Doc] [docs: List Doc] [pre middle post: Edge → Prop]`.
Seven of `hangsCons`'s nine arguments are named by its premises, and it
has 62 uses.

**Where [measured].** Lemmas with at least three such arguments:

| Family | Defined in | Lemmas | Uses | Argument-only lines | Inline arguments |
|---|---|---|---|---|---|
| `hangs…`, `allHangs…`, `framed…` | `Fmt/HangProofs.sw`, `MarkProofs.sw` | 48 | 409 | 258 | about 1,070 |
| `steps…`, `stay`, `linkSteps`, `allTo`, `allSpacing` | `Fmt/TouchSteps.sw`, `TouchSeq.sw` | 30 | about 440 | 15 | about 1,150 |
| `spells…` | `Fmt/SpellProofs.sw` | 8 | 90 | 23 | about 110 |
| `isCons`, `isConcat`, `refinesAppend` … | `Fmt/ToldDeclProofs.sw` | 9 | 74 | 15 | about 160 |
| `lays…` | `Fmt/LaysKinds.sw` | 3 | 34 | 18 | about 165 |

The `steps…` count is by name prefix and takes in a few unrelated
`steps…` lemmas in `Syntax/`; the lane should go by the definitions in
`TouchSteps.sw` and `TouchSeq.sw`. `stepsTo`, `stepsFrom`, `stepsConcat`
and `stepsSpacing` are called with five `_` each today (352 `_` in all).

**The change.** For each lemma, make the arguments its premises determine
implicit, delete them at every use, and reformat. Keep explicit any whose
premise is a bare lambda (SW-4230 kept `passesNil` for that reason).

**Saving.** 329 lines hold nothing but such an argument and go outright.
The rest are inline; removing them lets the formatter rejoin lines, which
is where most of SW-4230's 662 came from. 700 to 1,200 lines [estimated].

**Risk.** Low. No statement changes meaning. A lemma whose arguments do
not infer stays as it is.

**Lanes.** (a) the `hangs…` family: `HangProofs`, `BracketHangProofs`,
`DeclHangProofs`, `AppHangProofs`, `ChainHangProofs`, `ElementsParen`,
`MarkProofs`. (b) `steps…`, `spells…`, `is…`, `lays…`. Sonnet, 30 to 40
min each. They share no definitions, so they can run together.

**A tool worth considering.** `dev/spellings.py` deletes a spelled
argument and keeps the deletion if the file still checks. The same loop
over "make this binder implicit and drop it at each use" would let
DeepSeek do the remaining families (`runsSame`, `speltHung`, `leadHung`,
`deafItem`, `alikeGroup` and others in the 20,338 figure). I would build
it only if lanes (a) and (b) show the hand method is the slow part.

## 2. `Fail.toResultSeqN` infers its computations and values

**What.** `exprOk` (327 lines), `declOk` (302) and the other `…Ok`
traversal proofs in `Fmt/Walk.sw` have one arm per tree constructor, and
each arm spells out every argument of a std lemma:

```
| Paren open inner close =>
  rewrite Fail.toResultSeq1Then
        (() => inner.traverse on)
        (v1 => Paren open v1 close)
        on.expr
        (inner.walk p)
        (exprOk on p agree inner),
      agree.expr (Paren open (inner.walk p) close)
```

The computation and its value are both in the premise's type
(`Fail.toResult t1 = Ok v1`).

**Where [measured].** 121 uses: 50 of `Seq1`, 47 of `Seq2`, 13 of `Seq3`,
11 of `Seq4`; 60 of them the `…Then` forms. Defined in
`crates/elab/src/std/Fail/Walk.sw`; nothing outside `tools/fmt` uses them.

**The change.** In std, make each `tN` and `vN` implicit. Try `g` and `k`
implicit too. Then each arm above is
`rewrite Fail.toResultSeq1Then (exprOk on p agree inner), agree.expr (…)`.

**Probe [probed].** `probe2.sw` wraps `Fail.toResultSeq1` and
`Seq1Then` with `t1`, `v1`, `g` and `k` all implicit. Both
`seq1B h` as a term and `rewrite seq1ThenC h, after` check. The probe has
one child and a pair as the built value; the real arms have up to four
children and may need `g` kept explicit where two children have the same
type.

**Saving.** 424 lines from the computations and values alone; 594 if `g`
and `k` infer everywhere [measured counts of the lines those arguments
occupy].

**Risk.** Low. Std signatures change (hash snapshots follow), with one
user.

**Lane.** Sonnet, 30 min. Check `Fmt.Walk` and `Fmt.ReadBackFile`.

## 3. The two-run walk's assumptions as tiered records

**What.** The lemmas that say the parser reads two sources alike take the
facts they assume about other parser functions one hypothesis each:

```
theorem followsMatchedPiped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (atoms: AtomFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (matches: MatchFollows self selfTwin)
    (clauses: ClauseLambdaFollows self selfTwin)
    (lambdaFacts: LambdaFollows self selfTwin)
    …
```

and pass them on in the same order
(`followsPipeChain knot atoms braces matches clauses lambdaFacts …`). The
shape walk over the same parser already solved this with tiered records:
`OutsideAtoms`, then `OutsideBraced { below: OutsideAtoms self, … }`, up
to `Outside` (`Syntax/ParseWalk.sw`, lines 214 to 280), each lemma taking
the lowest tier it needs.

**Where [measured].** In the `Syntax/Follows*.sw` files (16,768 lines),
904 hypothesis lines have the form `(name: XFollows self selfTwin)`, over
24 such `XFollows` definitions. 92 theorems carry three or more (612
lines); 39 carry nine or more. The runs nest as a ladder: `knot atoms
braces` appears in 58 statements, extended by `matches clauses` in 53, by
`lambdaFacts` in 41, by `ifs` in 25. The call sites pass `knot atoms
braces` together 73 times and `atoms braces matches clauses` 66 times.

**The change.** Define tier records over `self selfTwin` that follow that
ladder, restate the 92 lemmas over the lowest tier each needs, and build
the top record once where the facts are proved (the closing sections
"the facts that other lanes assume of this file's functions").

**Saving.** About 500 statement lines (612 less one or two per theorem)
and the argument runs at about 140 call sites [estimated from the
measured counts].

**Risk.** Medium. Internal lemmas are restated; each keeps its meaning
because a record of the same propositions is the same assumption. No top
theorem mentions these. The orchestrator checks the restatements
statement by statement (D2436).

**Lane.** Sonnet, 45 to 60 min, with the ParseWalk tiers named in the
brief as the model. Rerun on Opus if the hypotheses do not fall into
tiers. Run before target 6, which moves the same files.

**A larger version, not sized.** The file headers say several of these
hypotheses exist because separate lanes proved the files in parallel
("Lane 4's facts about this lane's functions"). Where the dependency is
not circular, the hypothesis could be replaced by the lemma itself. That
needs the call graph worked out, so it is an Opus design question; the
records are worth having either way.

## 4. One list of operators in place of the literal staircases

**What.** `operatorText1` in `Fmt/Slice1.sw` tests a text against 22
literals in four functions (`operatorTextA1` to `D1`). Each fact about
those operators is then proved by four theorems that repeat the test as a
staircase of `match a0: text == "->" with | True => … | False =>`:
`opKindA`…`D`, `operatorA`…`D`, `binaryFactsA`…`D`,
`operatorSpellsA`…`D`, each family with a fifth theorem to join them.

**Where [measured].** 21 theorems with three or more staircase steps,
335 lines, 131 steps: `Fmt/TreeJoinProofs.sw` 32 steps, `SpeltSlots.sw`
28, `ExprHangProofs.sw` 25, `OutputFileProofs.sw` 22, `WordsEdge.sw` 7.
These are all 17 of the project's letter-suffixed names.

**The change.** Leave `operatorText1` alone (it is part of the slice's
grammar). Add `def operators1: List Text` and one bridge theorem,
`operatorText1 text = True → operators1.contains text = True` (the only
staircase left). Each family becomes one line with std's `List.allMember`:

```
theorem opKindOf ∀ (text: Text) (listed: operatorText1 text = True): opKind text = True :=
  List.allMember opKind operators1 byComputing text (operatorListed text listed).read
```

**Probe [probed].** `probe4.sw`: a three-literal version of the bridge
and the one-line use both check. `OperatorFacts` is a proposition, not a
test, so that family uses `List.allMem` with a `List.All` built from 22
one-line proofs.

**Saving.** About 250 lines [estimated: 335 less the bridge and four
short theorems].

**Risk.** Low. The `prefix…` staircases (`prefixToken`, `prefixSpellsOf`,
`prefixPlain`) can take the same treatment with a second list.

**Lane.** Sonnet, 25 to 30 min.

## 5. std `Parse` lemmas whose arguments are always `_`

**What.** `Parse.givesDone` takes only the proof. Its siblings take the
value and the spec explicitly, and the proofs write `_ _`:
`Parse.readsFatal _ _` at 103 of its 105 uses.

**Where [measured].**

| Lemma | Uses with `_` | `_` written |
|---|---|---|
| `Parse.followsDone (x) (y)` | 126 of 225 | 252 |
| `Parse.readsFatal (message) (spec)` | 103 of 105 | 205 |
| `Parse.readsAtDone` | 54 of 70 | 88 |
| `Parse.readsDone (x) (spec)` | 47 of 48 | 86 |
| `List.consInjectiveHead` | 25 of 35 | 85 |
| `followsFatalAny` (fmt) | 56 of 99 | 76 |
| `givesFail` (fmt) | 32 of 42 | 32 |
| `Parse.followsLoop` | 15 of 15 | 30 |

**The change.** Make those arguments implicit in std and in
`Syntax/FollowsBase.sw` and `ParseProofs.sw`; delete them at the uses.
Where a use names the value for the reader (`Parse.followsDone None None
Trivial`), keep it as a spelled argument only if inference fails.

**Saving.** About 870 `_` [measured]; few lines. This is for reading.

**Risk.** Low, but wider than `tools/fmt`: about 12 AoC days' parse
proofs use `Parse.readsDone` and its siblings, and the lane may check
only the days it edits. The whole-AoC check is Overmind's.

**Lane.** Sonnet, 30 min. Hash snapshots follow the std change.

## 6. Split `FollowsForms.sw` and `FollowsDecl.sw`

**What.** SW-4216 split `ParseWalk.sw` and a one-theorem edit went from
13 s to 5 s. The two largest namespaces now are `Syntax.FollowsForms`
(4,375 lines, 281 theorems) and `Syntax.FollowsDecl` (4,152, 281). Both
already have section comments (37 and 29) that give the cut: atoms and
sections; binders, lambdas and quantifiers; arms and `match`; patterns;
keyword expressions and blocks; and for declarations: attributes and
groups; headers and binders; definitions; data declarations; imports;
one declaration.

**Saving.** Edit-loop time for every later lane in these files. No lines.

**Risk.** Low: a pure move. It conflicts with any open edit of the same
files, so run it after target 3.

**Lane.** DeepSeek, 25 min each, one after the other. Next in size if
this pays: `Fmt/Walk.sw` 2,818, `Syntax/ReadBackRuns.sw` 2,738,
`Fmt/ToldDeclProofs.sw` 2,612, `Fmt/HangProofs.sw` 2,594,
`Syntax/LexProofs.sw` 2,549.

## 7. Later slices out of the root namespace

**What.** Fourteen files share `namespace Fmt`, and 146 files depend on
it. The proving guide records 5:18 to recheck the project after one edit
there. Seven of the fourteen are `Slice2.sw` to `Slice6a.sw`, program
code for slices that have no proofs yet, used by `Twin.sw` and tests.

**Where [measured].** Following names from the proof files and the slice
1 driver, 679 of the root's 3,067 declaration lines are never reached:
all of `Slice4a`, `Slice4b`, `Slice5a`, `Slice6a`, all but one
declaration of `Slice4c`, and 82 lines of `Rules.sw`. `Slice2` and
`Slice3` are reached (`within2`, `within3`, `commented`).

**The change.** Give `Slice4a` to `Slice6a` a namespace of their own
(`Fmt.Later`, say), imported by `Twin.sw` and the tests that need it.

**Saving.** Work on a later slice stops invalidating the slice 1 proofs.
Worth little tonight; worth a five-minute recheck per edit once slice 2
work starts.

**Risk.** Low. The reachability is by name, so the lane confirms with a
check of `Fmt` and of `Twin`'s namespace.

**Lane.** DeepSeek, 20 min.

## 8. A record for the hung-line hypotheses

**What.** The longest proof, `atomHung` (415 lines), and its siblings
`unaryHung`, `appHung`, `cmpHung`, `arrowHung`, `appendHung` and
`mulAccHung` each have a 15- to 24-line statement, six lines of which
are the same:

```
(lineRead: lineAll read = True)
(lineRest: lineAll rest = True)
(openFirst: openHead modes read = True)
(bound: bounds modes (state.enters read) = True)
(hung: hangsFrom state (leavesOf (read ++ rest)) = True)
(deepItems: deepAll (read ++ rest) = True)
```

**Where [measured].** 13 theorems in `Syntax/ReadBackHungApp.sw`,
`…Atoms.sw`, `…AtomsLemmas.sw`, `…Chains.sw`, `…InlineLemmas.sw` and
`…Top.sw`. The recursive call in `atomHung` passes 17 arguments.

**The change.** A record `HungAt modes state read rest` with those six
fields, and two or three lemmas for the moves the proofs repeat (step
past an opener, split `read`).

**Saving.** About 65 statement lines and five arguments per call
[estimated]. The proofs themselves are long because each constructor's
case is different work; I found no shortcut for that.

**Risk.** Medium: internal statements are restated. `FullHungAt` is the
induction's statement, so the lane must show it unfolds to the same
proposition or leave it.

**Lane.** Sonnet, 30 to 40 min.

## 9. Comments and names left from the process

**Where [measured].**

- 59 mentions of "lane N" in comments ("lane 2's `…Deaf` lemmas", "Lane
  4's facts about this lane's functions"). They name who wrote a proof,
  which the reader cannot use; the file name can replace each.
- 158 `SW-…` references in 98 files. Some point at a design note and
  earn their place; the lane should keep those and drop the ones that
  narrate history.
- Four files whose namespace is not their file name:
  `Syntax/LexProofs.sw` is `Syntax.Proofs`, and `Fmt/BlankProofs.sw`,
  `MeaningProofs.sw` and `MergeProofs.sw` share `Fmt.Proofs`. The
  proving guide has a paragraph warning about exactly this.
- 549 declarations have a digit in the name; 179 end in `1`
  (`grammar1`, `within1`, `formatAccepts1`). SW-4210's note keeps the
  slice's own names numbered on purpose, and I did not re-audit which of
  the 179 are those.

**Lane.** DeepSeek, 20 to 30 min: the comments, and the two namespace
renames with their importers.

## 10. Small std and tidy items

One lane, DeepSeek or Sonnet, 25 min:

- `Syntax/LexReadsProofs.sw` defines its own `Gives parser holds`, which
  is `Parse.Gives Parse.Invariant.any parser holds`, with its own
  `givesDone` (explicit value and spec), `givesThen` and `givesFatal`.
  Use std's.
- General facts still local [measured: 53 theorems whose statements name
  nothing from `tools/fmt`, 273 lines; most are one-off Bool identities
  that should stay where they are used]. The ones that belong in std:
  `nonZeroAdd`, `nonZeroAddLeft` (`OutputFileProofs`), `boolEqSelf`
  (`SplitProofs`), `orImplies` (`ToldDeclProofs`), `replicateSpaces`
  (`PrintLexProofs`), `takeSplit` (`LexReadsProofs`), `cutOfMade`
  (`LexProofs`), `startsHeadChar` (`SharedFacts`), and the
  `digitNot…`/`digitBeq` character facts (`TreeJoinProofs`,
  `GoodItemProofs`, `LexProofs`).
- The `…Blank` list lemmas: 13 theorems (`paramsBlank`, `armsBlank`,
  `scrutineesBlank`, `fieldPatternsBlank`, `clausesBlank`,
  `operationsBlank` and others in `FollowsForms`, `FollowsStatements`,
  `FollowsDecl`) are the same 12 lines over different element types: a
  function that splits over cons gives equal results on `List.All2`-alike
  lists. One std lemma would make each about 4 lines.

## Looked at and not recommended

- **Dead lemmas: none of note.** A name-count script finds 109
  theorems used nowhere else. 88 are `…Example` theorems and the other
  21 are witnesses and illustrations in the `…Statements` files
  (`witnessIdempotent`, `holdsOnClosers`). SW-4193 did this job. The
  count is by text, so it can miss a dead lemma whose name also appears
  in a comment.
- **Spelled arguments.** 392 remain after three script passes; they are
  the ones the script found necessary.
- **A shared framework for the printer's logics.** `HangLays`, `Steps`,
  `Passes` and `Spells` each have their own `…Cons`, `…Nest`, `…Group`
  lemmas. Only 26 lemma names are shared by three or more, and the
  copies beyond one each total 331 lines [measured]. A generic version
  would restate four definitions to save that.
- **Short list inductions.** 285 theorems of eight lines or fewer lift a
  fact from an element to a list (1,618 lines). Most are over the
  formatter's own recursive functions, not `map` or `all`, so no one std
  lemma fits; `match induct` (SW-4261, SW-4264) is the right tool and is
  under way.
- **Merging the shape walk with the tokens-kept walk.** SW-4210's note
  argues against it; only 6 theorem pairs across the two are equal up to
  renaming.
- **The long per-constructor proofs** (`homeStands`, `speltSlots`,
  `bitsHeard`, `elShape`, `elCalm`, `elSpells`). Each arm does different
  work. Targets 1 and 2 shorten them; I found nothing structural.

## What this lane did not do

- It did not run `stitchwort uses --unused --dead`, which checks the
  whole project; the dead count is textual.
- It did not time any check. The edit-loop figures are SW-4216's and the
  proving guide's.
- The line savings for targets 1, 3, 4 and 8 are estimates from measured
  counts. Only target 2's is a direct count of removable lines, and only
  targets 2 and 4 were probed, each on a small stand-in for the real
  goals.
- It did not read the 36 proofs over 100 lines one by one: `atomHung`,
  `exprOk` and `exprTwice` were read, the rest classified by name and
  family.
