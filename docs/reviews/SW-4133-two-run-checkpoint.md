# Checkpoint: the two-run parser proofs (SW-4177, lane 9 of SW-4132)

Fable, paper review, 19 Nov 2026. Read against `main` with lanes 1 to 8
merged (f59ee458b). Nothing was built or checked here: that the files
check with no open goal is taken from the lanes' reports and the merge
verifier, plus a grep of the chain's files for `?` goals, `axiom` and
`trusted` (none).

## Verdict: sound, with notes

`groupKeepsTokens` says what the formatter needs, with no hypothesis
beyond "same tokens" and "the first group parses", and for every
declaration, not only slice 1's. No gap found. Nothing was narrowed
(D3688): no parser, lexer, grammar, blanking or walk file changed in the
eight lanes, and `groupKeepsTokens1`'s statement is SW-4129's, character
for character.

The notes, none of which is a defect in the proofs:

1. "Same tokens" means whole tokens, with `column` and `lineStart`. That
   is right (the parser reads layout), and it is the caller's to supply.
   Rule N's own-line last comma moves a `lineStart`, so that case is
   outside this theorem and stays behind `settledParses1`'s `plain1`
   condition (SW-4131), as before.
2. The theorem speaks of successes only. Used both ways it gives "one
   parses if and only if the other does", but says nothing about the two
   error messages being equal.
3. The twin's `Group.bare` can differ from the original's. Nothing
   downstream of `groupKeepsTokens1` reads it, but a later lemma that
   carries a fact from `decl` to `twin` through the blanked trees must be
   about a function that doesn't read `bare`.
4. `Anything` is used on three `()` results as well as on `Comments` and
   `consumedBare`'s `Bool`. Harmless; the doc comment's "only" is
   slightly off.
5. The file layer above (`groupsKeepTokens1`, `parseKeepsTokens1`) is
   still slice 1 only, through `seenAfter1`.

A point that shortens most of the questions below: the top theorem is
closed and its statement mentions none of the intermediate relations.
`DeclsAlike` unfolds to exactly `decl.walk blankPure = twin.walk
blankPure` (`FollowsBase.sw:88`), and `FollowsParse.sw` supplies every
hypothesis the lanes' lemmas take. So a relation that was too weak, or a
lemma hypothesis that didn't hold, could only have stopped the proof
from going through; it cannot make the checked statement say less. What
needs a reader's judgement is therefore the statement itself: its two
hypotheses, `SameCode`'s starting point, and what `blankPure` erases.

## 1. Does `groupKeepsTokens` say what the formatter needs?

Yes. `Fmt/SettleParseProofs.sw:43`:

```
theorem groupKeepsTokens ∀ (seen: Seen) (group other: List Leaf) (decl: Decl)
    (same: tokens group = tokens other)
    (runs: groupRun seen group = Ok decl):
    ∃ (twin: Decl) => groupRun seen other = Ok twin ∧ twin.walk blankPure = decl.walk blankPure
```

- `tokens` is `leaves.map (leaf => leaf.token)` (`Syntax/SettleProofs.sw:10`),
  and a `Leaf` is `{ token, trivia }` (`Syntax/Tree.sw:18`). So `other` is
  any leaves with the same tokens and any trivia at all: comments moved,
  rewritten, added or removed, and any blank-line counts.
- `groupRun` is what `parseGroups` runs on a group (`:36`), with the same
  `Seen` on both sides.
- It is the plan's statement (docs/reviews/SW-4132-two-run-parse.md §3,
  lines 217 to 221) unchanged.

Is "equal after `walk blankPure`" the right notion? `blankPure`
(`Fmt/BlankProofs.sw:347`) is the seven functions of `Fmt/Blank.sw`. I
read all of that file. Every field it sets is one of:

- a `Comments` set to `Comments.none` (`above = [], after = None,
  blankBefore = False`, `Blank.sw:20`), directly or through `Word.blank`
  (`:22`), which keeps the word's `text`;
- `Group.bare = True` (`Blank.sw:113`), the one non-`Comments` field.

Every `Option` keeps its `Some`/`None` (`blankAfter`, `blankComments`,
`blankPair`, `blankCommentsWord`, `blankReverse`, `blankUnfolding`), so
no presence of a keyword or clause is erased; trailing-comma flags,
kinds, `implicit`, texts and all sub-trees are untouched.

`bare` is `default.isNone && consumed` (`DeclParser.sw:281`), where
`consumed` is "the group's items have no comments" (`consumedBare`,
`:286` to `:296`). `default` itself stays in the blanked tree, so
setting `bare = True` hides only the comment-derived half. Nothing a
program means is lost.

Two further supports:

- `meaningBlanksFirst` (`BlankProofs.sw:378`) proves
  `file.withoutComments.meaning = file.meaning`. So blank-equal trees
  have equal `meaning`: the notion here is at least as strict as the
  trusted "same program", and erases only what `meaning` already leaves
  out (`Fmt/Meaning.sw:11` to `:16`).
- A node the walk failed to blank would make the conclusion stricter,
  not looser (`Blank.sw:11` to `:13`), and the proof would then not have
  closed, since comments are unrelated between the runs.

Note 1 (token positions). A `Token` is `{ kind, text, column, lineStart }`
(`Syntax/Token.sw:309`), so `same` fixes each token's column and whether
it starts its line. Comments are `--` to the end of the line only
(`Token.sw:290` to `:293`), so moving or rewriting a comment can't change
a token's column, and can change `lineStart` only where a pass moves a
token relative to a line break. Rule N does that in one case, the
own-line last comma, which `settledParses1` (`SettleParseProofs.sw:288`)
excludes by `plain1` and SW-4131 treats on its own. That condition
predates this work and is not part of the chain reviewed here; I list it
so nobody reads `groupKeepsTokens` as covering it.

Note 2 (successes only). If `group` fails to parse, the theorem used
with the roles swapped says `other` fails too, but the messages are not
related. The formatter's proofs so far start from "the source parses",
so this is enough today.

## 2. The relations and `Anything`

`Anything` is defined at `FollowsBase.sw:90`. Every line that names it in the Follows
files (66 in `FollowsDecl.sw`, 4 in `FollowsStatements.sw`, 3 in
`FollowsForms.sw`, 3 in `FollowsBase.sw`, 1 in `FollowsLadder.sw`; doc comments included) relates one of:

- a `Comments`: the result of `fixedFrom` (`FollowsForms.sw:2453`) and
  `expectFixed` (`FollowsDecl.sw:81`, `:663`; `FollowsStatements.sw:101`),
  and the `Comments` half of a pair or option (`PairAlike Anything
  WordsAlike`, `PairAlike Anything ExprsAlike`, `Option.Alike Anything`,
  `PairAlike Anything Anything` for a rule's `Option (Comments,
  Comments)` at `FollowsStatements.sw:1481`). In each the other half is
  related properly, and `Option.Alike` (`std/Parse/Follows.sw:83`) still
  forces `Some` against `Some` and `None` against `None`;
- `consumedBare`'s `Bool` (`FollowsDecl.sw:693`), once;
- a `()`: `refuseAttributes` (`FollowsDecl.sw:248`, `:1205`),
  `afterOpaqueOn` and `afterOpaque` (`:4288`, `:4297`). On `()` it is the
  same as equality. This is note 4: `FollowsBase.sw:39` to `:41` says
  `Anything` is on `Comments` and that one `Bool` only.

No other `Bool`, `Nat`, `Tok`, `Text` or tree is related by `Anything`.
The other relations are equalities after blanking (`FollowsBase.sw:72` to
`:88`), `Same`, `List.All2` and `PairAlike`; `FollowsDecl.sw`'s own
(`HeaderAlike` and the rest) are described as equality of a blanked key
and I did not read each one, for the reason given under the verdict.

Is the unrelated `bare` flag sound? Yes. `groupKeepsTokens1` gives its
callers three things about `twin`: the blanked-tree equation, `grammar1`
and `loweringError`. The first can't see `bare` (`Group.blank`). The
other two are read off the blanked tree by `grammar1Deaf` and
`loweringDeaf` (`DeafProofs.sw:984`, `:1228`), proved for every `Decl`,
so neither reads `bare`. The code that does read it, the merge pass
(`Fmt/Passes.sw:313`), runs on the settled tree itself and so sees that
tree's own flag, computed from its own comments, which is what it
should see. Note 3 is the caution for later work: `twin.bare` and
`decl.bare` are not known equal.

## 3. `SameCode` and line positions

`Leaf.stripped` sets `trivia = Trivia.empty` and nothing else
(`DeafProofs.sw:11`); `Item.stripped` strips the leaf and keeps the
item's `glued`, `afterOperand`, `afterDot`, `index`, `depth` and
`lineIndent` (`:13`, `Parser.sw:30`). `Trivia` is the leading comments,
the blank-line count and the trailing comment (`Token.sw:298`).

The parser does read line positions (`stopsByLine`, `lineIndent`,
`token.column`, `token.lineStart`, `glued`), and stripping keeps all of
them: they are in the `Token` or computed from tokens by `itemsAfter`
(`Parser.sw:52` to `:70`), never from trivia. So there is no gap of the
kind the question asks about. `stopsByLineDeaf` (`DeafProofs.sw:42`) and
its neighbours are proved, and `groupItemsSameCode` (`:916`) derives
`List.All2 SameCode (items group) (items other)` from the token equation
alone.

What stripping erases that is not a comment: `trivia.blankLines`. The
parser copies it into `Comments.blankBefore` (`Syntax/Expr.sw:36`) and
reads it nowhere else, and blanking sets it to `False`.

## 4. Hypotheses, and narrowing

The chain from the walk to `groupKeepsTokens1`:

| Step | Where | Hypotheses |
|---|---|---|
| `groupItemsSameCode` | `DeafProofs.sw:916` | `tokens group = tokens other` |
| `expressionRuleFollows` | `FollowsParse.sw:30` | none |
| `expressionSelfFollows`, `patternSelfFollows` | `:53`, `:56` | none |
| `declarationFollows` | `:59` | none |
| `groupDeclarationFollows` | `:66` | none |
| `Parse.followsRun` | `std/Parse/Follows.sw:499` | the `Follows` fact, alike inputs, the first run succeeds |
| `declarationKeepsTokens` | `FollowsParse.sw:79` | `same`, `runs` |
| `groupKeepsTokens` | `SettleParseProofs.sw:43` | `same`, `runs` |
| `grammar1Deaf`, `loweringDeaf` | `DeafProofs.sw:984`, `:1228` | none |
| `groupKeepsTokens1` | `SettleParseProofs.sw:55` | `same`, `runs`, `decl.grammar1 = True` |

Inside the lanes' files, lemmas take more than alike arguments and the
knot in these ways, all supplied in `FollowsParse.sw` or at the call:

- the other lanes' facts as hypotheses (`HeaderGroupFollows`,
  `BinderTypeFollows`, `PiExprFollows`, `ResultTypeFollows`,
  `ExpectFixedFollows`, `LowerQualifiedFollows`, `AttributesOfFollows`,
  `DefinitionPartsFollows`, `AltPatternFollows`, and lane 7's
  `inductFollows` to `thenBodyFollows`), each proved for every `self`
  and `selfTwin` at a knot (`FollowsDecl.sw:4513` to `:4551`,
  `FollowsForms.sw:3786`);
- `followsLook`'s `deaf` (`FollowsBase.sw:197`): the look-ahead gives the
  same answer on stripped items, supplied by lane 2's `…Deaf` lemmas,
  each for all inputs;
- `Never` for branches that only fail (`FollowsBase.sw:109`), proved for
  each such function.

None is a condition on the input, and the top statement shows none
survives. No narrowing: `git diff 373c9e872..HEAD` (SW-4129's merge to
now) touches none of `Parser.sw`, `DeclParser.sw`, `Statements.sw`,
`Lexer.sw`, `Token.sw`, `Expr.sw`, `Decl.sw`, `Blank.sw`, `Walk.sw`,
`BlankProofs.sw` or `Grammar1.sw`. (`Driver1.sw` and `Slice1.sw` did
change in that range, from other tickets, and both changes accept more:
`sourcePlain1` for `plain1`, and `auto` as a name.)

The audit's vacuity warnings on `gluedSame`, `indexSameOf` and
`depthSameOf` (SW-4170's note) are the random tester not producing two
items with `SameCode`; the hypothesis holds of any item and itself.

## 5. `groupKeepsTokens1`

Yes on both counts. The proof (`SettleParseProofs.sw:63` to `:73`) takes
`twin` and the blanked equation from `groupKeepsTokens`, then two `calc`
chains: `twin.grammar1` to `(twin.walk blankPure).grammar1` by
`grammar1Deaf twin`, across by the equation, back by `grammar1Deaf decl`,
then the hypothesis; and the same shape with `loweringDeaf` for
`loweringError`. Nothing else is used.

The statement is identical to the one SW-4129 left open
(`git show 373c9e872:tools/fmt/src/Fmt/SettleParseProofs.sw`, lines 45
to 53, where the body was `?`): same binders, same three hypotheses,
same four conjuncts, and `groupRun` unchanged. The definitions it names
are unchanged too (question 4's diff).

## 6. `std/Parse/Follows.sw`

Nothing vacuous or too strong that affects this use.

- `Parse.Follows` (`:53`) is one-directional and about successes, and
  says so. It holds trivially of a first parser that never succeeds
  (`followsFatal`, `followsStop`, `followsNever`, `:172` to `:193`); that
  is how failing branches are discharged, and it is honest because the
  top theorem's `runs` hypothesis puts the first run on a succeeding
  path. `followsRun` (`:499`) turns the fact into a statement about
  `Parse.run` with the success as an explicit hypothesis, using
  `runFromAddMark` (`:449`), an induction over every `Parse` operation,
  so the "with the mark after it" form inside `Follows` is not a hidden
  restriction.
- `Parse.Mark.Alike` (`:32`) asks for related items left, equal offsets
  and equal counts left. `followsRun` establishes it at the start from
  `List.All2` alone (`:516`). It is not too strong for two inputs of the
  same length, which is the only use.
- The file's header (`:9` to `:19`) says the family does not cover
  `optional`, `many`, `oneOf`, `attempt` or `label`. The formatter's
  parser uses none of them (grep of `tools/fmt/src/Syntax`: only
  `Lexer.sw` calls `Parse.many`, and the lexer is not in this chain), so
  the success-only form is enough here. Anyone reusing the family on a
  parser with choice would be stopped by the missing lemmas, not misled.
- `followsRecursiveWithFuel` (`:363`) at no fuel is vacuous because the
  first run is a `fatal`; both runs take their fuel from `left`, which
  `Mark.Alike` makes equal.
- `followsReset` (`:162`) relates its `()` results by an inline
  `x y => Unit`; fine.

## Follow-ups

| Candidate ticket | Model | Estimate |
|---|---|---|
| Lift the file layer off slice 1: `parseKeepsTokens` for every file, from `groupKeepsTokens`, needing "`seen.after` and `loweringError` don't read comments" in place of `seenAfter1` and `declLowers1` (the plan's Findings already name this). Statement to be agreed first. | Opus | 25 min |
| Doc wording: `FollowsBase.sw:39` to `:41` and `FollowsDecl.sw:56` to `:59` say `Anything` is only on `Comments` and one `Bool`; add "and `()` results", or relate those three by `Same`. | DeepSeek | 5 min |
| A note on `groupKeepsTokens`' doc that `same` includes each token's `column` and `lineStart`, and that `twin`'s `Group.bare` is not known equal to `decl`'s. | DeepSeek | 5 min |
| Only if a later slice needs it: the failure direction with equal messages (a two-sided `Follows` over outcomes, as the std header describes). Not needed now; file as backlog or not at all. | Fable (statement), Opus (proof) | not estimated |

## What this review did not do

It did not run `check` or the audit, read the roughly 13,000 lines of
lemma proofs, or read each `…Alike` relation in `FollowsDecl.sw` and
`FollowsStatements.sw` (see the verdict for why that doesn't bear on the
top statement). It did not read `Fmt/Walk.sw` in full: that `Decl.walk`
only rebuilds the tree and applies the seven steps is taken from its
head (`Walk.sw:294`) and from `blankAgrees` and `meaningBlanksFirst`,
which tie it to the traversal `meaning` uses.
