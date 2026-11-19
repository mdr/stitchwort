# SW-4165: the two-run pattern lane (Syntax/FollowsBase.sw)

Lane 3 of the two-run parser plan (docs/reviews/SW-4132-two-run-parse.md).
Opus, 19 Nov 2026, about 15 minutes. `Syntax/FollowsBase.sw`, 70 theorems,
no open goals, audit clean. The file's header is the how-to for lanes 4 to
7; this note keeps the lane's report for them.

## No single cross-file record (orchestrator's call)

The parser files call each other (`statement` calls `exprInline`,
`exprKeyword` calls `letStatement`). A shared record of every other file's
facts could never be built: lane 8 would need each lane's lemmas to build
it before any could be used. So each walk lemma takes, as its own
hypothesis, the `Follows` fact of each function from another lane that it
calls directly; lane 8 supplies them in call order. That order has no
cycle, because the parser recurses only through `self`, `pself` and fuel.
`followsParenRest`, `followsParenOther`, `followsParenAtom` and
`followsBracketAtom` show the pattern (facts for `rightSection`,
`operatorSection`, `namedArgument` passed in). Lanes 4 and 5 split
`Parser.sw` and call each other's functions, so this applies between them
too.

## Relations

- `WordsAlike`, `ExprsAlike`, `PatternsAlike`, `DeclsAlike`: equal after
  `walk blankPure`.
- `GroupsAlike`, `StatementsAlike`, `LetsAlike`: walked, then `.blank`.
- `ParamsAlike`: a one-element list through `blankParams (walkParams
  blankPure …)`.
- `Same` (equality) for `Bool`, `Nat`, `Tok`, `Option Tok`, `Modes`.
- `Anything` for `Comments`, and for `consumedBare`'s `Bool` only.
- `PairAlike` for pairs; lists use `List.All2`.

## Wrappers (each: the function follows itself on alike arguments)

- Reading one item: `followsBump`, `followsBumpThen`, `followsEat`,
  `followsExpect`/`On`, `followsLower`/`On`.
- Look-aheads: `followsLeft`, `followsOn`, `followsLook`, `followsPeek`,
  `followsPeekAt`, `followsPeeked`, `followsAt`, `followsAtEither`,
  `followsOffset`, `followsLeftCount`.
- Sequencing: `followsThenEq` (a value equal in both runs).
- Failures: `followsFail`, `followsFailName`, `followsFailNameOn`,
  `followsGap`, `followsFatalAny`.

Knot: `SelfFollows` and `PatternSelfFollows`; the tie lemmas
`followsExpressionAt`, `followsExpression` and `followsPattern` close the
recursion with `Parse.followsRecursiveWith`, so lane 8 proves only
`expressionRule`'s and `patternRule`'s rule lemmas.

Worked pattern: tree builders `alike<Constructor>` (atom, prefix, paren,
unit, annotation, tuple, list, spread; `walkExprsAlike` for lists); atoms;
brackets and tuples; lists; comma lists (`followsCommaListFrom` by fuel);
paren and bracket atoms.

## What lanes 4 to 7 do

- One `followsF` per function. Hypotheses: alike arguments, the knot, the
  direct cross-lane calls. Nothing else.
- Each `let x := p()` is `Parse.followsThen`, or `followsThenEq` when the
  value is equal in both runs; finish with `followsDone`/`followsMap` and
  an `alike<Constructor>` lemma.
- Where each run computes a value from its own items, prove the two equal
  with lane 2's lemmas (`deafOfStripped`, `deafItem`, `stopsSame`), then
  `rewrite` and `match`.
- Give `[p := …] [q := …] [j := …] [k := …]` for steps on `Parse.mark()`,
  for `||`/`&&` between two parsers, and after a match on a pair. After a
  `match`, failure lemmas need the second parser written out.
- Write the parser's `fatal` as `Syntax.fatal`: a bare `fatal` resolved to
  std's under `import Std (Parse)`.
- A theorem about a function with a free result type (`modes.fail what :
  a`) needs `∀ [a: Type]` and `Never [a := a]`.
- Hidden matches (from SW-4141): `byComputing` and `cases` fail on a
  stripped item against a plain one until each stuck scrutinee is split
  with a `match` (the item's `kind`, `modes.stops item.stripped`,
  `skipGroup`, …); lists need `rewrite <- lemma` first; destructure records
  and tuples first; `cases` caps at 64 on a `Tok` split. Mismatched-length
  list arms: `let clash := Eq.cong (.isEmpty) same` then `cases`.
- `bareTaken` and `itemsBare` read comments (hard spot 1): only
  `consumedBare`'s `Bool` is related by `Anything`.

Not done here: other atoms (`includeAtom`, `universeAtom`, `casesAtom`,
`atomOf`, `atomAfter`, suffixes) go to lanes 4 and 5; list lemmas for
`ParamsAlike` and `GroupsAlike` are added by the lane that first needs one.
