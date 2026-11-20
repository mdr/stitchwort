--| Two runs of the parser on items that differ only in their comments give trees that are alike: equal once their
--| comments are blanked (docs/reviews/SW-4132-two-run-parse.md). This file has the relations, the two-run
--| forms of the parser's own operations (`bump`, `peek`, `eat`, `expect`, `lower`, the failures), the recursion's knot,
--| and atoms, brackets, tuples, lists and comma lists walked as the pattern for the rest of the parser.
--|
--| How to write one. Each parser function `f` gets one lemma, `followsF`: called with alike arguments, `f` follows
--| itself. Its only hypotheses are alike arguments, the knot (`SelfFollows self selfTwin`, or `PatternSelfFollows`),
--| and one hypothesis for each function in another file that `f` calls directly (below). The proof follows `f`'s
--| body step by step:
--|
--| - `let x := p(); rest` is `Parse.followsThen (followsP …) (x xTwin xs => …)`, where `xs` says `x` and `xTwin` are
--|   alike. When `p` gives a `Bool`, `Nat`, `Tok` or `Option Tok` (a look-ahead, `modes.at`, `offset()`), its lemma
--|   relates the values by `Same`, and `followsThenEq (followsP …) (x => …)` carries on with one value for both runs.
--| - The end, a tree built from the values read, is `Parse.followsDone _ _ (alike… …)`, or `Parse.followsMap` when the
--|   last step reads something. Each tree constructor gets an `alike…` lemma (`alikeParen`): a `calc` from the walked
--|   tree to the constructor with blanked words (`byComputing`), `rewrite` with the parts' facts, and back.
--| - A `match` or `if` on a value both runs share (a `Same` value, an argument) is a `match` in the proof. On a value
--|   each run computes from its own items (`peekIn`, `rightOperator`, `item.kind`), first prove the two equal with
--|   the lemmas in `Syntax/DeafProofs.sw` (`deafOfStripped f fDeaf items others same`, `deafItem`, `stopsSame`), then
--|   `rewrite` with that and `match` on the twin's value (`followsParenRest`), or match both and leave out the arms
--|   the checker calls unreachable (`followsLowerOn`).
--| - `f … left()` (an `…On` function given the items left) is `followsOn`, with a lemma for `f` on two lists related
--|   by `List.All2 SameCode`.
--| - A branch that only fails is `followsFail`, `followsFailName`, `followsGap` or `followsFatalAny`. After a `match`
--|   the goal has already taken a step, so give the second parser: `followsFail modes what (() => modes.fail what)`.
--| - A loop with its own fuel (`commaListFrom`, `blockLines`) is a recursive theorem on the fuel, the same on both
--|   sides (`followsCommaListFrom`). `Parse.loop` is `Parse.followsLoop`.
--| - A parser passed as an argument (`next`, `ends`) comes with its own `Follows` fact, for the two runs' versions
--|   (`followsCommaList`).
--| - A `match` the parser writes inside a lambda (the step of a loop, of `operatorLinks`) is not restated in the
--|   proof: restating it gives a different hidden function. Leave the step to unify (`Parse.followsLoop _ _ …`).
--| - A function the proof calls at changed modes (`modes.inBrackets`, a `sectionHead`) has a cross-file hypothesis
--|   stated for every `modes`, not one.
--| - Items the two runs compute from their own items (`negativeNumeral`, `headKind`, `pipeAheadOn`) are proved equal
--|   with the `…Deaf` lemmas in `Syntax/DeafProofs.sw` and rewritten, so those need no hypothesis.
--|
--| When `Parse.followsThen` can't find the parsers itself, give them: `[p := …] [q := …] [j := …] [k := …]`. This is
--| needed for a step on `Parse.mark()` (`Parse.mark().left + 1` as fuel, `followsListItems`), for `||` or `&&` between
--| two parsers, which read the second only when needed (`followsAtEither`), and after a `match` on a pair. Write the
--| parser's `fatal` as `Syntax.fatal` in a statement here.
--|
--| The relations: words, expressions, patterns, groups, parameters, statements, `let`s and declarations are alike
--| when they are equal once walked with `blankPure` and, for those the walk doesn't blank itself, blanked
--| (`GroupsAlike`). Lists are `List.All2` of the element's relation, pairs `PairAlike`. `Bool`, `Nat`, `Tok`,
--| `Option Tok` and `Modes` are `Same`. `Comments` are `Anything`, and so is `consumedBare`'s `Bool`: the one value the
--| parser computes from comments (§4, hard spot 1), which only `Group.bare` keeps and blanking sets to `True`. So are
--| the `()` results of `refuseAttributes`, `afterOpaque` and `afterOpaqueOn`, which compute nothing. No other `Bool`
--| may be related by `Anything`.
--|
--| Calls between files. The files call each other (`statement` calls `exprInline`; `exprKeyword` calls
--| `letStatement`), so one record of every cross-file fact could never be built. Instead each lemma takes, as a
--| hypothesis, the `Follows` fact of each function in another file that it calls directly, written out as
--| that file's lemma will state it (`rightSections` in `followsParenRest`). `Syntax/FollowsParse.sw` supplies them in
--| call order, which has no cycle, since the parser recurses only through `self`, `pself` and fuel.
--|
--| A worked example, `bracketed`:
--|
--| ```
--| def bracketed (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
--|   let open := bump()
--|   bracketedTail self modes open
--| ```
--|
--| `bracketedTail` and `bracketedFirst` only pass values on, so the proof reads through them: `bump`, then `full self`
--| at the inner modes (the knot), then a peek, then `bracketedAfter` on alike values (`followsBracketed` below).
--| `bracketedAfter`'s lemma matches on the peeked `Option Tok`, which both runs share, and ends in the lemmas for a
--| tuple, an annotation or `parenClose`; `parenClose`'s is `followsExpect` mapped through `alikeParen`.

namespace Syntax.FollowsBase
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)

-- The alike relations.

def WordsAlike (word twin: Word): Prop := word.blank = twin.blank

def ExprsAlike (expr twin: Expr): Prop := expr.walk blankPure = twin.walk blankPure

def PatternsAlike (pattern twin: Pattern): Prop := pattern.walk blankPure = twin.walk blankPure

def GroupsAlike (group twin: Group): Prop := (group.walk blankPure).blank = (twin.walk blankPure).blank

def ParamsAlike (param twin: Param): Prop :=
  blankParams (walkParams blankPure [param]) = blankParams (walkParams blankPure [twin])

def StatementsAlike (statement twin: Statement): Prop :=
  (walkStatement blankPure statement).blank = (walkStatement blankPure twin).blank

def LetsAlike (binding twin: Let): Prop := (walkLet blankPure binding).blank = (walkLet blankPure twin).blank

def DeclsAlike (decl twin: Decl): Prop := decl.walk blankPure = twin.walk blankPure

def Anything (x: a) (y: b): Prop := Unit

def Same (x y: a): Prop := x = y

@[noReceiver]
def PairAlike (left: a → b → Prop) (right: c → d → Prop) (pair: (a, c)) (twin: (b, d)): Prop :=
  left pair.fst twin.fst ∧ right pair.snd twin.snd

-- Words of related items.

theorem wordsAlikeOfSame ∀ (item other: Item) (same: SameCode item other): WordsAlike item.leaf.word other.leaf.word :=
  let tokens: item.leaf.token = other.leaf.token := Eq.cong (found => found.leaf.token) same
  calc item.leaf.word.blank
    _ = { text = item.leaf.token.text, comments = Comments.none } := byComputing
    _ = { text = other.leaf.token.text, comments = Comments.none } := rewrite tokens
    _ = other.leaf.word.blank := byComputing

-- Parsers that never succeed.

def Never (p: () → {Parse Item} a): Prop :=
  ∀ (state: Parse.State Item) (value: a) (after: Parse.Mark Item) => ¬(Parse.runFrom state (() => (p(), Parse.mark()))
    = Ok (value, after))

theorem neverFatal ∀ [a: Type] (message: Text): Never [a := a] (() => Syntax.fatal message) := state value after ran =>
  (Result.errNotOk ran).impossible

theorem neverThen ∀ [p: () → {Parse Item} a] [j: a → {Parse Item} b]
    (rest: ∀ (x: a) => Never (() => j x)):
    Never (() => j (p())) :=
  state value after ran =>
    let (x, middle, ranFirst, ranRest) :=
      Parse.runFromThenOk2 p state j (found => (found, Parse.mark())) (value, after) ran
    rest x middle value after ranRest

theorem neverFail ∀ [a: Type] (modes: Modes) (what: Text): Never [a := a] (() => modes.fail what) :=
  neverThen (message => neverFatal message)

theorem followsBump: Parse.Follows SameCode WordsAlike (() => bump()) (() => bump()) :=
  Parse.followsThen
    (Parse.followsNext (item => True) (item => True) (x y same => byComputing))
    (found foundTwin alike =>
      match found, foundTwin with
        | Some item, Some other => Parse.followsDone (wordsAlikeOfSame item other alike)
        | None, None => Parse.followsFatal _ _)

theorem followsBumpThen ∀ [alike: a → b → Prop] (k: Word → {Parse Item} a) (kTwin: Word → {Parse Item} b)
    (rest: ∀ (word twin: Word) => WordsAlike word twin
      → Parse.Follows SameCode alike (() => k word) (() => kTwin twin)):
    Parse.Follows SameCode alike (() => k (bump())) (() => kTwin (bump())) :=
  Parse.followsThen followsBump rest

theorem followsLeft: Parse.Follows SameCode (List.All2 SameCode) (() => left()) (() => left()) :=
  Parse.followsThen Parse.followsMark (m n marks => Parse.followsDone marks.left)

theorem neverFailNameOn ∀ [a: Type] (modes: Modes) (what: Text) (items: List Item):
    Never [a := a] (() => modes.failNameOn what items) :=
  match items with
    | [item, ..rest] =>
      match keywordHere modes item with
        | True => neverFatal _
        | False => neverFail modes what
    | [] => neverFail modes what

theorem neverFailName ∀ [a: Type] (modes: Modes) (what: Text): Never [a := a] (() => modes.failName what) :=
  neverThen (items => neverFailNameOn modes what items)

theorem neverGapOn ∀ [a: Type] (modes: Modes) (message: Text) (items: List Item):
    Never [a := a] (() => modes.gapOn message items) :=
  match blockEnd modes.lines items.head with
    | Some ending => neverFatal ending
    | None => neverFatal message

theorem neverGap ∀ [a: Type] (modes: Modes) (message: Text): Never [a := a] (() => modes.gap message) :=
  neverThen (items => neverGapOn modes message items)

theorem followsFatalAny ∀ [alike: a → b → Prop] (message: Text) (second: () → {Parse Item} b):
    Parse.Follows SameCode alike (() => Syntax.fatal message) second :=
  Parse.followsNever (() => Syntax.fatal message) second (neverFatal message)

theorem followsFail ∀ [alike: a → b → Prop] (modes: Modes) (what: Text) (second: () → {Parse Item} b):
    Parse.Follows SameCode alike (() => modes.fail what) second :=
  Parse.followsNever (() => modes.fail what) second (neverFail modes what)

theorem followsFailName ∀ [alike: a → b → Prop] (modes: Modes) (what: Text) (second: () → {Parse Item} b):
    Parse.Follows SameCode alike (() => modes.failName what) second :=
  Parse.followsNever (() => modes.failName what) second (neverFailName modes what)

theorem followsGap ∀ [alike: a → b → Prop] (modes: Modes) (message: Text) (second: () → {Parse Item} b):
    Parse.Follows SameCode alike (() => modes.gap message) second :=
  Parse.followsNever (() => modes.gap message) second (neverGap modes message)

-- Sequencing on a value both runs agree on.

theorem followsThenEq ∀ [alike: c → d → Prop] [p q: () → {Parse Item} a] [j: a → {Parse Item} c] [k: a → {Parse Item} d]
    (first: Parse.Follows SameCode Same p q)
    (rest: ∀ (x: a) => Parse.Follows SameCode alike (() => j x) (() => k x)):
    Parse.Follows SameCode alike (() => j (p())) (() => k (q())) :=
  Parse.followsThen first (x y same => rewrite <- same then rest x)

-- Looking ahead.

theorem followsLook ∀ (read: List Item → r)
    (deaf: ∀ (items: List Item) => read items = read (items.map Item.stripped)):
    Parse.Follows SameCode Same (() => read left()) (() => read left()) :=
  Parse.followsThen followsLeft (seen seenTwin same => Parse.followsDone (deafOfStripped read deaf seen seenTwin same))

theorem followsLeftCount: Parse.Follows SameCode Same (() => Parse.mark().left) (() => Parse.mark().left) :=
  Parse.followsThen Parse.followsMark (m n marks => Parse.followsDone marks.right.right)

theorem followsOffset: Parse.Follows SameCode Same (() => offset()) (() => offset()) :=
  Parse.followsThen Parse.followsMark (m n marks => Parse.followsDone marks.right.left)

theorem followsPeek ∀ (modes: Modes): Parse.Follows SameCode Same (() => modes.peek) (() => modes.peek) :=
  followsLook (peekIn modes 0) (peekInDeaf modes 0)

theorem followsPeekAt ∀ (modes: Modes) (ahead: Nat):
    Parse.Follows SameCode Same (() => modes.peekAt ahead) (() => modes.peekAt ahead) :=
  followsLook (peekIn modes ahead) (peekInDeaf modes ahead)

theorem followsAt ∀ (modes: Modes) (wanted: Tok):
    Parse.Follows SameCode Same (() => modes.at wanted) (() => modes.at wanted) :=
  followsThenEq (followsPeek modes) (seen => Parse.followsDone byComputing)

theorem followsPeeked ∀ [alike: a → b → Prop] (modes: Modes)
    (k: Option Tok → {Parse Item} a) (kTwin: Option Tok → {Parse Item} b)
    (each: ∀ (seen: Option Tok) => Parse.Follows SameCode alike (() => k seen) (() => kTwin seen)):
    Parse.Follows SameCode alike (() => k modes.peek) (() => kTwin modes.peek) :=
  followsThenEq (followsPeek modes) each

theorem followsOn ∀ [alike: a → b → Prop] (k: List Item → {Parse Item} a) (kTwin: List Item → {Parse Item} b)
    (each: ∀ (items others: List Item) => List.All2 SameCode items others
      → Parse.Follows SameCode alike (() => k items) (() => kTwin others)):
    Parse.Follows SameCode alike (() => k left()) (() => kTwin left()) :=
  Parse.followsThen followsLeft each

-- Reading one item.

theorem followsEat ∀ (modes: Modes) (wanted: Tok):
    Parse.Follows SameCode (Option.Alike WordsAlike) (() => modes.eat wanted) (() => modes.eat wanted) :=
  followsThenEq (followsAt modes wanted) (here =>
    match here with
      | True => Parse.followsMap (word => Some word) (word => Some word) followsBump (x y alike => alike)
      | False => Parse.followsDone Trivial)

theorem followsExpectOn ∀ (modes: Modes) (wanted: Tok) (what: Text) (seen: Option Tok):
    Parse.Follows SameCode WordsAlike (() => modes.expectOn wanted what seen) (() => modes.expectOn wanted what seen) :=
  match isSome wanted seen with
    | True => followsBump
    | False => followsFail modes what (() => modes.fail what)

theorem followsExpect ∀ (modes: Modes) (wanted: Tok) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.expect wanted what) (() => modes.expect wanted what) :=
  followsThenEq (followsPeek modes) (seen => followsExpectOn modes wanted what seen)

theorem followsLowerOn ∀ (modes: Modes) (what: Text) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode WordsAlike (() => modes.lowerOn what items) (() => modes.lowerOn what others) :=
  match items, others with
    | [], [] => followsFailName modes what (() => modes.failName what)
    | [item, ..rest], [other, ..restTwin] =>
      let kinds: item.kind = other.kind := deafItem Item.kind itemKindDeaf item other same.left
      let stops: modes.stops item = modes.stops other := stopsSame modes item other same.left
      let qualified: isQualified item = isQualified other := deafItem isQualified isQualifiedDeaf item other same.left
      let guards: (item.kind == Lower && !modes.stops item) = (other.kind == Lower && !modes.stops other) :=
        Eq.cong2 (kind stopped => kind == Lower && !stopped) kinds stops
      match lower: item.kind == Lower && !modes.stops item, lowerTwin: other.kind == Lower && !modes.stops other with
        | True, True =>
          match named: isQualified item, namedTwin: isQualified other with
            | True, True => followsFatalAny _ _
            | False, False => followsBump
        | False, False => followsFailName modes what (() => modes.failName what)

theorem followsLower ∀ (modes: Modes) (what: Text):
    Parse.Follows SameCode WordsAlike (() => modes.lower what) (() => modes.lower what) :=
  Parse.followsThen followsLeft (seen seenTwin same => followsLowerOn modes what seen seenTwin same)

-- The knot.

def SelfFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (goal: Goal) => Parse.Follows SameCode ExprsAlike (() => self goal) (() => selfTwin goal)

def PatternSelfFollows (pself pselfTwin: PatternGoal → {Parse Item} Pattern): Prop :=
  ∀ (goal: PatternGoal) => Parse.Follows SameCode PatternsAlike (() => pself goal) (() => pselfTwin goal)

theorem followsFull ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => full self modes) (() => full selfTwin modes) :=
  knot { modes, level = LevelFull }

theorem followsExpressionAt ∀
    (rule: ∀ (self selfTwin: Goal → {Parse Item} Expr) => SelfFollows self selfTwin
      → SelfFollows (expressionRule self) (expressionRule selfTwin)) (goal: Goal):
    Parse.Follows SameCode ExprsAlike (() => expressionAt goal) (() => expressionAt goal) :=
  Parse.followsRecursiveWith
    [goals := Same]
    expressionRule
    expressionRule
    (self selfTwin inner argument argumentTwin same =>
      rewrite <- same then rule self selfTwin (here => inner here here byComputing) argument)
    goal
    goal
    byComputing

theorem followsPattern ∀
    (rule: ∀ (pself pselfTwin: PatternGoal → {Parse Item} Pattern) => PatternSelfFollows pself pselfTwin
      → PatternSelfFollows (patternRule pself) (patternRule pselfTwin)) (goal: PatternGoal):
    Parse.Follows SameCode PatternsAlike (() => pattern goal) (() => pattern goal) :=
  Parse.followsRecursiveWith
    [goals := Same]
    patternRule
    patternRule
    (pself pselfTwin inner argument argumentTwin same =>
      rewrite <- same then rule pself pselfTwin (here => inner here here byComputing) argument)
    goal
    goal
    byComputing

-- Trees built from alike parts.

theorem walkExprsAlike ∀ (items others: List Expr)
    (alike: List.All2 ExprsAlike items others):
    walkExprs blankPure items = walkExprs blankPure others :=
  match items, others with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] =>
      let (head, rest) := alike
      calc walkExprs blankPure [x, ..xs]
        _ = [x.walk blankPure, ..walkExprs blankPure xs] := byComputing
        _ = [y.walk blankPure, ..walkExprs blankPure ys] := rewrite head, walkExprsAlike xs ys rest
        _ = walkExprs blankPure [y, ..ys] := byComputing

theorem alikeAtom ∀ (kind: Tok) (word twin: Word)
    (words: WordsAlike word twin):
    ExprsAlike (Atom kind word) (Atom kind twin) :=
  calc (Atom kind word).walk blankPure
    _ = Atom kind word.blank := byComputing
    _ = Atom kind twin.blank := rewrite words
    _ = (Atom kind twin).walk blankPure := byComputing

theorem alikePrefix ∀ (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin):
    ExprsAlike (Prefix operator operand) (Prefix operatorTwin operandTwin) :=
  calc (Prefix operator operand).walk blankPure
    _ = Prefix operator.blank (operand.walk blankPure) := byComputing
    _ = Prefix operatorTwin.blank (operandTwin.walk blankPure) := rewrite operators, operands
    _ = (Prefix operatorTwin operandTwin).walk blankPure := byComputing

theorem alikeParen ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (inner innerTwin: Expr)
    (inners: ExprsAlike inner innerTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (Paren open inner close) (Paren openTwin innerTwin closeTwin) :=
  calc (Paren open inner close).walk blankPure
    _ = Paren open.blank (inner.walk blankPure) close.blank := byComputing
    _ = Paren openTwin.blank (innerTwin.walk blankPure) closeTwin.blank := rewrite opens, inners, closes
    _ = (Paren openTwin innerTwin closeTwin).walk blankPure := byComputing

theorem alikeAnnotation ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (colon colonTwin: Word)
    (colons: WordsAlike colon colonTwin) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike
      (Annotation open value colon annotation close)
      (Annotation openTwin valueTwin colonTwin annotationTwin closeTwin) :=
  calc (Annotation open value colon annotation close).walk blankPure
    _ = Annotation open.blank (value.walk blankPure) colon.blank (annotation.walk blankPure) close.blank := byComputing
    _ = Annotation openTwin.blank
        (valueTwin.walk blankPure)
        colonTwin.blank
        (annotationTwin.walk blankPure)
        closeTwin.blank := rewrite opens, values, colons, annotations, closes
    _ = (Annotation openTwin valueTwin colonTwin annotationTwin closeTwin).walk blankPure := byComputing

theorem alikeTuple ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items itemsTwin: List Expr)
    (alike: List.All2 ExprsAlike items itemsTwin) (trailing trailingTwin: Bool)
    (trailings: trailing = trailingTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (Tuple open items trailing close) (Tuple openTwin itemsTwin trailingTwin closeTwin) :=
  calc (Tuple open items trailing close).walk blankPure
    _ = Tuple open.blank (walkExprs blankPure items) trailing close.blank := byComputing
    _ = Tuple openTwin.blank (walkExprs blankPure itemsTwin) trailingTwin closeTwin.blank :=
      rewrite opens, walkExprsAlike items itemsTwin alike, trailings, closes
    _ = (Tuple openTwin itemsTwin trailingTwin closeTwin).walk blankPure := byComputing

theorem alikeListOf ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items itemsTwin: List Expr)
    (alike: List.All2 ExprsAlike items itemsTwin) (trailing trailingTwin: Bool)
    (trailings: trailing = trailingTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (ListOf open items trailing close) (ListOf openTwin itemsTwin trailingTwin closeTwin) :=
  calc (ListOf open items trailing close).walk blankPure
    _ = ListOf open.blank (walkExprs blankPure items) trailing close.blank := byComputing
    _ = ListOf openTwin.blank (walkExprs blankPure itemsTwin) trailingTwin closeTwin.blank :=
      rewrite opens, walkExprsAlike items itemsTwin alike, trailings, closes
    _ = (ListOf openTwin itemsTwin trailingTwin closeTwin).walk blankPure := byComputing

theorem alikeSpread ∀ (dots dotsTwin: Word)
    (dotted: WordsAlike dots dotsTwin) (list listTwin: Expr)
    (lists: ExprsAlike list listTwin):
    ExprsAlike (Spread dots list) (Spread dotsTwin listTwin) :=
  calc (Spread dots list).walk blankPure
    _ = Spread dots.blank (list.walk blankPure) := byComputing
    _ = Spread dotsTwin.blank (listTwin.walk blankPure) := rewrite dotted, lists
    _ = (Spread dotsTwin listTwin).walk blankPure := byComputing

-- Atoms.

theorem followsWordAtom ∀ (kind: Tok): Parse.Follows SameCode ExprsAlike (() => wordAtom kind) (() => wordAtom kind) :=
  Parse.followsMap (spelled => Atom kind spelled) (spelled => Atom kind spelled) followsBump (spelled twin words =>
    alikeAtom kind spelled twin words)

theorem followsNumberAfter ∀ (minus minusTwin: Word)
    (minuses: WordsAlike minus minusTwin) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => numberAfter minus items) (() => numberAfter minusTwin others) :=
  let kinds: numberKind items = numberKind others := deafOfStripped numberKind numberKindDeaf items others same
  Parse.followsMap
    (digits => Prefix minus (Atom (numberKind items) digits))
    (digits => Prefix minusTwin (Atom (numberKind others) digits))
    followsBump
    (digits digitsTwin numbers =>
      alikePrefix minus minusTwin minuses _ _
        (rewrite kinds then alikeAtom (numberKind others) digits digitsTwin numbers))

theorem followsNegativeNumber: Parse.Follows SameCode ExprsAlike (() => negativeNumber()) (() => negativeNumber()) :=
  Parse.followsThen followsBump (minus minusTwin minuses =>
    Parse.followsThen followsLeft (seen seenTwin same => followsNumberAfter minus minusTwin minuses seen seenTwin same))

-- Comma lists.

theorem followsCommaListFrom ∀ [alike: a → b → Prop] (modes: Modes) (ends endsTwin: Nat → {Parse Item} Bool)
    (endsFollow: ∀ (count: Nat) => Parse.Follows SameCode Same (() => ends count) (() => endsTwin count))
    (next: () → {Parse Item} a) (nextTwin: () → {Parse Item} b)
    (nexts: Parse.Follows SameCode alike next nextTwin)
    (fuel count: Nat) (current: a) (currentTwin: b) (currents: alike current currentTwin)
    (found: List a) (foundTwin: List b)
    (founds: List.All2 alike found foundTwin):
    Parse.Follows SameCode
      (PairAlike (List.All2 alike) Same)
      (() => commaListFrom fuel modes ends next count current found)
      (() => commaListFrom fuel modes endsTwin nextTwin count currentTwin foundTwin) :=
  let sofar: List.All2 alike [current, ..found] [currentTwin, ..foundTwin] := Both currents founds
  let done: PairAlike (List.All2 alike) Same ([current, ..found].reverse, False) (
    [currentTwin, ..foundTwin].reverse,
    False
  ) :=
    (List.all2Reverse [current, ..found] [currentTwin, ..foundTwin] sofar, byComputing)
  followsThenEq (followsPeek modes) (seen =>
    match fuel, seen with
      | Succ more, Some kind =>
        match kind == Comma with
          | True => Parse.followsThen followsBump (comma commaTwin commas =>
            followsThenEq (endsFollow count) (stop =>
              match stop with
                | True =>
                  Parse.followsDone (List.all2Reverse [current, ..found] [currentTwin, ..foundTwin] sofar, byComputing)
                | False => Parse.followsThen nexts (value valueTwin values =>
                  followsCommaListFrom modes ends endsTwin endsFollow next nextTwin nexts more
                    (count + 1)
                    value
                    valueTwin
                    values
                    [current, ..found]
                    [currentTwin, ..foundTwin]
                    sofar)))
          | False => Parse.followsDone done
      | Succ more, None => Parse.followsDone done
      | Zero, _ => Parse.followsDone done)

theorem followsCommaList ∀ [alike: a → b → Prop] (modes: Modes) (ends endsTwin: Nat → {Parse Item} Bool)
    (endsFollow: ∀ (count: Nat) => Parse.Follows SameCode Same (() => ends count) (() => endsTwin count))
    (next: () → {Parse Item} a) (nextTwin: () → {Parse Item} b)
    (nexts: Parse.Follows SameCode alike next nextTwin)
    (fuel: Nat) (current: a) (currentTwin: b) (currents: alike current currentTwin) (found: List a) (foundTwin: List b)
    (founds: List.All2 alike found foundTwin):
    Parse.Follows SameCode
      (PairAlike (List.All2 alike) Same)
      (() => commaList fuel modes ends next current found)
      (() => commaList fuel modes endsTwin nextTwin currentTwin foundTwin) :=
  followsCommaListFrom modes ends endsTwin endsFollow next nextTwin nexts fuel 1 current currentTwin currents found
      foundTwin founds

-- Brackets: `( … )`, tuples and annotations.

theorem followsParenClose ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin):
    Parse.Follows SameCode ExprsAlike (() => parenClose inner open first) (() => parenClose inner openTwin firstTwin) :=
  Parse.followsMap
    (close => Paren open first close)
    (close => Paren openTwin firstTwin close)
    (followsExpect inner RParen "`)`")
    (close closeTwin closes => alikeParen open openTwin opens first firstTwin firsts close closeTwin closes)

theorem followsAnnotatedEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (colon colonTwin: Word)
    (colons: WordsAlike colon colonTwin) (annotation annotationTwin: Expr)
    (annotations: ExprsAlike annotation annotationTwin) (comma: Bool):
    Parse.Follows SameCode ExprsAlike (() => annotatedEnd inner open first colon annotation comma) (() =>
      annotatedEnd inner openTwin firstTwin colonTwin annotationTwin comma) :=
  match comma with
    | True => followsFatalAny tupleAnnotation (() => Syntax.fatal tupleAnnotation)
    | False =>
      Parse.followsMap
        (close => Annotation open first colon annotation close)
        (close => Annotation openTwin firstTwin colonTwin annotationTwin close)
        (followsExpect inner RParen "`)`")
        (close closeTwin closes =>
          alikeAnnotation open openTwin opens first firstTwin firsts colon colonTwin colons annotation annotationTwin
              annotations close closeTwin closes)

theorem followsAnnotated ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin):
    Parse.Follows SameCode ExprsAlike (() => annotated self inner open first) (() =>
      annotated selfTwin inner openTwin firstTwin) :=
  Parse.followsThen followsBump (colon colonTwin colons =>
    Parse.followsThen (followsFull knot inner) (annotation annotationTwin annotations =>
      followsThenEq (followsAt inner Comma) (comma =>
        followsAnnotatedEnd inner open openTwin opens first firstTwin firsts colon colonTwin colons annotation
            annotationTwin annotations comma)))

theorem followsTupleEnds ∀ (inner: Modes) (count: Nat):
    Parse.Follows SameCode Same (() => tupleEnds inner count) (() => tupleEnds inner count) :=
  followsThenEq (followsAt inner RParen) (closing => Parse.followsDone byComputing)

theorem followsTupleClose ∀ (modes: Modes):
    Parse.Follows SameCode WordsAlike (() => tupleClose modes) (() => tupleClose modes) :=
  followsThenEq (followsAt modes Colon) (annotatedHere =>
    match annotatedHere with
      | True => followsFatalAny tupleAnnotation (() => Syntax.fatal tupleAnnotation)
      | False => followsExpect modes RParen "`)`")

theorem followsTupleEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (pair pairTwin: (List Expr, Bool))
    (pairs: PairAlike (List.All2 ExprsAlike) Same pair pairTwin):
    Parse.Follows SameCode ExprsAlike (() => tupleEnd inner open pair) (() => tupleEnd inner openTwin pairTwin) :=
  match pair, pairTwin with
    | (items, trailing), (itemsTwin, trailingTwin) =>
      Parse.followsMap
        (close => Tuple open items trailing close)
        (close => Tuple openTwin itemsTwin trailingTwin close)
        (followsTupleClose inner)
        (close closeTwin closes =>
          alikeTuple open openTwin opens items itemsTwin pairs.left trailing trailingTwin pairs.right close closeTwin
              closes)

theorem followsTupleSecond ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin)
    (fuel: Nat) (second secondTwin: Expr)
    (seconds: ExprsAlike second secondTwin):
    Parse.Follows SameCode ExprsAlike (() => tupleSecond self inner open first fuel second) (() =>
      tupleSecond selfTwin inner openTwin firstTwin fuel secondTwin) :=
  Parse.followsThen
    (followsCommaListFrom inner
      (tupleEnds inner)
      (tupleEnds inner)
      (count => followsTupleEnds inner count)
      (() => full self inner)
      (() => full selfTwin inner)
      (followsFull knot inner)
      fuel
      2
      second
      secondTwin
      seconds
      [first]
      [firstTwin]
      (Both firsts Trivial))
    (pair pairTwin pairs => followsTupleEnd inner open openTwin opens pair pairTwin pairs)

theorem followsTupleRest ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin):
    Parse.Follows SameCode ExprsAlike (() => tupleRest self inner open first) (() =>
      tupleRest selfTwin inner openTwin firstTwin) :=
  followsThenEq followsLeftCount (fuel =>
    Parse.followsThen followsBump (comma commaTwin commas =>
      Parse.followsThen (followsFull knot inner) (second secondTwin seconds =>
        followsTupleSecond knot inner open openTwin opens first firstTwin firsts fuel second secondTwin seconds)))

theorem followsBracketedAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => bracketedAfter self inner open first seen) (() =>
      bracketedAfter selfTwin inner openTwin firstTwin seen) :=
  match seen with
    | Some kind =>
      match kind == Comma with
        | True => followsTupleRest knot inner open openTwin opens first firstTwin firsts
        | False =>
          match kind == Colon with
            | True => followsAnnotated knot inner open openTwin opens first firstTwin firsts
            | False => followsParenClose inner open openTwin opens first firstTwin firsts
    | None => followsParenClose inner open openTwin opens first firstTwin firsts

theorem followsBracketed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => bracketed self modes) (() => bracketed selfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen (followsFull knot modes.inBrackets) (first firstTwin firsts =>
      followsThenEq (followsPeek modes.inBrackets) (seen =>
        followsBracketedAfter knot modes.inBrackets open openTwin opens first firstTwin firsts seen)))

-- Lists: `[ … ]`.

theorem followsListSpread ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (dots dotsTwin: Word)
    (dotted: WordsAlike dots dotsTwin) (empty: Bool):
    Parse.Follows SameCode ExprsAlike (() => listSpread self modes dots empty) (() =>
      listSpread selfTwin modes dotsTwin empty) :=
  match empty with
    | True => followsFatalAny "expected a list after `..`, as in `[x, ..xs]`" (() =>
      Syntax.fatal "expected a list after `..`, as in `[x, ..xs]`")
    | False =>
      Parse.followsMap
        (list => Spread dots list)
        (list => Spread dotsTwin list)
        (followsFull knot modes)
        (list listTwin lists => alikeSpread dots dotsTwin dotted list listTwin lists)

theorem followsAtEither ∀ (modes: Modes) (wanted other: Tok):
    Parse.Follows SameCode Same (() => modes.at wanted || modes.at other) (() => modes.at wanted || modes.at other) :=
  followsThenEq (followsAt modes wanted) (here =>
    match here with
      | True => Parse.followsDone byComputing
      | False => followsAt modes other)

theorem followsListItem ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => listItem self modes) (() => listItem selfTwin modes) :=
  followsThenEq (followsAt modes DotDot) (spread =>
    match spread with
      | True => Parse.followsThen followsBump (dots dotsTwin dotted =>
        followsThenEq (followsAtEither modes Comma RBracket) (empty =>
          followsListSpread knot modes dots dotsTwin dotted empty))
      | False => followsFull knot modes)

theorem followsListItemsEnd ∀ [self selfTwin: Goal → {Parse Item} Expr] (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (pair pairTwin: (List Expr, Bool))
    (pairs: PairAlike (List.All2 ExprsAlike) Same pair pairTwin):
    Parse.Follows SameCode ExprsAlike (() => listItemsEnd self inner open pair) (() =>
      listItemsEnd selfTwin inner openTwin pairTwin) :=
  match pair, pairTwin with
    | (items, trailing), (itemsTwin, trailingTwin) =>
      Parse.followsMap
        (close => ListOf open items trailing close)
        (close => ListOf openTwin itemsTwin trailingTwin close)
        (followsExpect inner RBracket "`,` or `]`")
        (close closeTwin closes =>
          alikeListOf open openTwin opens items itemsTwin pairs.left trailing trailingTwin pairs.right close closeTwin
              closes)

theorem followsListItems ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin):
    Parse.Follows SameCode ExprsAlike (() => listItems self inner open) (() => listItems selfTwin inner openTwin) :=
  Parse.followsThen (followsListItem knot inner) (first firstTwin firsts =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsCommaList inner
            (count => inner.at RBracket)
            (count => inner.at RBracket)
            (count => followsAt inner RBracket)
            (() => listItem self inner)
            (() => listItem selfTwin inner)
            (followsListItem knot inner)
            (here.left + 1)
            first
            firstTwin
            firsts
            []
            []
            Trivial)
          (pair pairTwin pairs => followsListItemsEnd inner open openTwin opens pair pairTwin pairs)))

theorem followsListAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => listAfter self inner open seen) (() =>
      listAfter selfTwin inner openTwin seen) :=
  match seen with
    | Some kind =>
      match kind == RBracket with
        | True =>
          Parse.followsMap
            (close => ListOf open [] False close)
            (close => ListOf openTwin [] False close)
            followsBump
            (close closeTwin closes =>
              alikeListOf open openTwin opens [] [] Trivial False False byComputing close closeTwin closes)
        | False => followsListItems knot inner open openTwin opens
    | None => followsListItems knot inner open openTwin opens

theorem followsListExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => listExpr self modes) (() => listExpr selfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    followsThenEq (followsPeek modes.inBrackets) (seen =>
      followsListAfter knot modes.inBrackets open openTwin opens seen))

-- A call into another file's function, taken as a hypothesis.

theorem followsParenRest ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes)
    (rightSections: ∀ (inside: Nat) => Parse.Follows SameCode ExprsAlike (() => rightSection self modes inside) (() =>
      rightSection selfTwin modes inside)) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => parenRest self modes items) (() => parenRest selfTwin modes others) :=
  let operators: rightOperator items = rightOperator others :=
    deafOfStripped rightOperator rightOperatorDeaf items others same
  rewrite operators then
    match rightOperator others with
      | Some inside => rightSections inside
      | None => followsBracketed knot modes

theorem alikeUnit ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    ExprsAlike (Expr.Unit open close) (Expr.Unit openTwin closeTwin) :=
  calc (Expr.Unit open close).walk blankPure
    _ = Expr.Unit open.blank close.blank := byComputing
    _ = Expr.Unit openTwin.blank closeTwin.blank := rewrite opens, closes
    _ = (Expr.Unit openTwin closeTwin).walk blankPure := byComputing

theorem followsParenOther ∀ [self selfTwin: Goal → {Parse Item} Expr] (modes: Modes)
    (namedArguments: ∀ (closer: Tok) (closeText: Text) => Parse.Follows SameCode ExprsAlike
      (() => namedArgument self modes closer closeText)
      (() => namedArgument selfTwin modes closer closeText))
    (operatorSections: Parse.Follows SameCode ExprsAlike (() => operatorSection self modes) (() =>
      operatorSection selfTwin modes)) (second third: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => parenOther self modes second third) (() =>
      parenOther selfTwin modes second third) :=
  match isSome RParen second with
    | True => followsBumpThen (open => Expr.Unit open bump()) (open => Expr.Unit open bump()) (open openTwin opens =>
      Parse.followsMap
        (close => Expr.Unit open close)
        (close => Expr.Unit openTwin close)
        followsBump
        (close closeTwin closes => alikeUnit open openTwin opens close closeTwin closes))
    | False =>
      match isSome Lower second && isSome ColonEq third with
        | True => namedArguments RParen "`)`"
        | False => operatorSections

theorem followsParenAtom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes)
    (namedArguments: ∀ (closer: Tok) (closeText: Text) => Parse.Follows SameCode ExprsAlike
      (() => namedArgument self modes closer closeText)
      (() => namedArgument selfTwin modes closer closeText))
    (operatorSections: Parse.Follows SameCode ExprsAlike (() => operatorSection self modes) (() =>
      operatorSection selfTwin modes))
    (rightSections: ∀ (inside: Nat) => Parse.Follows SameCode ExprsAlike (() => rightSection self modes inside) (() =>
      rightSection selfTwin modes inside)):
    Parse.Follows SameCode ExprsAlike (() => parenAtom self modes) (() => parenAtom selfTwin modes) :=
  followsThenEq (followsPeekAt modes 1) (second =>
    followsThenEq (followsPeekAt modes 2) (third =>
      match parenOutside second third with
        | True => followsParenOther modes namedArguments operatorSections second third
        | False =>
          followsOn (seen => parenRest self modes seen) (seen => parenRest selfTwin modes seen) (seen seenTwin same =>
            followsParenRest knot modes rightSections seen seenTwin same)))

theorem followsBracketAtom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes)
    (namedArguments: ∀ (closer: Tok) (closeText: Text) => Parse.Follows SameCode ExprsAlike
      (() => namedArgument self modes closer closeText)
      (() => namedArgument selfTwin modes closer closeText)):
    Parse.Follows SameCode ExprsAlike (() => bracketAtom self modes) (() => bracketAtom selfTwin modes) :=
  followsThenEq (followsPeekAt modes 1) (second =>
    followsThenEq (followsPeekAt modes 2) (third =>
      match (isSome Lower second || isSome KwDecreasing second) && isSome ColonEq third with
        | True => namedArguments RBracket "`]`"
        | False => followsListExpr knot modes))

theorem wordsAlikeExample: WordsAlike witnessItem.leaf.word witnessSpaced.leaf.word :=
  wordsAlikeOfSame witnessItem witnessSpaced byComputing
