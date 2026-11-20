--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md): `followsF`, one lemma for each parser function of the first half of
--| `Syntax/Parser.sw`, says that `F` follows itself on alike arguments, by the pattern of `Syntax/FollowsBase.sw`.
--|
--| Covered (Parser.sw, in the order of the file):
--|
--| - the logic and the end of an operator expression: `andOrAhead`, `operatorExpr`, `opStart`, `opSection`,
--|   `opCompared`, `logicOf`, `logicLevel`, `logicAfter`, `opLogic`, `iffOf`, `opIffed`, `opSequence`, `opEnd`,
--|   `arrowEnd`, `semiExpr`, `semiAfter`, `logicChain`, `logicLinks`, `logicOn`, `logicLink`, `logicOperand`, `iff`,
--|   `iffAfter`, `iffRight`, `iffEnd`, `quantifierAhead`;
--| - pipes: `atPipe`, `pipeChain`, `pipesFrom` (with `pipesStep` and `pipesAfter` read through, and each also has
--|   its own lemma), `pipeFunction`, `pipeOperand`, `pipeSection`;
--| - comparisons: `cmpExpr`, `cmpFirst`, `cmpPiped`, `cmpOn`, `cmpKind`, `cmpCompare`, `cmpAfter`, `cmpIf`,
--|   `cmpSecond`, `cmpChain`, `pipedRange`, `pipedAt`, `pipedAfter`, `pipedEnd`, `membership`, `comparisonChain`,
--|   `chainAfter`, `chainLinks`, `chainOn`, `chainLink`;
--| - ranges: `rangeExpr`, `rangeFrom`, `rangeOn`, `rangeHigh`, `rangeEnd`, `rangeChained`;
--| - the arithmetic ladder: `appendExpr`, `operatorLinks`, `addExpr`, `mulExpr`;
--| - `unary`, `unaryOn`, `unarySome`, `unaryBar`, `unaryNext`;
--| - applications: `app`, `appAt`, `appHead`, `appCalls`, `appEnd`, `appliedTo`, `arguments`, `argumentStep`,
--|   `argument`, `argumentAt`, `argumentBrace`, `startsAtom`, `bareCases`.
--|
--| The boundary with `Syntax/FollowsForms.sw`: that file has everything before `andOrAhead` (the keyword
--| expressions, `exprPi`, `lambdaHere`, ...), the quantifiers, lambdas, `if`, `namedBinder` and `Modes.expectKeyword`
--| between `iffEnd` and `atPipe`, and every function from `atom` on (atoms, suffixes, records, `match`, clause
--| lambdas, patterns). Three look-aheads over the items left that are defined there or in Statements.sw are proved
--| here too, as short lemmas from the `…Deaf` facts in `Syntax/DeafProofs.sw`, so that no hypothesis is needed for
--| them: `lambdaHere` (`followsLambdaHere`), `matchesBarAhead` and `sequenceAhead`.
--|
--| Hypotheses. Each lemma takes the knot (`SelfFollows self selfTwin`), alike arguments, and the `Follows` fact of
--| each function in another file that it calls directly. Those facts are the definitions below, each for every
--| `modes` (the ladder calls the same function at changed modes, `modes.inBrackets` or a `sectionHead`); the
--| functions are in `Syntax/Parser.sw` and `Syntax/DeclParser.sw`, the facts are proved in `Syntax/FollowsForms.sw`
--| and its continuations, and `Syntax/FollowsParse.sw` supplies them. A lemma takes them as one tier record
--| (`AtomFacts` up to `QuantifierFacts`, below), the lowest that holds what it calls:
--|
--| - `AtomFollows`: `atom self modes True`;
--| - `BraceFollows`: `braceArgument self modes`;
--| - `MatchFollows`: `matchExpr self modes keyword` for alike keywords;
--| - `ClauseLambdaFollows`: `clauseLambda self modes keyword None ClauseMatches` for alike keywords;
--| - `LambdaFollows`: `lambda self modes None`;
--| - `IfFollows`: `ifExpr self modes indent keyword` for alike keywords;
--| - `QuantifierFollows`: `quantifier self modes`;
--| - `ResultTypeFollows`: `resultType self modes` (`Syntax/DeclParser.sw`).
--|
--| Nothing here reads a comment, and the only relation on a `Bool` that isn't equality, `Anything`, isn't used at
--| all: every `Bool` the ladder reads (`modes.at`, the look-aheads, `startsAtom`) is `Same` in the two runs. Items
--| the two runs compute from their own items (`negativeNumeral`, `sectionLineAt`, `pipeAheadOn`, `headKind`) are
--| proved equal with the `…Deaf` lemmas in `Syntax/DeafProofs.sw` and rewritten. A `match` that the parser writes
--| inside a lambda (the step of `operatorLinks`, of the loops) is not restated in a proof: restating gives a
--| different hidden function, so the loop's step is left to unify (`Parse.followsLoop _ _ …`).
--|
--| Helpers added here: `alikeInfix`, `alikeSection`, `alikeApp`, `alikeChain` (the trees), `linksAlike` (links
--| `List.All2 (PairAlike WordsAlike ExprsAlike)` to the equality that `Syntax/DeafProofs.sw`'s `leftNestedDeaf` and
--| friends take), `headKindDeaf`, and the look-aheads `followsStartsAtom`, `followsAndOrAhead`, `followsAtPipe`,
--| `followsHeadIndent`, `followsSequenceAhead`, `followsMatchesBarAhead`, `followsQuantifierAhead`,
--| `followsLambdaHere`, `followsAtUpperBrace`, `followsBareCases`.

namespace Syntax.FollowsLadder
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)

-- Trees built from alike parts.

theorem alikeInfix ∀ (kind: InfixKind) (left leftTwin: Expr)
    (lefts: ExprsAlike left leftTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (right rightTwin: Expr)
    (rights: ExprsAlike right rightTwin):
    ExprsAlike (Infix kind left operator right) (Infix kind leftTwin operatorTwin rightTwin) :=
  calc (Infix kind left operator right).walk blankPure
    _ = Infix kind (left.walk blankPure) operator.blank (right.walk blankPure) := byComputing
    _ = Infix kind (leftTwin.walk blankPure) operatorTwin.blank (rightTwin.walk blankPure) :=
      rewrite lefts, operators, rights
    _ = (Infix kind leftTwin operatorTwin rightTwin).walk blankPure := byComputing

theorem alikeSection ∀ (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ExprsAlike (Section body) (Section bodyTwin) :=
  calc (Section body).walk blankPure
    _ = Section (body.walk blankPure) := byComputing
    _ = Section (bodyTwin.walk blankPure) := rewrite bodies
    _ = (Section bodyTwin).walk blankPure := byComputing

theorem alikeApp ∀ (head headTwin: Expr)
    (heads: ExprsAlike head headTwin) (arguments argumentsTwin: List Expr)
    (alike: List.All2 ExprsAlike arguments argumentsTwin):
    ExprsAlike (App head arguments) (App headTwin argumentsTwin) :=
  calc (App head arguments).walk blankPure
    _ = App (head.walk blankPure) (walkExprs blankPure arguments) := byComputing
    _ = App (headTwin.walk blankPure) (walkExprs blankPure argumentsTwin) :=
      rewrite heads, walkExprsAlike arguments argumentsTwin alike
    _ = (App headTwin argumentsTwin).walk blankPure := byComputing

theorem linksAlike ∀ (links twins: List (Word, Expr))
    (alike: List.All2 (PairAlike WordsAlike ExprsAlike) links twins):
    blankLinks (walkLinks blankPure links) = blankLinks (walkLinks blankPure twins) :=
  match links, twins with
    | [], [] => byComputing
    | [(operator, next), ..rest], [(operatorTwin, nextTwin), ..restTwin] =>
      let (head, tail) := alike
      let sameOperator: operator.blank = operatorTwin.blank := head.left
      let sameNext: next.walk blankPure = nextTwin.walk blankPure := head.right
      calc blankLinks (walkLinks blankPure [(operator, next), ..rest])
        _ = [(operator.blank, next.walk blankPure), ..blankLinks (walkLinks blankPure rest)] := byComputing
        _ = [(operatorTwin.blank, nextTwin.walk blankPure), ..blankLinks (walkLinks blankPure restTwin)] :=
          rewrite sameOperator, sameNext, linksAlike rest restTwin tail
        _ = blankLinks (walkLinks blankPure [(operatorTwin, nextTwin), ..restTwin]) := byComputing

theorem alikeChain ∀ (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (rest restTwin: List (Word, Expr))
    (alike: List.All2 (PairAlike WordsAlike ExprsAlike) rest restTwin):
    ExprsAlike (Chain first rest) (Chain firstTwin restTwin) :=
  calc (Chain first rest).walk blankPure
    _ = Chain (first.walk blankPure) (blankLinks (walkLinks blankPure rest)) := byComputing
    _ = Chain (firstTwin.walk blankPure) (blankLinks (walkLinks blankPure restTwin)) :=
      rewrite firsts, linksAlike rest restTwin alike
    _ = (Chain firstTwin restTwin).walk blankPure := byComputing

-- The facts about other files' functions that the ladder calls directly, each as `Syntax/FollowsForms.sw` (or
-- `Syntax/FollowsStatements.sw`) states it.

def AtomFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => atom self modes True) (() => atom selfTwin modes True)

def BraceFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => braceArgument self modes) (() =>
    braceArgument selfTwin modes)

def MatchFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (keyword keywordTwin: Word) => WordsAlike keyword keywordTwin
    → Parse.Follows SameCode ExprsAlike (() => matchExpr self modes keyword) (() =>
      matchExpr selfTwin modes keywordTwin)

def ClauseLambdaFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (keyword keywordTwin: Word) => WordsAlike keyword keywordTwin
    → Parse.Follows SameCode ExprsAlike (() => clauseLambda self modes keyword None ClauseMatches) (() =>
      clauseLambda selfTwin modes keywordTwin None ClauseMatches)

def LambdaFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => lambda self modes None) (() =>
    lambda selfTwin modes None)

def IfFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (indent: Nat) (keyword keywordTwin: Word) => WordsAlike keyword keywordTwin
    → Parse.Follows SameCode ExprsAlike (() => ifExpr self modes indent keyword) (() =>
      ifExpr selfTwin modes indent keywordTwin)

def QuantifierFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => Syntax.quantifier self modes) (() =>
    Syntax.quantifier selfTwin modes)

def ResultTypeFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => resultType self modes) (() => resultType selfTwin modes)

-- The facts above in tiers: the expression ladder's lemmas take the lowest tier that holds what they call, so each passes
-- on one record in place of a run of hypotheses. Every field is the `Follows` fact its name says, for the same `self` and
-- `selfTwin`; `.below` reaches the tier under. `atomFactsOf` and the builders after it (in `FollowsForms`) make a tier
-- from the facts about the other files' functions.

--| The tier 0 of the ladder's facts: the knot, atoms, and `C { … }` arguments, which every expression lemma needs.
type AtomFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  knot: SelfFollows self selfTwin,
  atoms: AtomFollows self selfTwin,
  braces: BraceFollows self selfTwin
}

--| The tier 1 of the ladder's facts: `match` and clause lambdas, which the unary level reads.
type MatchFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: AtomFacts self selfTwin,
  matches: MatchFollows self selfTwin,
  clauses: ClauseLambdaFollows self selfTwin
}

--| The tier 2 of the ladder's facts: lambdas.
type LambdaFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: MatchFacts self selfTwin,
  lambdas: LambdaFollows self selfTwin
}

--| The tier 3 of the ladder's facts: `if` expressions.
type IfFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: LambdaFacts self selfTwin,
  ifs: IfFollows self selfTwin
}

--| The tier 4 of the ladder's facts, all of them: quantifiers and result types.
type QuantifierFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: IfFacts self selfTwin,
  quantifiers: QuantifierFollows self selfTwin,
  results: ResultTypeFollows self selfTwin
}

-- Look-aheads over the items left.

theorem followsStartsAtom ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => startsAtom modes) (() => startsAtom modes) :=
  followsLook (startsAtomOn modes) (startsAtomOnDeaf modes)

theorem followsAndOrAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => andOrAhead modes) (() => andOrAhead modes) :=
  followsLook (andOrOn modes) (andOrOnDeaf modes)

theorem followsAtPipe ∀ (modes: Modes): Parse.Follows SameCode Same (() => atPipe modes) (() => atPipe modes) :=
  followsLook (atPipeOn modes) (atPipeOnDeaf modes)

theorem followsHeadIndent: Parse.Follows SameCode Same (() => headIndent()) (() => headIndent()) :=
  followsLook headIndentOn headIndentOnDeaf

theorem followsSequenceAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => sequenceAhead modes) (() => sequenceAhead modes) :=
  followsLook (sequenceOn modes) (sequenceOnDeaf modes)

theorem followsMatchesBarAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => matchesBarAhead modes) (() => matchesBarAhead modes) :=
  followsLook (matchesBarOn modes) (matchesBarOnDeaf modes)

theorem followsQuantifierAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => quantifierAhead modes) (() => quantifierAhead modes) :=
  followsAtEither modes KwExists KwForall

theorem followsLambdaHere ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => lambdaHere modes) (() => lambdaHere modes) :=
  followsThenEq
    [p := () => Parse.mark().left]
    [q := () => Parse.mark().left]
    [j := fuel => lambdaAhead modes (fuel + 1) left()]
    [k := fuel => lambdaAhead modes (fuel + 1) left()]
    followsLeftCount
    (fuel => followsLook (lambdaAhead modes (fuel + 1)) (lambdaAheadDeaf modes (fuel + 1)))

theorem followsAtUpperBrace ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => modes.at Upper && isSome LBrace (modes.peekAt 1)) (() =>
      modes.at Upper && isSome LBrace (modes.peekAt 1)) :=
  followsThenEq (followsAt modes Upper) (here =>
    match here with
      | True => followsThenEq (followsPeekAt modes 1) (seen => Parse.followsDone byComputing)
      | False => Parse.followsDone byComputing)

-- Applications.

theorem followsArgumentBrace ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (modes: Modes) (brace: Bool):
    Parse.Follows SameCode ExprsAlike (() => argumentBrace self modes brace) (() =>
      argumentBrace selfTwin modes brace) :=
  match brace with
    | True => braces modes
    | False => knot { modes, level = LevelArgument }

theorem followsArgumentAt ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => argumentAt self modes items) (() => argumentAt selfTwin modes others) :=
  let lines: sectionLineAt modes items = sectionLineAt modes others :=
    deafOfStripped (sectionLineAt modes) (sectionLineAtDeaf modes) items others same
  rewrite lines then
    match sectionLineAt modes others with
      | True => followsFatalAny "a line can't start with a method section" (() =>
        Syntax.fatal "a line can't start with a method section")
      | False => followsThenEq (followsAtUpperBrace modes) (brace => followsArgumentBrace knot braces modes brace)

theorem followsArgument ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => argument self modes) (() => argument selfTwin modes) :=
  followsOn (seen => argumentAt self modes seen) (seen => argumentAt selfTwin modes seen) (seen others same =>
    followsArgumentAt knot braces modes seen others same)

theorem followsArgumentStep ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (modes: Modes) (starts: Bool):
    Parse.Follows SameCode (Option.Alike ExprsAlike) (() => argumentStep self modes starts) (() =>
      argumentStep selfTwin modes starts) :=
  match starts with
    | True => Parse.followsMap (x => Some x) (x => Some x) (followsArgument knot braces modes) (x y alike => alike)
    | False => Parse.followsDone Trivial

theorem followsArguments ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 ExprsAlike) (() => arguments self modes) (() => arguments selfTwin modes) :=
  Parse.followsLoop
    [step := (() => argumentStep self modes (startsAtom modes))]
    [stepTwin := (() => argumentStep selfTwin modes (startsAtom modes))]
    (followsThenEq (followsStartsAtom modes) (starts => followsArgumentStep knot braces modes starts))

theorem followsAppliedTo ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (modes: Modes) (head headTwin: Expr)
    (heads: ExprsAlike head headTwin):
    Parse.Follows SameCode ExprsAlike (() => appliedTo self modes head) (() => appliedTo selfTwin modes headTwin) :=
  Parse.followsThen (followsArgument knot braces modes) (first firstTwin firsts =>
    Parse.followsThen (followsArguments knot braces modes) (more moreTwin mores =>
      Parse.followsDone (alikeApp head headTwin heads [first, ..more] [firstTwin, ..moreTwin] (Both firsts mores))))

theorem followsAppEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (modes: Modes) (section: Bool) (head headTwin: Expr)
    (heads: ExprsAlike head headTwin) (applies: Bool):
    Parse.Follows SameCode ExprsAlike (() => appEnd self modes section head applies) (() =>
      appEnd selfTwin modes section headTwin applies) :=
  match applies with
    | True =>
      Parse.followsMap
        (applied => sectioned section applied)
        (applied => sectioned section applied)
        (followsAppliedTo knot braces modes head headTwin heads)
        (applied appliedTwin alike => sectionedDeaf section applied appliedTwin alike)
    | False => Parse.followsDone (sectionedDeaf section head headTwin heads)

theorem followsAppCalls ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (modes: Modes) (section: Bool) (head headTwin: Expr)
    (heads: ExprsAlike head headTwin):
    Parse.Follows SameCode ExprsAlike (() => appCalls self modes section head) (() =>
      appCalls selfTwin modes section headTwin) :=
  followsThenEq (followsStartsAtom modes) (applies =>
    followsAppEnd knot braces modes section head headTwin heads applies)

theorem followsAppHead ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: AtomFacts self selfTwin)
    (modes: Modes) (section: Bool):
    Parse.Follows SameCode ExprsAlike (() => appHead self modes section) (() => appHead selfTwin modes section) :=
  Parse.followsThen (facts.atoms modes) (head headTwin heads =>
    followsAppCalls facts.knot facts.braces modes section head headTwin heads)

theorem followsAppAt ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: AtomFacts self selfTwin)
    (modes: Modes) (start: Nat):
    Parse.Follows SameCode ExprsAlike (() => appAt self modes start) (() => appAt selfTwin modes start) :=
  followsThenEq
    [p := () => modes.at Dot]
    [q := () => modes.at Dot]
    [j := here => appHead self modes (here && modes.sectionHead != Some start)]
    [k := here => appHead selfTwin modes (here && modes.sectionHead != Some start)]
    (followsAt modes Dot)
    (here => followsAppHead facts modes (here && modes.sectionHead != Some start))

theorem followsApp ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: AtomFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => app self modes) (() => app selfTwin modes) :=
  followsThenEq followsOffset (start => followsAppAt facts modes start)

-- Unary operators.

theorem headKindDeaf ∀ (items: List Item): items.head.map Item.kind = (items.map Item.stripped).head.map Item.kind :=
  match items with | [] | [_, .._] => byComputing

theorem followsUnaryNext ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: AtomFacts self selfTwin)
    (modes: Modes) (kind: Tok) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => unaryNext self modes kind items) (() =>
      unaryNext selfTwin modes kind others) :=
  let negatives: negativeNumeral items = negativeNumeral others :=
    deafOfStripped negativeNumeral negativeNumeralDeaf items others same
  rewrite negatives then
    match kind == Minus && negativeNumeral others with
      | True => followsApp facts modes
      | False =>
        match kind == Minus || kind == Bang with
          | True => Parse.followsThen followsBump (operator operatorTwin operators =>
            Parse.followsMap
              (operand => Prefix operator operand)
              (operand => Prefix operatorTwin operand)
              (facts.knot { modes, level = LevelUnary })
              (operand operandTwin operands =>
                alikePrefix operator operatorTwin operators operand operandTwin operands))
          | False => followsApp facts modes

theorem followsUnaryBar ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (atoms: AtomFollows self selfTwin)
    (braces: BraceFollows self selfTwin)
    (clauses: ClauseLambdaFollows self selfTwin)
    (modes: Modes) (kind: Tok) (bar: Bool):
    Parse.Follows SameCode ExprsAlike (() => unaryBar self modes kind bar) (() => unaryBar selfTwin modes kind bar) :=
  match bar with
    | True => Parse.followsThen followsBump (keyword keywordTwin keywords => clauses modes keyword keywordTwin keywords)
    | False =>
      followsOn
        (seen => unaryNext self modes kind seen)
        (seen => unaryNext selfTwin modes kind seen)
        (seen others same =>
          followsUnaryNext { knot = knot, atoms = atoms, braces = braces } modes kind seen others same)

theorem followsUnarySome ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin)
    (modes: Modes) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => unarySome self modes kind) (() => unarySome selfTwin modes kind) :=
  match kind == KwMatch with
    | True =>
      Parse.followsThen followsBump (keyword keywordTwin keywords => facts.matches modes keyword keywordTwin keywords)
    | False => followsThenEq (followsMatchesBarAhead modes) (bar =>
      followsUnaryBar facts.below.knot facts.below.atoms facts.below.braces facts.clauses modes kind bar)

theorem followsUnaryOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => unaryOn self modes seen) (() => unaryOn selfTwin modes seen) :=
  match seen with
    | Some kind => followsUnarySome facts modes kind
    | None => followsApp facts.below modes

theorem followsUnary ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => unary self modes) (() => unary selfTwin modes) :=
  followsPeeked modes (seen => unaryOn self modes seen) (seen => unaryOn selfTwin modes seen) (seen =>
    followsUnaryOn facts modes seen)

-- Binary operators by precedence.

theorem followsOperatorLinks ∀ (modes: Modes) (takes: Tok → Bool) (operand operandTwin: () → {Parse Item} Expr)
    (operands: Parse.Follows SameCode ExprsAlike operand operandTwin):
    Parse.Follows SameCode
      (List.All2 (PairAlike WordsAlike ExprsAlike))
      (() => operatorLinks modes takes operand)
      (() => operatorLinks modes takes operandTwin) :=
  Parse.followsLoop
    (followsThenEq (followsPeek modes) (seen =>
      match seen with
        | Some kind =>
          match takes kind with
            | True => Parse.followsThen followsBump (operator operatorTwin operators =>
              Parse.followsMap
                (value => Some (operator, value))
                (value => Some (operatorTwin, value))
                operands
                (value valueTwin values => (operators, values)))
            | False => Parse.followsDone Trivial
        | None => Parse.followsDone Trivial))

theorem followsMulExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => mulExpr self modes) (() => mulExpr selfTwin modes) :=
  Parse.followsThen (followsUnary facts modes) (first firstTwin firsts =>
    Parse.followsThen
      (followsOperatorLinks modes
        (kind => kind == Star || kind == Slash || kind == Percent)
        (() => unary self modes)
        (() => unary selfTwin modes)
        (followsUnary facts modes))
      (links linksTwin alike =>
        Parse.followsDone (leftNestedDeaf first firstTwin links linksTwin firsts (linksAlike links linksTwin alike))))

theorem followsAddExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => addExpr self modes) (() => addExpr selfTwin modes) :=
  Parse.followsThen (followsMulExpr facts modes) (first firstTwin firsts =>
    Parse.followsThen
      (followsOperatorLinks modes
        (kind => kind == Plus || kind == Minus)
        (() => mulExpr self modes)
        (() => mulExpr selfTwin modes)
        (followsMulExpr facts modes))
      (links linksTwin alike =>
        Parse.followsDone (leftNestedDeaf first firstTwin links linksTwin firsts (linksAlike links linksTwin alike))))

theorem followsAppendExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => appendExpr self modes) (() => appendExpr selfTwin modes) :=
  Parse.followsThen (followsAddExpr facts modes) (first firstTwin firsts =>
    Parse.followsThen
      (followsOperatorLinks modes
        (kind => kind == PlusPlus)
        (() => addExpr self modes)
        (() => addExpr selfTwin modes)
        (followsAddExpr facts modes))
      (links linksTwin alike =>
        Parse.followsDone (rightNestedDeaf first firstTwin links linksTwin firsts (linksAlike links linksTwin alike))))

-- Ranges.

theorem followsRangeChained ∀ (low lowTwin: Expr)
    (lows: ExprsAlike low lowTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (high highTwin: Expr)
    (highs: ExprsAlike high highTwin) (chained: Bool):
    Parse.Follows SameCode ExprsAlike (() => rangeChained low operator high chained) (() =>
      rangeChained lowTwin operatorTwin highTwin chained) :=
  match chained with
    | True => followsFatalAny "ranges don't chain" (() => Syntax.fatal "ranges don't chain")
    | False =>
      Parse.followsDone (alikeInfix InfixRange low lowTwin lows operator operatorTwin operators high highTwin highs)

theorem followsRangeEnd ∀ (modes: Modes) (low lowTwin: Expr)
    (lows: ExprsAlike low lowTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (high highTwin: Expr)
    (highs: ExprsAlike high highTwin):
    Parse.Follows SameCode ExprsAlike (() => rangeEnd modes low operator high) (() =>
      rangeEnd modes lowTwin operatorTwin highTwin) :=
  followsThenEq (followsAtEither modes DotDotLt DotDotEq) (chained =>
    followsRangeChained low lowTwin lows operator operatorTwin operators high highTwin highs chained)

theorem followsRangeHigh ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin)
    (modes: Modes) (low lowTwin: Expr)
    (lows: ExprsAlike low lowTwin):
    Parse.Follows SameCode ExprsAlike (() => rangeHigh self modes low) (() => rangeHigh selfTwin modes lowTwin) :=
  Parse.followsThen followsBump (operator operatorTwin operators =>
    Parse.followsThen (followsAppendExpr facts modes) (high highTwin highs =>
      followsRangeEnd modes low lowTwin lows operator operatorTwin operators high highTwin highs))

theorem followsRangeOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin)
    (modes: Modes) (low lowTwin: Expr)
    (lows: ExprsAlike low lowTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => rangeOn self modes low seen) (() => rangeOn selfTwin modes lowTwin seen) :=
  match seen with
    | Some kind =>
      match kind == DotDot with
        | True => followsFatalAny _ (() =>
          Syntax.fatal "a range is `a ..< b` (up to, not including, `b`) or `a ..= b` (through `b`)")
        | False =>
          match kind == DotDotLt || kind == DotDotEq with
            | True => followsRangeHigh facts modes low lowTwin lows
            | False => Parse.followsDone lows
    | None => Parse.followsDone lows

theorem followsRangeFrom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin)
    (modes: Modes) (low lowTwin: Expr)
    (lows: ExprsAlike low lowTwin):
    Parse.Follows SameCode ExprsAlike (() => rangeFrom self modes low) (() => rangeFrom selfTwin modes lowTwin) :=
  followsPeeked modes (seen => rangeOn self modes low seen) (seen => rangeOn selfTwin modes lowTwin seen) (seen =>
    followsRangeOn facts modes low lowTwin lows seen)

theorem followsRangeExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => rangeExpr self modes) (() => rangeExpr selfTwin modes) :=
  Parse.followsThen (followsAppendExpr facts modes) (low lowTwin lows => followsRangeFrom facts modes low lowTwin lows)

-- Pipes.

theorem followsPipeSection ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin)
    (modes: Modes) (start: Nat) (section: Bool):
    Parse.Follows SameCode ExprsAlike (() => pipeSection self modes start section) (() =>
      pipeSection selfTwin modes start section) :=
  match section with
    | True =>
      Parse.followsMap
        (operand => Section operand)
        (operand => Section operand)
        (followsAppendExpr facts { modes | sectionHead = Some start })
        (operand operandTwin alike => alikeSection operand operandTwin alike)
    | False =>
      Parse.followsMap
        (operand => operand)
        (operand => operand)
        (followsAppendExpr facts modes)
        (operand operandTwin alike => alike)

theorem followsPipeOperand ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: MatchFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => pipeOperand self modes) (() => pipeOperand selfTwin modes) :=
  followsThenEq followsOffset (start =>
    followsThenEq (followsAt modes Dot) (section => followsPipeSection facts modes start section))

theorem followsPipeFunction ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (lambdas: Bool):
    Parse.Follows SameCode ExprsAlike (() => pipeFunction self modes lambdas) (() =>
      pipeFunction selfTwin modes lambdas) :=
  match lambdas with
    | True => facts.lambdas modes
    | False => followsPipeOperand facts.below modes

theorem followsPipesFrom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (indent fuel: Nat) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    Parse.Follows SameCode ExprsAlike (() => pipesFrom fuel self modes indent value) (() =>
      pipesFrom fuel selfTwin modes indent valueTwin) :=
  followsOn
    (seen => pipesStep fuel self modes indent value (pipeAheadOn modes indent seen))
    (seen => pipesStep fuel selfTwin modes indent valueTwin (pipeAheadOn modes indent seen))
    (seen others same =>
      rewrite deafOfStripped (pipeAheadOn modes indent) (pipeAheadOnDeaf modes indent) seen others same then
        match fuel with
          | Zero => Parse.followsDone values
          | Succ more =>
            match pipeAheadOn modes indent others with
              | True => Parse.followsThen followsBump (operator operatorTwin operators =>
                followsThenEq (followsLambdaHere modes) (lambdas =>
                  Parse.followsThen (followsPipeFunction facts modes lambdas) (function functionTwin functions =>
                    followsPipesFrom facts modes indent more
                      (Infix InfixPipe value operator function)
                      (Infix InfixPipe valueTwin operatorTwin functionTwin)
                      (alikeInfix InfixPipe value valueTwin values operator operatorTwin operators function functionTwin
                          functions))))
              | False => Parse.followsDone values)

theorem followsPipeChain ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (indent: Nat) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    Parse.Follows SameCode ExprsAlike (() => pipeChain self modes indent value) (() =>
      pipeChain selfTwin modes indent valueTwin) :=
  followsThenEq
    [p := () => Parse.mark().left]
    [q := () => Parse.mark().left]
    [j := fuel => pipesFrom (fuel + 1) self modes indent value]
    [k := fuel => pipesFrom (fuel + 1) selfTwin modes indent valueTwin]
    followsLeftCount
    (fuel => followsPipesFrom facts modes indent (fuel + 1) value valueTwin values)

theorem followsPipedEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (indent: Nat) (range rangeTwin: Expr)
    (ranges: ExprsAlike range rangeTwin) (pipe: Bool):
    Parse.Follows SameCode ExprsAlike (() => pipedEnd self modes indent range pipe) (() =>
      pipedEnd selfTwin modes indent rangeTwin pipe) :=
  match pipe with
    | True => followsPipeChain facts modes indent range rangeTwin ranges
    | False => Parse.followsDone ranges

theorem followsPipedAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (indent: Nat) (range rangeTwin: Expr)
    (ranges: ExprsAlike range rangeTwin):
    Parse.Follows SameCode ExprsAlike (() => pipedAfter self modes indent range) (() =>
      pipedAfter selfTwin modes indent rangeTwin) :=
  followsThenEq (followsAtPipe modes) (pipe => followsPipedEnd facts modes indent range rangeTwin ranges pipe)

theorem followsPipedAt ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (indent: Nat):
    Parse.Follows SameCode ExprsAlike (() => pipedAt self modes indent) (() => pipedAt selfTwin modes indent) :=
  Parse.followsThen (followsRangeExpr facts.below modes) (range rangeTwin ranges =>
    followsPipedAfter facts modes indent range rangeTwin ranges)

theorem followsPipedRange ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => pipedRange self modes) (() => pipedRange selfTwin modes) :=
  followsThenEq followsHeadIndent (indent => followsPipedAt facts modes indent)

-- Comparisons.

theorem followsMembership ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (first: Option Tok) (element elementTwin: Expr)
    (elements: ExprsAlike element elementTwin):
    Parse.Follows SameCode ExprsAlike (() => membership self modes first element) (() =>
      membership selfTwin modes first elementTwin) :=
  match isSome Bang first with
    | True => followsFatalAny "`!` here applies to the element, not to the membership test" (() =>
      Syntax.fatal "`!` here applies to the element, not to the membership test")
    | False => Parse.followsThen followsBump (operator operatorTwin operators =>
      Parse.followsMap
        (range => Infix InfixMembership element operator range)
        (range => Infix InfixMembership elementTwin operatorTwin range)
        (followsPipedRange facts modes)
        (range rangeTwin ranges =>
          alikeInfix InfixMembership element elementTwin elements operator operatorTwin operators range rangeTwin
              ranges))

theorem followsChainLink ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (descending: Bool) (kind: Tok):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike ExprsAlike))
      (() => chainLink self modes descending kind)
      (() => chainLink selfTwin modes descending kind) :=
  match kind == Equals || kind == EqEq with
    | True => followsFatalAny _ (() => Syntax.fatal (chainRefused kind))
    | False =>
      match kind == NotEq with
        | True => followsFatalAny _ (() => Syntax.fatal "`!=` can't be part of a chain of comparisons")
        | False =>
          match kind == KwIn || kind == NotIn with
            | True => followsFatalAny _ (() => Syntax.fatal "`in` can't be part of a chain of comparisons")
            | False =>
              match !(kind == Lt || kind == Le || isDescending kind) with
                | True => Parse.followsDone Trivial
                | False =>
                  match isDescending kind != descending with
                    | True => followsFatalAny _ (() =>
                      Syntax.fatal "a chain of comparisons goes one way: `<` and `<=` can't be mixed with `>` and `>=`")
                    | False => Parse.followsThen followsBump (operator operatorTwin operators =>
                      Parse.followsMap
                        (operand => Some (operator, operand))
                        (operand => Some (operatorTwin, operand))
                        (followsPipedRange facts modes)
                        (operand operandTwin operands => (operators, operands)))

theorem followsChainOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (descending: Bool) (seen: Option Tok):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike ExprsAlike))
      (() => chainOn self modes descending seen)
      (() => chainOn selfTwin modes descending seen) :=
  match seen with
    | Some kind => followsChainLink facts modes descending kind
    | None => Parse.followsDone Trivial

theorem followsChainLinks ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (descending: Bool):
    Parse.Follows SameCode
      (List.All2 (PairAlike WordsAlike ExprsAlike))
      (() => Syntax.chainLinks self modes descending)
      (() => Syntax.chainLinks selfTwin modes descending) :=
  Parse.followsLoop
    (followsPeeked modes
      (seen => chainOn self modes descending seen)
      (seen => chainOn selfTwin modes descending seen)
      (seen => followsChainOn facts modes descending seen))

theorem followsChainAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (second secondTwin: Expr)
    (seconds: ExprsAlike second secondTwin) (descending: Bool):
    Parse.Follows SameCode ExprsAlike (() => chainAfter self modes first operator second descending) (() =>
      chainAfter selfTwin modes firstTwin operatorTwin secondTwin descending) :=
  Parse.followsThen (followsChainLinks facts modes descending) (links linksTwin alike =>
    Parse.followsDone
      (alikeChain first firstTwin firsts
        [(operator, second), ..links]
        [(operatorTwin, secondTwin), ..linksTwin]
        (Both (operators, seconds) alike)))

theorem followsComparisonChain ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin)
    (kind: Tok) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (second secondTwin: Expr)
    (seconds: ExprsAlike second secondTwin):
    Parse.Follows SameCode ExprsAlike (() => comparisonChain self modes first kind operator second) (() =>
      comparisonChain selfTwin modes firstTwin kind operatorTwin secondTwin) :=
  match kind == Equals || kind == EqEq || kind == NotEq with
    | True => followsFatalAny _ (() => Syntax.fatal (chainRefused kind))
    | False =>
      followsChainAfter facts modes first firstTwin firsts operator operatorTwin operators second secondTwin seconds
        (isDescending kind)

theorem followsCmpChain ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin)
    (kind: Tok) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (second secondTwin: Expr)
    (seconds: ExprsAlike second secondTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => cmpChain self modes lhs kind operator second seen) (() =>
      cmpChain selfTwin modes lhsTwin kind operatorTwin secondTwin seen) :=
  match seen with
    | Some next =>
      match next.isComparison || next == KwIn || next == NotIn with
        | True =>
          followsComparisonChain facts modes lhs lhsTwin lhss kind operator operatorTwin operators second secondTwin
              seconds
        | False =>
          Parse.followsDone
            (alikeInfix InfixBinary lhs lhsTwin lhss operator operatorTwin operators second secondTwin seconds)
    | None =>
      Parse.followsDone
        (alikeInfix InfixBinary lhs lhsTwin lhss operator operatorTwin operators second secondTwin seconds)

theorem followsCmpSecond ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin)
    (kind: Tok) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (second secondTwin: Expr)
    (seconds: ExprsAlike second secondTwin):
    Parse.Follows SameCode ExprsAlike (() => cmpSecond self modes lhs kind operator second) (() =>
      cmpSecond selfTwin modes lhsTwin kind operatorTwin secondTwin) :=
  followsPeeked modes
    (seen => cmpChain self modes lhs kind operator second seen)
    (seen => cmpChain selfTwin modes lhsTwin kind operatorTwin secondTwin seen)
    (seen =>
      followsCmpChain facts modes lhs lhsTwin lhss kind operator operatorTwin operators second secondTwin seconds seen)

theorem followsCmpIf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin):
    Parse.Follows SameCode ExprsAlike (() => cmpIf self modes lhs operator) (() =>
      cmpIf selfTwin modes lhsTwin operatorTwin) :=
  followsThenEq followsHeadIndent (indent =>
    Parse.followsThen followsBump (keyword keywordTwin keywords =>
      Parse.followsMap
        (whenTrue => Infix InfixBinary lhs operator whenTrue)
        (whenTrue => Infix InfixBinary lhsTwin operatorTwin whenTrue)
        (facts.ifs modes indent keyword keywordTwin keywords)
        (whenTrue whenTrueTwin whens =>
          alikeInfix InfixBinary lhs lhsTwin lhss operator operatorTwin operators whenTrue whenTrueTwin whens)))

theorem followsCmpAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin)
    (kind: Tok) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (conditional: Bool):
    Parse.Follows SameCode ExprsAlike (() => cmpAfter self modes lhs kind operator conditional) (() =>
      cmpAfter selfTwin modes lhsTwin kind operatorTwin conditional) :=
  match conditional with
    | True => followsCmpIf facts modes lhs lhsTwin lhss operator operatorTwin operators
    | False => Parse.followsThen (followsPipedRange facts.below modes) (second secondTwin seconds =>
      followsCmpSecond facts.below modes lhs lhsTwin lhss kind operator operatorTwin operators second secondTwin
          seconds)

theorem followsCmpCompare ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => cmpCompare self modes lhs kind) (() =>
      cmpCompare selfTwin modes lhsTwin kind) :=
  Parse.followsThen followsBump (operator operatorTwin operators =>
    followsThenEq (followsAt modes KwIf) (conditional =>
      followsCmpAfter facts modes lhs lhsTwin lhss kind operator operatorTwin operators conditional))

theorem followsCmpKind ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (first: Option Tok) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => cmpKind self modes first lhs kind) (() =>
      cmpKind selfTwin modes first lhsTwin kind) :=
  match kind == KwIn || kind == NotIn with
    | True => followsMembership facts.below modes first lhs lhsTwin lhss
    | False =>
      match kind.isComparison with
        | True => followsCmpCompare facts modes lhs lhsTwin lhss kind
        | False => Parse.followsDone lhss

theorem followsCmpOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (first: Option Tok) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => cmpOn self modes first lhs seen) (() =>
      cmpOn selfTwin modes first lhsTwin seen) :=
  match seen with
    | Some kind => followsCmpKind facts modes first lhs lhsTwin lhss kind
    | None => Parse.followsDone lhss

theorem followsCmpPiped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (first: Option Tok) (lhs lhsTwin: Expr)
    (lhss: ExprsAlike lhs lhsTwin):
    Parse.Follows SameCode ExprsAlike (() => cmpPiped self modes first lhs) (() =>
      cmpPiped selfTwin modes first lhsTwin) :=
  followsPeeked modes
    (seen => cmpOn self modes first lhs seen)
    (seen => cmpOn selfTwin modes first lhsTwin seen)
    (seen => followsCmpOn facts modes first lhs lhsTwin lhss seen)

theorem followsCmpFirst ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin)
    (modes: Modes) (first: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => cmpFirst self modes first) (() => cmpFirst selfTwin modes first) :=
  Parse.followsThen (followsPipedRange facts.below modes) (lhs lhsTwin lhss =>
    followsCmpPiped facts modes first lhs lhsTwin lhss)

theorem followsCmpExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: IfFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => cmpExpr self modes) (() => cmpExpr selfTwin modes) :=
  followsOn
    (seen => cmpFirst self modes (seen.head.map Item.kind))
    (seen => cmpFirst selfTwin modes (seen.head.map Item.kind))
    (seen others same =>
      rewrite deafOfStripped (items => items.head.map Item.kind) headKindDeaf seen others same then
        followsCmpFirst facts modes (others.head.map Item.kind))

-- Logic and the end of an expression.

theorem followsLogicOperand ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (quantified: Bool):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike ExprsAlike))
      (() => logicOperand self modes operator quantified)
      (() => logicOperand selfTwin modes operatorTwin quantified) :=
  match quantified with
    | True =>
      Parse.followsMap
        (operand => Some (operator, operand))
        (operand => Some (operatorTwin, operand))
        (facts.quantifiers modes)
        (operand operandTwin operands => (operators, operands))
    | False =>
      Parse.followsMap
        (operand => Some (operator, operand))
        (operand => Some (operatorTwin, operand))
        (followsCmpExpr facts.below modes)
        (operand operandTwin operands => (operators, operands))

theorem followsLogicLink ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode (Option.Alike (PairAlike WordsAlike ExprsAlike)) (() => logicLink self modes) (() =>
      logicLink selfTwin modes) :=
  Parse.followsThen followsBump (operator operatorTwin operators =>
    followsThenEq (followsQuantifierAhead modes) (quantified =>
      followsLogicOperand facts modes operator operatorTwin operators quantified))

theorem followsLogicOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode (Option.Alike (PairAlike WordsAlike ExprsAlike)) (() => logicOn self modes seen) (() =>
      logicOn selfTwin modes seen) :=
  match seen with
    | Some kind =>
      match kind == AndAnd || kind == OrOr with
        | True => followsLogicLink facts modes
        | False => Parse.followsDone Trivial
    | None => Parse.followsDone Trivial

theorem followsLogicLinks ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode (List.All2 (PairAlike WordsAlike ExprsAlike)) (() => logicLinks self modes) (() =>
      logicLinks selfTwin modes) :=
  Parse.followsLoop
    (followsPeeked modes (seen => logicOn self modes seen) (seen => logicOn selfTwin modes seen) (seen =>
      followsLogicOn facts modes seen))

theorem followsLogicChain ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin):
    Parse.Follows SameCode ExprsAlike (() => logicChain self modes first) (() => logicChain selfTwin modes firstTwin) :=
  Parse.followsThen (followsLogicLinks facts modes) (links linksTwin alike =>
    Parse.followsDone
      (rewrite List.all2Length _ links linksTwin alike then
        groupLogicDeaf
          (linksTwin.length + 1)
          first
          firstTwin
          links
          linksTwin
          firsts
          (linksAlike links linksTwin alike)))

theorem followsLogicOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (compared comparedTwin: Expr)
    (compareds: ExprsAlike compared comparedTwin) (ahead: Bool):
    Parse.Follows SameCode ExprsAlike (() => logicOf self modes compared ahead) (() =>
      logicOf selfTwin modes comparedTwin ahead) :=
  match ahead with
    | True => followsLogicChain facts modes compared comparedTwin compareds
    | False => Parse.followsDone compareds

theorem followsLogicAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (compared comparedTwin: Expr)
    (compareds: ExprsAlike compared comparedTwin):
    Parse.Follows SameCode ExprsAlike (() => logicAfter self modes compared) (() =>
      logicAfter selfTwin modes comparedTwin) :=
  followsThenEq (followsAndOrAhead modes) (ahead => followsLogicOf facts modes compared comparedTwin compareds ahead)

theorem followsLogicLevel ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => logicLevel self modes) (() => logicLevel selfTwin modes) :=
  Parse.followsThen (followsCmpExpr facts.below modes) (compared comparedTwin compareds =>
    followsLogicAfter facts modes compared comparedTwin compareds)

-- `<->`.

theorem followsIffEnd ∀ (left leftTwin: Expr)
    (lefts: ExprsAlike left leftTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (right rightTwin: Expr)
    (rights: ExprsAlike right rightTwin) (chained: Bool):
    Parse.Follows SameCode ExprsAlike (() => iffEnd left operator right chained) (() =>
      iffEnd leftTwin operatorTwin rightTwin chained) :=
  match chained with
    | True => followsFatalAny "`<->` doesn't chain" (() => Syntax.fatal "`<->` doesn't chain")
    | False =>
      Parse.followsDone (alikeInfix InfixIff left leftTwin lefts operator operatorTwin operators right rightTwin rights)

theorem followsIffRight ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (quantified: Bool):
    Parse.Follows SameCode ExprsAlike (() => iffRight self modes quantified) (() =>
      iffRight selfTwin modes quantified) :=
  match quantified with
    | True => facts.quantifiers modes
    | False => Parse.followsThen (followsCmpExpr facts.below modes) (compared comparedTwin compareds =>
      followsLogicAfter facts modes compared comparedTwin compareds)

theorem followsIffAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (left leftTwin: Expr)
    (lefts: ExprsAlike left leftTwin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (quantified: Bool):
    Parse.Follows SameCode ExprsAlike (() => iffAfter self modes left operator quantified) (() =>
      iffAfter selfTwin modes leftTwin operatorTwin quantified) :=
  Parse.followsThen (followsIffRight facts modes quantified) (right rightTwin rights =>
    followsThenEq (followsAt modes IffArrow) (chained =>
      followsIffEnd left leftTwin lefts operator operatorTwin operators right rightTwin rights chained))

theorem followsIff ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (left leftTwin: Expr)
    (lefts: ExprsAlike left leftTwin):
    Parse.Follows SameCode ExprsAlike (() => iff self modes left) (() => iff selfTwin modes leftTwin) :=
  Parse.followsThen followsBump (operator operatorTwin operators =>
    followsThenEq (followsQuantifierAhead modes) (quantified =>
      followsIffAfter facts modes left leftTwin lefts operator operatorTwin operators quantified))

theorem followsIffOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (logic logicTwin: Expr)
    (logics: ExprsAlike logic logicTwin) (ahead: Bool):
    Parse.Follows SameCode ExprsAlike (() => iffOf self modes logic ahead) (() =>
      iffOf selfTwin modes logicTwin ahead) :=
  match ahead with
    | True => followsIff facts modes logic logicTwin logics
    | False => Parse.followsDone logics

-- The end of an operator expression: `->` and `;`.

theorem followsArrowEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (arrow arrowTwin: Word)
    (arrows: WordsAlike arrow arrowTwin):
    Parse.Follows SameCode ExprsAlike (() => arrowEnd self modes value arrow) (() =>
      arrowEnd selfTwin modes valueTwin arrowTwin) :=
  Parse.followsMap
    (result => Infix InfixArrow value arrow result)
    (result => Infix InfixArrow valueTwin arrowTwin result)
    (results modes)
    (result resultTwin results =>
      alikeInfix InfixArrow value valueTwin values arrow arrowTwin arrows result resultTwin results)

theorem followsSemiAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (semicolon semicolonTwin: Word)
    (semicolons: WordsAlike semicolon semicolonTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => semiAfter self modes value semicolon seen) (() =>
      semiAfter selfTwin modes valueTwin semicolonTwin seen) :=
  match seen with
    | None | Some RParen | Some RBracket | Some RBrace | Some Comma =>
      followsFatalAny semicolonAtEnd (() => Syntax.fatal semicolonAtEnd)
    | _ =>
      Parse.followsMap
        (right => Infix InfixSeq value semicolon right)
        (right => Infix InfixSeq valueTwin semicolonTwin right)
        (followsFull knot modes)
        (right rightTwin rights =>
          alikeInfix InfixSeq value valueTwin values semicolon semicolonTwin semicolons right rightTwin rights)

theorem followsSemiExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    Parse.Follows SameCode ExprsAlike (() => semiExpr self modes value) (() => semiExpr selfTwin modes valueTwin) :=
  Parse.followsThen followsBump (semicolon semicolonTwin semicolons =>
    followsThenEq (followsPeek modes) (seen =>
      followsSemiAfter knot modes value valueTwin values semicolon semicolonTwin semicolons seen))

theorem followsOpEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin)
    (sequence: Bool) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => opEnd self modes value sequence seen) (() =>
      opEnd selfTwin modes valueTwin sequence seen) :=
  match seen with
    | Some kind =>
      match kind == Arrow with
        | True => Parse.followsThen followsBump (arrow arrowTwin arrows =>
          followsArrowEnd knot results modes value valueTwin values arrow arrowTwin arrows)
        | False =>
          match kind == Semi && sequence with
            | True => followsSemiExpr knot modes value valueTwin values
            | False => Parse.followsDone values
    | None => Parse.followsDone values

theorem followsOpSequence ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (sequence: Bool):
    Parse.Follows SameCode ExprsAlike (() => opSequence self modes value sequence) (() =>
      opSequence selfTwin modes valueTwin sequence) :=
  followsPeeked modes
    (seen => opEnd self modes value sequence seen)
    (seen => opEnd selfTwin modes valueTwin sequence seen)
    (seen => followsOpEnd knot results modes value valueTwin values sequence seen)

theorem followsOpIffed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin)
    (modes: Modes) (section: Bool) (iffed iffedTwin: Expr)
    (iffeds: ExprsAlike iffed iffedTwin):
    Parse.Follows SameCode ExprsAlike (() => opIffed self modes section iffed) (() =>
      opIffed selfTwin modes section iffedTwin) :=
  followsThenEq (followsSequenceAhead modes) (sequence =>
    followsOpSequence knot results modes
      (sectioned section iffed)
      (sectioned section iffedTwin)
      (sectionedDeaf section iffed iffedTwin iffeds)
      sequence)

theorem followsOpLogic ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (section: Bool) (logic logicTwin: Expr)
    (logics: ExprsAlike logic logicTwin):
    Parse.Follows SameCode ExprsAlike (() => opLogic self modes section logic) (() =>
      opLogic selfTwin modes section logicTwin) :=
  followsThenEq
    [p := () => modes.at IffArrow]
    [q := () => modes.at IffArrow]
    [j := ahead => opIffed self modes section (iffOf self modes logic ahead)]
    [k := ahead => opIffed selfTwin modes section (iffOf selfTwin modes logicTwin ahead)]
    (followsAt modes IffArrow)
    (ahead =>
      Parse.followsThen (followsIffOf facts modes logic logicTwin logics ahead) (iffed iffedTwin iffeds =>
        followsOpIffed facts.below.below.below.below.knot facts.results modes section iffed iffedTwin iffeds))

theorem followsOpCompared ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (section: Bool) (compared comparedTwin: Expr)
    (compareds: ExprsAlike compared comparedTwin):
    Parse.Follows SameCode ExprsAlike (() => opCompared self modes section compared) (() =>
      opCompared selfTwin modes section comparedTwin) :=
  Parse.followsThen (followsLogicAfter facts modes compared comparedTwin compareds) (logic logicTwin logics =>
    followsOpLogic facts modes section logic logicTwin logics)

theorem followsOpSection ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (start: Nat) (section: Bool):
    Parse.Follows SameCode ExprsAlike (() => opSection self modes start section) (() =>
      opSection selfTwin modes start section) :=
  Parse.followsThen
    (followsCmpExpr facts.below (if section then { modes | sectionHead = Some start } else modes))
    (compared comparedTwin compareds => followsOpCompared facts modes section compared comparedTwin compareds)

theorem followsOpStart ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin)
    (modes: Modes) (start: Nat):
    Parse.Follows SameCode ExprsAlike (() => opStart self modes start) (() => opStart selfTwin modes start) :=
  followsThenEq (followsAt modes Dot) (section => followsOpSection facts modes start section)

theorem followsOperatorExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: QuantifierFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => operatorExpr self modes) (() => operatorExpr selfTwin modes) :=
  followsThenEq followsOffset (start => followsOpStart facts modes start)

-- The two steps `pipesFrom` is made of, from the same lemma.

theorem followsBareCases ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => bareCases modes) (() => bareCases modes) :=
  followsLook (bareCasesOn modes) (bareCasesOnDeaf modes)
