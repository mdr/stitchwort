--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md), continued from `Syntax.FollowsFormsPatterns`: expressions that start with a
--| keyword, a lambda, a quantifier, `if` or a binder; blocks; and the rule that `expression` is built from.

namespace Syntax.FollowsFormsBlocks
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)
import Syntax.FollowsFormsBinders (..)
import Syntax.FollowsFormsArms (..)
import Syntax.FollowsFormsPatterns (..)

-- Expressions that start with a keyword, a lambda, a quantifier, `if` or a binder.

def PiExprFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (implicit: Bool) => Parse.Follows SameCode ExprsAlike (() => piExpr self modes implicit) (() =>
    piExpr selfTwin modes implicit)

--| The tier 2 of the statement facts: `∀` types and result types.
type PiFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: InductFacts self selfTwin,
  pis: PiExprFollows self selfTwin,
  results: ResultTypeFollows self selfTwin
}

def HandleFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => handleExpr self modes) (() => handleExpr selfTwin modes)

def CalcFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => calcExpr self modes) (() => calcExpr selfTwin modes)

def RewriteFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => rewriteExpr self modes) (() =>
    rewriteExpr selfTwin modes)

def CasesFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => casesExpr self modes) (() => casesExpr selfTwin modes)

def WalkFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => walkExpr self modes) (() => walkExpr selfTwin modes)

def LetStatementFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode LetsAlike (() => letStatement self modes) (() =>
    letStatement selfTwin modes)

def LetBodyFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (binding twin: Let) => LetsAlike binding twin
    → Parse.Follows SameCode ExprsAlike (() => letBody self modes binding) (() => letBody selfTwin modes twin)

--| The tier 3 of the statement facts: the keyword expressions (`handle`, `let`, `calc`, `rewrite` and `cases`), and
--| walks.
type KeywordFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: PiFacts self selfTwin,
  handles: HandleFollows self selfTwin,
  lets: LetStatementFollows self selfTwin,
  bodies: LetBodyFollows self selfTwin,
  calcs: CalcFollows self selfTwin,
  rewrites: RewriteFollows self selfTwin,
  casings: CasesFollows self selfTwin,
  walks: WalkFollows self selfTwin
}

theorem followsLetExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => letExpr self modes) (() => letExpr selfTwin modes) :=
  Parse.followsThen (lets modes.sealed) (binding twin alike => bodies modes binding twin alike)

theorem followsMatchedPiped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: LambdaFacts self selfTwin)
    (modes: Modes) (indent: Nat) (matched matchedTwin: Expr)
    (matcheds: ExprsAlike matched matchedTwin) (piped: Bool):
    Parse.Follows SameCode ExprsAlike (() => matchedPiped self modes indent matched piped) (() =>
      matchedPiped selfTwin modes indent matchedTwin piped) :=
  match piped with
    | True => followsPipeChain facts modes indent matched matchedTwin matcheds
    | False => Parse.followsDone matcheds

theorem followsMatchPiped ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: InductFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => matchPiped self modes) (() => matchPiped selfTwin modes) :=
  followsThenEq followsHeadIndent (indent =>
    Parse.followsThen followsBump (keyword keywordTwin keywords =>
      Parse.followsThen
        (followsMatchExpr facts.below.knot altPatternFollows facts.inducts facts.reifies modes keyword keywordTwin
            keywords)
        (matched matchedTwin matcheds =>
          followsThenEq (followsAtPipe modes) (piped =>
            followsMatchedPiped
              (lambdaFactsOf (matchFactsOf facts.below.knot facts.inducts facts.reifies) facts.below)
              modes
              indent
              matched
              matchedTwin
              matcheds
              piped))))

theorem followsExprKeyword ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin)
    (handles: HandleFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin)
    (calcs: CalcFollows self selfTwin)
    (rewrites: RewriteFollows self selfTwin)
    (casings: CasesFollows self selfTwin)
    (modes: Modes) (kind: Tok):
    Parse.Follows SameCode ExprsAlike (() => exprKeyword self modes kind) (() => exprKeyword selfTwin modes kind) :=
  match kind == KwHandle with
    | True => handles modes
    | False =>
      match kind == KwLet with
        | True => followsLetExpr lets bodies modes
        | False =>
          match kind == KwCalc with
            | True => calcs modes
            | False =>
              match kind == KwRewrite with
                | True => rewrites modes
                | False =>
                  match kind == KwCases with
                    | True => casings modes
                    | False =>
                      followsMatchPiped
                        {
                          below = { knot = knot, groups = groups, binders = binders },
                          inducts = inducts,
                          reifies = reifies
                        }
                        modes

theorem followsLambdaResultHere ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => lambdaResultHere modes) (() => lambdaResultHere modes) :=
  followsThenEq followsLeftCount (fuel =>
    followsLook (lambdaResultType modes (fuel + 1) False) (lambdaResultTypeDeaf modes (fuel + 1) False))

theorem followsImplicitHere ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => implicitHere modes) (() => implicitHere modes) :=
  followsThenEq followsLeftCount (fuel =>
    Parse.followsThen followsLeft (rest others same =>
      followsThenEq (followsPeek modes) (seen =>
        Parse.followsDone
          (deafOfStripped
            (found => implicitOn (fuel + 1) found seen)
            (found => implicitOnDeaf (fuel + 1) found seen)
            rest
            others
            same))))

theorem followsPiHere ∀ (modes: Modes): Parse.Follows SameCode Same (() => piHere modes) (() => piHere modes) :=
  Parse.followsThen followsLeft (rest others same =>
    followsThenEq (followsPeek modes) (seen =>
      Parse.followsDone (deafOfStripped (found => piOn found seen) (found => piOnDeaf found seen) rest others same)))

theorem followsIfKeyword ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => ifKeyword self modes) (() => ifKeyword selfTwin modes) :=
  followsThenEq followsHeadIndent (indent =>
    Parse.followsThen followsBump (keyword keywordTwin keywords =>
      followsIfExpr knot modes indent keyword keywordTwin keywords))

theorem followsExprPi ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: PiFacts self selfTwin)
    (modes: Modes) (pi: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprPi self modes pi) (() => exprPi selfTwin modes pi) :=
  match pi with
    | True => facts.pis modes False
    | False =>
      let header := facts.below.below
      let matched := matchFactsOf header.knot facts.below.inducts facts.below.reifies
      followsOperatorExpr (quantifierFactsOf (ifFactsOf (lambdaFactsOf matched header)) header facts.results) modes

theorem followsExprImplicit ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: PiFacts self selfTwin)
    (modes: Modes) (implicit: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprImplicit self modes implicit) (() =>
      exprImplicit selfTwin modes implicit) :=
  match implicit with
    | True => facts.pis modes True
    | False => followsThenEq (followsPiHere modes) (pi => followsExprPi facts modes pi)

theorem followsExprPlain ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: PiFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => exprPlain self modes) (() => exprPlain selfTwin modes) :=
  followsThenEq (followsImplicitHere modes) (implicit => followsExprImplicit facts modes implicit)

theorem followsExprBinder ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: PiFacts self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => exprBinder self modes seen) (() => exprBinder selfTwin modes seen) :=
  match seen with
    | Some kind =>
      match kind == KwExists || kind == KwForall with
        | True => followsQuantifier facts.below.below patternOfFollows modes
        | False =>
          match kind == KwIf with
            | True => followsIfKeyword facts.below.below.knot modes
            | False => followsExprPlain facts modes
    | None => followsExprPlain facts modes

theorem followsExprResult ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: PiFacts self selfTwin)
    (modes: Modes) (refused: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprResult self modes refused) (() => exprResult selfTwin modes refused) :=
  match refused with
    | True =>
      followsFatalAny "a lambda doesn't take a result type" (() => Syntax.fatal "a lambda doesn't take a result type")
    | False =>
      followsPeeked modes (seen => exprBinder self modes seen) (seen => exprBinder selfTwin modes seen) (seen =>
        followsExprBinder facts modes seen)

theorem followsExprLambda ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: PiFacts self selfTwin)
    (modes: Modes) (lambdas: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprLambda self modes lambdas) (() => exprLambda selfTwin modes lambdas) :=
  match lambdas with
    | True => followsLambdaOf facts.below.below patternOfFollows modes None None Trivial
    | False => followsThenEq (followsLambdaResultHere modes) (refused => followsExprResult facts modes refused)

theorem followsWalkHere ∀ (modes: Modes): Parse.Follows SameCode Same (() => walkHere modes) (() => walkHere modes) :=
  followsLook (walkOn modes) (walkOnDeaf modes)

theorem followsExprWalk ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: KeywordFacts self selfTwin)
    (modes: Modes) (walk: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprWalk self modes walk) (() => exprWalk selfTwin modes walk) :=
  match walk with
    | True => facts.walks modes
    | False => followsThenEq (followsLambdaHere modes) (lambdas => followsExprLambda facts.below modes lambdas)

theorem followsExprOther ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: KeywordFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => exprOther self modes) (() => exprOther selfTwin modes) :=
  followsThenEq (followsWalkHere modes) (walk => followsExprWalk facts modes walk)

theorem followsExprInlineOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: KeywordFacts self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => exprInlineOn self modes seen) (() => exprInlineOn selfTwin modes seen) :=
  match seen with
    | Some kind =>
      match startsKeywordExpr kind with
        | True =>
          followsExprKeyword facts.below.below.below.knot facts.below.below.below.groups facts.below.below.below.binders
              facts.below.below.inducts facts.below.below.reifies facts.handles facts.lets facts.bodies facts.calcs
              facts.rewrites facts.casings modes kind
        | False => followsExprOther facts modes
    | None => followsExprOther facts modes

theorem followsExprInline ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: KeywordFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => exprInline self modes) (() => exprInline selfTwin modes) :=
  followsPeeked modes (seen => exprInlineOn self modes seen) (seen => exprInlineOn selfTwin modes seen) (seen =>
    followsExprInlineOn facts modes seen)

-- Blocks.

def StatementTag: Statement → Nat
  | LetStatement _ => 0
  | LocalDef _ _ _ => 1
  | ExprStatement _ => 2

theorem tagOfWalked ∀ (statement: Statement):
    StatementTag (walkStatement blankPure statement).blank = StatementTag statement :=
  match statement with | LetStatement _ | LocalDef _ _ _ | ExprStatement _ => byComputing

theorem tagSame ∀ (statement twin: Statement)
    (alike: StatementsAlike statement twin):
    StatementTag statement = StatementTag twin :=
  calc StatementTag statement
    _ = StatementTag (walkStatement blankPure statement).blank := Eq.flipped (tagOfWalked statement)
    _ = StatementTag (walkStatement blankPure twin).blank := rewrite alike
    _ = StatementTag twin := tagOfWalked twin

theorem statementsBlankCons ∀ (statement: Statement) (rest: List Statement):
    blankStatements (walkStatements blankPure [statement, ..rest])
      = [(walkStatement blankPure statement).blank, ..blankStatements (walkStatements blankPure rest)] :=
  byComputing

theorem statementsBlank ∀ (statements twins: List Statement)
    (alike: List.All2 StatementsAlike statements twins):
    blankStatements (walkStatements blankPure statements) = blankStatements (walkStatements blankPure twins) :=
  List.all2Join
    [f := list => blankStatements (walkStatements blankPure list)]
    [key := statement => (walkStatement blankPure statement).blank]
    (k rest => [k, ..rest])
    statementsBlankCons
    (x y same => same)
    statements
    twins
    alike

theorem alikeBlock ∀ (first twin: Statement)
    (firsts: StatementsAlike first twin) (rest restTwin: List Statement)
    (rests: List.All2 StatementsAlike rest restTwin) (result resultTwin: Expr)
    (results: ExprsAlike result resultTwin):
    ExprsAlike (Block first rest result) (Block twin restTwin resultTwin) :=
  calc (Block first rest result).walk blankPure
    _ = Block
        (walkStatement blankPure first).blank
        (blankStatements (walkStatements blankPure rest))
        (result.walk blankPure) := byComputing
    _ = Block
        (walkStatement blankPure twin).blank
        (blankStatements (walkStatements blankPure restTwin))
        (resultTwin.walk blankPure) := rewrite firsts, statementsBlank rest restTwin rests, results
    _ = (Block twin restTwin resultTwin).walk blankPure := byComputing

def StatementFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode StatementsAlike (() => statement self modes) (() =>
    statement selfTwin modes)

--| The tier 4 of the statement facts: statements.
type StatementFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: KeywordFacts self selfTwin,
  statements: StatementFollows self selfTwin
}

def valueOf (fallback: Expr): Statement → Expr
  | ExprStatement value => value
  | _ => fallback

theorem valuesOfStatements ∀ (value twin: Expr)
    (alike: StatementsAlike (ExprStatement value) (ExprStatement twin)):
    ExprsAlike value twin :=
  Eq.cong (valueOf value) alike

theorem followsBlockOrdered ∀ (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin) (ordered orderedTwin: List Statement)
    (alike: List.All2 StatementsAlike ordered orderedTwin):
    Parse.Follows SameCode ExprsAlike
      (() =>
        (match ordered with
          | [first, ..rest] => Block first rest value
          | [] => value))
      (() =>
        (match orderedTwin with
          | [first, ..rest] => Block first rest valueTwin
          | [] => valueTwin)) :=
  match ordered, orderedTwin with
    | [first, ..rest], [firstTwin, ..restTwin] =>
      Parse.followsDone (alikeBlock first firstTwin alike.left rest restTwin alike.right value valueTwin values)
    | [], [] => Parse.followsDone values

theorem followsBlockResult ∀ (statements twins: List Statement)
    (alike: List.All2 StatementsAlike statements twins):
    Parse.Follows SameCode ExprsAlike (() => blockResult statements) (() => blockResult twins) :=
  match statements, twins with
    | [], [] =>
      followsFatalAny "the parser read no line of a block" (() => Syntax.fatal "the parser read no line of a block")
    | [statement, ..rest], [twin, ..restTwin] =>
      match statement, twin with
        | ExprStatement value, ExprStatement valueTwin =>
          match rest, restTwin with
            | [], [] => Parse.followsDone (valuesOfStatements value valueTwin alike.left)
            | [], [lastTwin, ..earlierTwin] => alike.right.impossible
            | [last, ..earlier], [] => alike.right.impossible
            | [last, ..earlier], [lastTwin, ..earlierTwin] =>
              followsBlockOrdered value valueTwin
                (valuesOfStatements value valueTwin alike.left)
                [last, ..earlier].reverse
                [lastTwin, ..earlierTwin].reverse
                (List.all2Reverse [last, ..earlier] [lastTwin, ..earlierTwin] alike.right)
        | LetStatement binding, LetStatement twinBinding =>
          followsFatalAny "a block must end with an expression, not `let`" (() =>
            Syntax.fatal "a block must end with an expression, not `let`")
        | LocalDef attributes header body, LocalDef attributesTwin headerTwin bodyTwin =>
          followsFatalAny "a block must end with an expression, not a local `def` or `theorem`" (() =>
            Syntax.fatal "a block must end with an expression, not a local `def` or `theorem`")
        | LetStatement binding, LocalDef attributesTwin headerTwin bodyTwin =>
          let clash := tagSame (LetStatement binding) (LocalDef attributesTwin headerTwin bodyTwin) alike.left
          cases
        | LetStatement binding, ExprStatement valueTwin =>
          let clash := tagSame (LetStatement binding) (ExprStatement valueTwin) alike.left
          cases
        | LocalDef attributes header body, LetStatement bindingTwin =>
          let clash := tagSame (LocalDef attributes header body) (LetStatement bindingTwin) alike.left
          cases
        | LocalDef attributes header body, ExprStatement valueTwin =>
          let clash := tagSame (LocalDef attributes header body) (ExprStatement valueTwin) alike.left
          cases
        | ExprStatement value, LetStatement bindingTwin =>
          let clash := tagSame (ExprStatement value) (LetStatement bindingTwin) alike.left
          cases
        | ExprStatement value, LocalDef attributesTwin headerTwin bodyTwin =>
          let clash := tagSame (ExprStatement value) (LocalDef attributesTwin headerTwin bodyTwin) alike.left
          cases

theorem followsBlockOffset ∀ [self selfTwin: Goal → {Parse Item} Expr] (more: Nat) (modes: Modes) (column: Nat)
    (many: Bool) (done doneTwin: List Statement)
    (dones: List.All2 StatementsAlike done doneTwin)
    (before: Nat) (next other: Item)
    (same: SameCode next other) (now: Nat)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockOffset more self modes column many done before next now)
      (() => blockOffset more selfTwin modes column many doneTwin before other now) :=
  let starts: next.leaf.token.lineStart = other.leaf.token.lineStart := lineStartSame next other same
  let columns: next.leaf.token.column = other.leaf.token.column := columnSame next other same
  let kinds: next.kind = other.kind := kindSame next other same
  let guards: (now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind)
    = (now != before
      && many
      && other.leaf.token.lineStart
      && other.leaf.token.column == column
      && !endsBlocks other.kind) :=
    rewrite starts, columns, kinds
  match guard: now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind, guardTwin: now != before
    && many
    && other.leaf.token.lineStart
    && other.leaf.token.column == column
    && !endsBlocks other.kind with
    | True, True => rest done doneTwin dones
    | False, False => Parse.followsDone dones

theorem followsBlockItems ∀ [self selfTwin: Goal → {Parse Item} Expr] (more: Nat) (modes: Modes) (column: Nat)
    (many: Bool) (done doneTwin: List Statement)
    (dones: List.All2 StatementsAlike done doneTwin)
    (before: Nat) (items others: List Item)
    (same: List.All2 SameCode items others)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockItems more self modes column many done before items)
      (() => blockItems more selfTwin modes column many doneTwin before others) :=
  match items, others with
    | [], [] => Parse.followsDone dones
    | [next, ..tail], [other, ..tailTwin] => followsThenEq followsOffset (now =>
      followsBlockOffset more modes column many done doneTwin dones before next other same.left now rest)

theorem followsBlockDone ∀ [self selfTwin: Goal → {Parse Item} Expr] (more: Nat) (modes: Modes) (column: Nat)
    (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin)
    (before: Nat) (line lineTwin: Statement)
    (lines: StatementsAlike line lineTwin)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockDone more self modes column many found before line)
      (() => blockDone more selfTwin modes column many foundTwin before lineTwin) :=
  followsOn
    (seen => blockItems more self modes column many [line, ..found] before seen)
    (seen => blockItems more selfTwin modes column many [lineTwin, ..foundTwin] before seen)
    (seen others same =>
      followsBlockItems more modes column many
        [line, ..found]
        [lineTwin, ..foundTwin]
        (Both lines founds)
        before
        seen
        others
        same
        rest)

theorem followsBlockKind ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (more: Nat) (modes statementModes: Modes) (column: Nat) (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin)
    (before: Nat) (seen: Option Tok)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockKind more self modes column many found before statementModes seen)
      (() => blockKind more selfTwin modes column many foundTwin before statementModes seen) :=
  Parse.followsThen
    (statements { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] })
    (line lineTwin lines =>
      followsBlockDone more modes column many found foundTwin founds before line lineTwin lines rest)

theorem followsBlockLine ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (more: Nat) (modes: Modes) (column: Nat) (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin)
    (before: Nat) (items others: List Item)
    (same: List.All2 SameCode items others)
    (rest: ∀ (found foundTwin: List Statement) => List.All2 StatementsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines more self modes column many found) (() =>
        blockLines more selfTwin modes column many foundTwin)):
    Parse.Follows SameCode
      (List.All2 StatementsAlike)
      (() => blockLine more self modes column many found before items)
      (() => blockLine more selfTwin modes column many foundTwin before others) :=
  rewrite deafOfStripped nextIndex nextIndexDeaf items others same then
    followsThenEq (followsPeek { modes | allow = nextIndex others }) (seen =>
      followsBlockKind statements more modes
        { modes | allow = nextIndex others }
        column
        many
        found
        foundTwin
        founds
        before
        seen
        rest)

theorem followsBlockLines ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (fuel: Nat) (modes: Modes) (column: Nat) (many: Bool) (found foundTwin: List Statement)
    (founds: List.All2 StatementsAlike found foundTwin):
    Parse.Follows SameCode (List.All2 StatementsAlike) (() => blockLines fuel self modes column many found) (() =>
      blockLines fuel selfTwin modes column many foundTwin) :=
  match fuel with
    | Zero => Parse.followsDone founds
    | Succ more => followsThenEq followsOffset (before =>
      followsOn
        (seen => blockLine more self modes column many found before seen)
        (seen => blockLine more selfTwin modes column many foundTwin before seen)
        (seen others same =>
          followsBlockLine statements more modes column many found foundTwin founds before seen others same
            (found1 found2 founds2 => followsBlockLines statements more modes column many found1 found2 founds2)))

theorem followsBlockInner ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (inner: Modes) (column: Nat) (many: Bool):
    Parse.Follows SameCode ExprsAlike
      (() => blockResult (blockLines (Parse.mark().left + 1) self inner column many []))
      (() => blockResult (blockLines (Parse.mark().left + 1) selfTwin inner column many [])) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks =>
    rewrite <- marks.right.right then
      Parse.followsThen
        (followsBlockLines statements (Succ here.left) inner column many [] [] Trivial)
        (lines twins alike => followsBlockResult lines twins alike))

theorem followsBlock ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (statements: StatementFollows self selfTwin)
    (modes: Modes) (column: Nat) (many: Bool):
    Parse.Follows SameCode ExprsAlike (() => block self modes column many) (() => block selfTwin modes column many) :=
  match many with
    | True => followsBlockInner statements { modes | limit = Some column, letValue = None } column True
    | False => followsBlockInner statements { modes | limit = Some column } column False

theorem followsExprRuns ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: StatementFacts self selfTwin)
    (modes: Modes) (item other: Item)
    (same: SameCode item other)
    (limit: Nat) (runs: Bool):
    Parse.Follows SameCode ExprsAlike (() => exprRuns self modes item limit runs) (() =>
      exprRuns selfTwin modes other limit runs) :=
  match runs with
    | True => followsGap modes ranOutLine (() => modes.gap ranOutLine)
    | False =>
      let columns: item.leaf.token.column = other.leaf.token.column := columnSame item other same
      rewrite columns then
        match other.leaf.token.column == limit with
          | True => followsBlock facts.statements modes other.leaf.token.column False
          | False => followsExprInline facts.below modes

theorem followsExprBlock ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: StatementFacts self selfTwin)
    (modes: Modes) (item other: Item)
    (same: SameCode item other):
    Parse.Follows SameCode ExprsAlike (() => exprBlock self modes item) (() => exprBlock selfTwin modes other) :=
  let columns: item.leaf.token.column = other.leaf.token.column := columnSame item other same
  match modes.limit with
    | None => rewrite columns then followsBlock facts.statements modes other.leaf.token.column True
    | Some limit =>
      let wide: (item.leaf.token.column > limit: Bool) = (other.leaf.token.column > limit: Bool) := rewrite columns
      match big: (item.leaf.token.column > limit: Bool), bigTwin: (other.leaf.token.column > limit: Bool) with
        | True, True => rewrite columns then followsBlock facts.statements modes other.leaf.token.column True
        | False, False =>
          followsOn
            (seen => exprRuns self modes item limit (runsOutAt modes item limit seen))
            (seen => exprRuns selfTwin modes other limit (runsOutAt modes other limit seen))
            (seen others samed =>
              let runs: runsOutAt modes item limit seen = runsOutAt modes other limit others := calc runsOutAt modes
                  item limit seen
                _ = runsOutAt modes item.stripped limit (seen.map Item.stripped) := runsOutAtDeaf modes item limit seen
                _ = runsOutAt modes other.stripped limit (others.map Item.stripped) :=
                  rewrite same, sameCodeMap seen others samed
                _ = runsOutAt modes other limit others := Eq.flipped (runsOutAtDeaf modes other limit others)
              rewrite runs then followsExprRuns facts modes item other same limit (runsOutAt modes other limit others))

theorem followsExprOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: StatementFacts self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => exprOn self modes items) (() => exprOn selfTwin modes others) :=
  match items, others with
    | [], [] => followsExprInline facts.below modes
    | [item, ..rest], [other, ..restTwin] =>
      let starts: startsBlock modes item = startsBlock modes other :=
        deafItem (startsBlock modes) (startsBlockDeaf modes) item other same.left
      rewrite starts then
        match startsBlock modes other with
          | True => followsExprBlock facts modes item other same.left
          | False => followsExprInline facts.below modes

theorem followsExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: StatementFacts self selfTwin) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => expr self modes) (() => expr selfTwin modes) :=
  followsOn (seen => exprOn self modes seen) (seen => exprOn selfTwin modes seen) (seen others same =>
    followsExprOn facts modes seen others same)

-- The rule that `expression` is built from.

def ThenBodyFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => thenBody self modes) (() => thenBody selfTwin modes)

--| The tier 5 of the statement facts, all of them: `then` bodies.
type ThenFacts (self selfTwin: Goal → {Parse Item} Expr) = {
  below: StatementFacts self selfTwin,
  thens: ThenBodyFollows self selfTwin
}

theorem followsExpressionRule ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (facts: ThenFacts self selfTwin):
    SelfFollows (expressionRule self) (expressionRule selfTwin) :=
  goal =>
    let inducts := facts.below.below.below.below
    let header := inducts.below
    let matched := matchFactsOf header.knot inducts.inducts inducts.reifies
    let ifs := ifFactsOf (lambdaFactsOf matched header)
    match goal.level with
      | LevelFull => followsExpr facts.below goal.modes
      | LevelInline => followsExprInline facts.below.below goal.modes
      | LevelLogic => followsLogicLevel (quantifierFactsOf ifs header facts.below.below.below.results) goal.modes
      | LevelComparison => followsCmpExpr ifs goal.modes
      | LevelAppend => followsAppendExpr matched goal.modes
      | LevelAdditive => followsAddExpr matched goal.modes
      | LevelMultiplicative => followsMulExpr matched goal.modes
      | LevelUnary => followsUnary matched goal.modes
      | LevelArgument => followsAtom header.knot goal.modes False
      | LevelApp => followsApp matched.below goal.modes
      | LevelThenBody => facts.thens goal.modes
