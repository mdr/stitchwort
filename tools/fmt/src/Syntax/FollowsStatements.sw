--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md): `followsF`, one lemma for each parser function of `Syntax/Statements.sw`, says
--| that `F` follows itself on alike arguments, by the pattern of `Syntax/FollowsBase.sw`.
--|
--| Covered with a lemma of their own (79 functions, in the order of the file):
--|
--|   here, hereOn, columnHere, statement, statementOn, statementValue, statementOther, letStatementEnd,
--|   attributedLocal, localAttributed, letStatement, letAnnotation, letEquals, letPattern, letPatternOf, letBody,
--|   letBodyOf, letEnd, localDef, handleExpr, reifyExpr, reifyComma, handlerClauses, handlerClausesEnd, clausesFrom,
--|   handlerClause, handlerClauseOf, handlerName, operationClause, operationEnd, inductExpr, inductComma, inductEnd,
--|   inductArms, caseNames, caseNamesOn, calcExpr, calcIndented, calcAfter, calcBody, calcEnd, calcOperand,
--|   calcSteps, calcLine, calcRelation, calcRecord, stepSign, calcProof, rewriteExpr, rewriteAfter, rewriteWith,
--|   repeatedlyAhead, repeatedlyOn, rewriteRulesOf, reverseAhead, reverseOn, reverseOf, reverseIf, rewriteRules,
--|   rewriteRule, ruleSet, ruleSetAfter, setRules, setRule, rewriteTarget, rewriteTargetIf, targetAfter, targetOf,
--|   rewriteThen, rewriteOldIn, rewriteBody, startsAt, startsOn, ownLineAt, casesExpr, casesIn, casesThen, thenBody,
--|   thenBodyOn
--|
--| Without a lemma: `startsOtherStatement`, `allowedAt`, `letAtEnd`, `sequenceOn`, `calcNextOn`, `ownLineOn`,
--| `reverseMinus`, `columnOn` (pure; the `…Deaf` lemmas in `Syntax/DeafProofs.sw`), `calcRelations`, `atWithoutTarget`,
--| `oldIn` (text),
--| and `clausesLined`, `clausesAhead`, `inductLined`, `inductAhead`, `calcStep`, `rewriteMore`, `setMore`,
--| `setRulesAfter` (the lemma of the function that calls them runs over their bodies, as `matchArmsLined` is in
--| `Syntax/FollowsFormsArms.sw`). `sequenceAhead`'s lemma is in `Syntax/FollowsLadder.sw` (`followsSequenceAhead`).
--|
--| Hypotheses. A lemma takes the knot (`SelfFollows self selfTwin`), alike arguments, and the `Follows` fact of each
--| function in another file that it calls, as a `def` below:
--|
--| - `Syntax/DeclParser.sw`: `ExpectFixedFollows` (`Modes.expectFixed`), `LowerQualifiedFollows`
--|   (`Modes.lowerQualified`), `AttributesOfFollows` (`attributesOf`) and `DefinitionPartsFollows` (`definitionParts`
--|   with no `export` or `opaque`). They are stated with this file's own relations `AttributesAlike` and `PartsAlike`
--|   (the attributes walked with `blankPure`; the header walked and the body walked and blanked), so
--|   `Syntax/FollowsDecl.sw`'s lemmas need an adapter if they use other relations. `followsExpectFixed` and
--|   `followsLowerQualified` in `Syntax/FollowsDecl.sw` are `ExpectFixedFollows` and `LowerQualifiedFollows` as they
--|   stand.
--| - `Syntax/FollowsLadder.sw` and the `Syntax/FollowsForms…` files, where the lemma needs many hypotheses of its
--|   own: `ExprInlineFollows`, `CalcOperandFollows`, `AppendExprFollows`, `BlockFollows` and `ExprFollows`, each
--|   proved at the end from the knot and the facts below (`exprInlineFollows`, `calcOperandFollows`,
--|   `appendExprFollows`; `blocks` and `exprs` are `followsBlock` and `followsExpr` in
--|   `Syntax/FollowsFormsBlocks.sw`, in `thenBodyFollows`).
--|
--| The ten facts that `Syntax/FollowsForms.sw` and its continuations state about this file (`StatementFollows`,
--| `LetStatementFollows`, `LetBodyFollows`, `HandleFollows`, `CalcFollows`, `RewriteFollows`, `CasesFollows`,
--| `ThenBodyFollows`, `InductFollows`, `ReifyFollows`) are proved in the last section (`statementFollows`,
--| `letStatementFollows`, `letBodyFollows`, `handleFollows`, `calcFollows`,
--| `rewriteFollows`, `followsCasesExpr`, `thenBodyFollows`, `inductFollows`, `reifyFollows`), none with a cycle:
--| `followsExprInline` in `Syntax/FollowsForms.sw` takes the facts about `handleExpr`, `letStatement`, `letBody`,
--| `calcExpr`, `rewriteExpr` and `casesExpr`, but not `statement`'s, and `thenBodyFollows` uses `statementFollows`.
--| `Syntax/FollowsParse.sw` supplies the facts from `Syntax/FollowsDecl.sw` and the `Syntax/FollowsForms…` files that
--| the closing theorems take (`HeaderGroupFollows`, `BinderTypeFollows`, `PiExprFollows`, `ResultTypeFollows`, and
--| `Syntax/FollowsDecl.sw`'s four above).
--|
--| Nothing here reads a comment: a keyword's comments are `Anything`, and `Handle`, `Reify`, `Induct`, `Calc`,
--| `Rewrite`, `Cases` and `LetIn` are alike whatever those comments are (`inductFollows` and `reifyFollows` hold for
--| any comments, as `Syntax/FollowsForms.sw` states them). A statement's `LocalDef` is alike when its attributes and
--| header are equal once walked and its body walked and blanked; `localDef` reads the header's `unfolding` clause and
--| whether the body
--| is a primitive from these (`unfoldingSame`, `primitiveSame`).
--|
--| Helpers added here: the relations `CommentedAlike`, `AttributesAlike`, `PartsAlike`, `ClauseAlike`, `InductArmAlike`,
--| `StepAlike`, `RuleAlike`, `RuleSetAlike`, `RulesAlike`, `ReverseAlike`, `StepsAlike`, `SetRulesAlike`, the trees
--| (`alikeLet`, `alikeLetIn`, `alikeLocalDef`, `alikeHandle`, `alikeReify`, `alikeInduct`, `alikeCalc`,
--| `alikeRewrite`, `alikeCases`, …) and their list lemmas (`clausesBlank`, `inductArmsBlank`, `blankCalcStepsAlike`,
--| `ruleListBlank`).

namespace Syntax.FollowsStatements
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
import Syntax.FollowsFormsBlocks (..)

-- Relations on the parts of a statement, a handler, a `calc` and a `rewrite`.

def CommentedAlike (found twin: Option (Comments, Expr)): Prop :=
  Option.Alike (PairAlike Anything ExprsAlike) found twin

def AttributesAlike (attributes twin: List Attributes): Prop :=
  walkAttributes blankPure attributes = walkAttributes blankPure twin

def PartsAlike (parts twin: (Header, DefBody)): Prop :=
  walkHeader blankPure parts.fst = walkHeader blankPure twin.fst
    ∧ (walkDefBody blankPure parts.snd).blank = (walkDefBody blankPure twin.snd).blank

def ClauseAlike (clause twin: HandlerClause): Prop :=
  blankClauses (walkClauses blankPure [clause]) = blankClauses (walkClauses blankPure [twin])

def InductArmAlike (arm twin: InductArm): Prop :=
  blankInductArms (walkInductArms blankPure [arm]) = blankInductArms (walkInductArms blankPure [twin])

def StepAlike (step twin: CalcStep): Prop :=
  blankCalcSteps (walkSteps blankPure [step]) = blankCalcSteps (walkSteps blankPure [twin])

def RuleAlike (rule twin: RewriteRule): Prop :=
  blankRuleList (walkRuleList blankPure [rule]) = blankRuleList (walkRuleList blankPure [twin])

def RuleSetAlike (set twin: RuleSet): Prop := walkRuleSet blankPure set = walkRuleSet blankPure twin

def RulesAlike (rules twin: Rules): Prop := (walkRules blankPure rules).blank = (walkRules blankPure twin).blank

-- Facts about the functions in `Syntax/DeclParser.sw` that this file calls directly, each for every argument.

def ExpectFixedFollows: Prop :=
  ∀ (modes: Modes) (wanted: Tok) (what: Text) => Parse.Follows SameCode Anything
    (() => modes.expectFixed wanted what)
    (() => modes.expectFixed wanted what)

def LowerQualifiedFollows: Prop :=
  ∀ (modes: Modes) (what: Text) => Parse.Follows SameCode WordsAlike (() => modes.lowerQualified what) (() =>
    modes.lowerQualified what)

def AttributesOfFollows: Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode AttributesAlike (() => attributesOf modes) (() => attributesOf modes)

def DefinitionPartsFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (local: Option Nat) => Parse.Follows SameCode PartsAlike
    (() => definitionParts self modes None None local)
    (() => definitionParts selfTwin modes None None local)

-- Facts about the functions that `Syntax/FollowsLadder.sw` and the `Syntax/FollowsForms…` files cover, and whose
-- lemmas take many hypotheses.

def ExprInlineFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => exprInline self modes) (() => exprInline selfTwin modes)

def CalcOperandFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => calcOperand self modes) (() =>
    calcOperand selfTwin modes)

def AppendExprFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => appendExpr self modes) (() => appendExpr selfTwin modes)

def BlockFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) (column: Nat) (many: Bool) => Parse.Follows SameCode ExprsAlike
    (() => block self modes column many)
    (() => block selfTwin modes column many)

def ExprFollows (self selfTwin: Goal → {Parse Item} Expr): Prop :=
  ∀ (modes: Modes) => Parse.Follows SameCode ExprsAlike (() => expr self modes) (() => expr selfTwin modes)

-- Items the two runs read as the same code.

theorem indexSameOf ∀ (item other: Item) (same: SameCode item other): item.index = other.index :=
  deafItem Item.index (found => byComputing) item other same

theorem depthSameOf ∀ (item other: Item) (same: SameCode item other): item.depth = other.depth :=
  deafItem Item.depth (found => byComputing) item other same

-- Trees built from alike parts.

theorem afterBlank ∀ (found twin: Option (Comments, Expr))
    (alike: CommentedAlike found twin):
    blankAfter (walkAfter blankPure found) = blankAfter (walkAfter blankPure twin) :=
  match found, twin with
    | None, None => byComputing
    | Some (comments, value), Some (commentsTwin, valueTwin) =>
      calc blankAfter (walkAfter blankPure (Some (comments, value)))
        _ = Some (Comments.none, value.walk blankPure) := byComputing
        _ = Some (Comments.none, valueTwin.walk blankPure) := rewrite alike.right
        _ = blankAfter (walkAfter blankPure (Some (commentsTwin, valueTwin))) := byComputing

theorem alikeExprStatement ∀ (value twin: Expr)
    (values: ExprsAlike value twin):
    StatementsAlike (ExprStatement value) (ExprStatement twin) :=
  calc (walkStatement blankPure (ExprStatement value)).blank
    _ = ExprStatement (value.walk blankPure) := byComputing
    _ = ExprStatement (twin.walk blankPure) := rewrite values
    _ = (walkStatement blankPure (ExprStatement twin)).blank := byComputing

theorem alikeLetStatement ∀ (binding twin: Let)
    (lets: LetsAlike binding twin):
    StatementsAlike (LetStatement binding) (LetStatement twin) :=
  calc (walkStatement blankPure (LetStatement binding)).blank
    _ = LetStatement (walkLet blankPure binding).blank := byComputing
    _ = LetStatement (walkLet blankPure twin).blank := rewrite lets
    _ = (walkStatement blankPure (LetStatement twin)).blank := byComputing

theorem alikeLet ∀ (keyword keywordTwin: Comments) (pattern patternTwin: Pattern)
    (patterns: PatternsAlike pattern patternTwin) (annotation annotationTwin: Option (Comments, Expr))
    (annotations: CommentedAlike annotation annotationTwin)
    (colonEq colonEqTwin: Comments) (value valueTwin: Expr)
    (values: ExprsAlike value valueTwin):
    LetsAlike { keyword, pattern, annotation, colonEq, value } {
      keyword = keywordTwin,
      pattern = patternTwin,
      annotation = annotationTwin,
      colonEq = colonEqTwin,
      value = valueTwin
    } :=
  calc (walkLet blankPure { keyword, pattern, annotation, colonEq, value }).blank
    _ = {
        keyword = Comments.none,
        pattern = pattern.walk blankPure,
        annotation = blankAfter (walkAfter blankPure annotation),
        colonEq = Comments.none,
        value = value.walk blankPure
      } := byComputing
    _ = {
        keyword = Comments.none,
        pattern = patternTwin.walk blankPure,
        annotation = blankAfter (walkAfter blankPure annotationTwin),
        colonEq = Comments.none,
        value = valueTwin.walk blankPure
      } := rewrite patterns, afterBlank annotation annotationTwin annotations, values
    _ = (walkLet blankPure {
        keyword = keywordTwin,
        pattern = patternTwin,
        annotation = annotationTwin,
        colonEq = colonEqTwin,
        value = valueTwin
      }).blank := byComputing

theorem alikeLetIn ∀ (binding twin: Let)
    (lets: LetsAlike binding twin)
    (semicolon semicolonTwin: Comments) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ExprsAlike (LetIn binding semicolon body) (LetIn twin semicolonTwin bodyTwin) :=
  calc (LetIn binding semicolon body).walk blankPure
    _ = LetIn (walkLet blankPure binding).blank Comments.none (body.walk blankPure) := byComputing
    _ = LetIn (walkLet blankPure twin).blank Comments.none (bodyTwin.walk blankPure) := rewrite lets, bodies
    _ = (LetIn twin semicolonTwin bodyTwin).walk blankPure := byComputing

-- The two sides of a header's `unfolding` clause and a body's primitiveness are read by `localDef`.

theorem unfoldingKept ∀ (header: Header):
    (walkHeader blankPure header).unfoldingClause.isSome = header.unfoldingClause.isSome :=
  match header with
    | {
        exportKeyword,
        opaqueKeyword,
        kind,
        keyword,
        name,
        forallKeyword,
        params,
        colon,
        result,
        decreasingClause,
        unfoldingClause
      } =>
      match unfoldingClause with
        | Some (written, names) => byComputing
        | None => byComputing

theorem unfoldingSame ∀ (parts twin: (Header, DefBody))
    (alike: PartsAlike parts twin):
    parts.fst.unfoldingClause.isSome = twin.fst.unfoldingClause.isSome :=
  calc parts.fst.unfoldingClause.isSome
    _ = (walkHeader blankPure parts.fst).unfoldingClause.isSome := Eq.flipped (unfoldingKept parts.fst)
    _ = (walkHeader blankPure twin.fst).unfoldingClause.isSome :=
      Eq.cong (found => found.unfoldingClause.isSome) alike.left
    _ = twin.fst.unfoldingClause.isSome := unfoldingKept twin.fst

def BodyTag: DefBody → Nat
  | Primitive => 0
  | Assigned _ _ => 1
  | Arms _ => 2

theorem primitiveKept ∀ (body: DefBody): BodyTag (walkDefBody blankPure body).blank = BodyTag body := match body with
  | Primitive | Assigned _ _ | Arms _ => byComputing

theorem primitiveSame ∀ (parts twin: (Header, DefBody))
    (alike: PartsAlike parts twin):
    BodyTag parts.snd = BodyTag twin.snd :=
  calc BodyTag parts.snd
    _ = BodyTag (walkDefBody blankPure parts.snd).blank := Eq.flipped (primitiveKept parts.snd)
    _ = BodyTag (walkDefBody blankPure twin.snd).blank := Eq.cong BodyTag alike.right
    _ = BodyTag twin.snd := primitiveKept twin.snd

theorem alikeLocalDef ∀ (attributes twinAttributes: List Attributes)
    (attributeses: AttributesAlike attributes twinAttributes)
    (header twinHeader: Header) (body twinBody: DefBody)
    (parts: PartsAlike (header, body) (twinHeader, twinBody)):
    StatementsAlike (LocalDef attributes header body) (LocalDef twinAttributes twinHeader twinBody) :=
  calc (walkStatement blankPure (LocalDef attributes header body)).blank
    _ = LocalDef
        (walkAttributes blankPure attributes)
        (walkHeader blankPure header)
        (walkDefBody blankPure body).blank := byComputing
    _ = LocalDef
        (walkAttributes blankPure twinAttributes)
        (walkHeader blankPure twinHeader)
        (walkDefBody blankPure twinBody).blank := rewrite attributeses, parts.left, parts.right
    _ = (walkStatement blankPure (LocalDef twinAttributes twinHeader twinBody)).blank := byComputing

-- Where the next item is.

theorem followsHereOn ∀ (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode Same (() => hereOn items) (() => hereOn others) :=
  match items, others with
    | [], [] => Parse.followsMap (found => (found, 0)) (found => (found, 0)) followsOffset (found twin founds =>
      Eq.cong (n => (n, 0)) founds)
    | [item, ..rest], [other, ..restTwin] =>
      Parse.followsDone
        (Eq.cong2 (index depth => (index, depth)) (indexSameOf item other same.left) (depthSameOf item other same.left))

theorem followsHere: Parse.Follows SameCode Same (() => here()) (() => here()) := byWalking [followsHereOn]

theorem followsColumnHere: Parse.Follows SameCode Same (() => columnHere()) (() => columnHere()) :=
  followsLook columnOn columnOnDeaf

-- A local definition.

theorem followsLocalDefMatch ∀ (attributes twinAttributes: List Attributes)
    (attributeses: AttributesAlike attributes twinAttributes)
    (header twinHeader: Header) (body twinBody: DefBody)
    (parts: PartsAlike (header, body) (twinHeader, twinBody)):
    Parse.Follows SameCode StatementsAlike
      (() =>
        match header.unfoldingClause, body with
          | Some _, _ => Syntax.fatal "a local definition can't have `unfolding`"
          | None, Primitive => Syntax.fatal localNeedsBody
          | None, _ => LocalDef attributes header body)
      (() =>
        match twinHeader.unfoldingClause, twinBody with
          | Some _, _ => Syntax.fatal "a local definition can't have `unfolding`"
          | None, Primitive => Syntax.fatal localNeedsBody
          | None, _ => LocalDef twinAttributes twinHeader twinBody) :=
  let some: header.unfoldingClause.isSome = twinHeader.unfoldingClause.isSome :=
    unfoldingSame (header, body) (twinHeader, twinBody) parts
  let primitive: BodyTag body = BodyTag twinBody := primitiveSame (header, body) (twinHeader, twinBody) parts
  match header.unfoldingClause, twinHeader.unfoldingClause with
    | Some written, Some writtenTwin => followsFatalAny "a local definition can't have `unfolding`" (() =>
      Syntax.fatal "a local definition can't have `unfolding`")
    | None, None =>
      match body, twinBody with
        | Primitive, Primitive => followsFatalAny localNeedsBody (() => Syntax.fatal localNeedsBody)
        | Assigned colonEq value, Assigned colonEqTwin valueTwin =>
          Parse.followsDone (alikeLocalDef attributes twinAttributes attributeses header twinHeader _ _ parts)
        | Arms arms, Arms armsTwin =>
          Parse.followsDone (alikeLocalDef attributes twinAttributes attributeses header twinHeader _ _ parts)
        | Primitive, Assigned colonEqTwin valueTwin =>
          let clash := primitive
          cases
        | Primitive, Arms armsTwin =>
          let clash := primitive
          cases
        | Assigned colonEq value, Primitive =>
          let clash := primitive
          cases
        | Arms arms, Primitive =>
          let clash := primitive
          cases
        | Assigned colonEq value, Arms armsTwin =>
          let clash := primitive
          cases
        | Arms arms, Assigned colonEqTwin valueTwin =>
          let clash := primitive
          cases

theorem followsLocalDef ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (definitions: DefinitionPartsFollows self selfTwin)
    (modes: Modes) (attributes twinAttributes: List Attributes)
    (alike: AttributesAlike attributes twinAttributes):
    Parse.Follows SameCode StatementsAlike (() => localDef self modes attributes) (() =>
      localDef selfTwin modes twinAttributes) :=
  followsThenEq followsColumnHere (d =>
    Parse.followsThen (definitions modes (Some d)) (found twin parts =>
      match found, twin with
        | (header, body), (twinHeader, twinBody) =>
          followsLocalDefMatch attributes twinAttributes alike header twinHeader body twinBody parts))

-- `let`.

theorem followsLetAnnotation ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (atColon: Bool):
    Parse.Follows SameCode CommentedAlike (() => letAnnotation self modes atColon) (() =>
      letAnnotation selfTwin modes atColon) :=
  match atColon with
    | True => Parse.followsThen followsFixedFrom (colon colonTwin colons =>
      Parse.followsMap
        (annotation => Some (colon, annotation))
        (annotation => Some (colonTwin, annotation))
        (knot { modes = modes.sealed, level = LevelInline })
        (annotation annotationTwin annotations => (colons, annotations)))
    | False => Parse.followsDone Trivial

theorem followsLetEquals ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes) (depth: Nat)
    (keyword keywordTwin: Comments) (pattern patternTwin: Pattern)
    (patterns: PatternsAlike pattern patternTwin) (annotation annotationTwin: Option (Comments, Expr))
    (annotations: CommentedAlike annotation annotationTwin) (atEquals: Bool):
    Parse.Follows SameCode LetsAlike (() => letEquals self modes depth keyword pattern annotation atEquals) (() =>
      letEquals selfTwin modes depth keywordTwin patternTwin annotationTwin atEquals) :=
  match atEquals with
    | True => followsFatalAny defEquals (() => Syntax.fatal defEquals)
    | False => Parse.followsThen (expects modes ColonEq "`:=`") (colonEq colonEqTwin colonEqs =>
      Parse.followsMap
        (value => { keyword, pattern, annotation, colonEq, value })
        (value =>
          { keyword = keywordTwin, pattern = patternTwin, annotation = annotationTwin, colonEq = colonEqTwin, value })
        (followsFull knot { modes | letValue = Some depth })
        (value valueTwin values =>
          alikeLet keyword keywordTwin pattern patternTwin patterns annotation annotationTwin annotations colonEq
              colonEqTwin value valueTwin values))

theorem followsLetPatternOf ∀ (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => letPatternOf modes isCtor) (() => letPatternOf modes isCtor) :=
  match isCtor with
    | True => Parse.followsThen followsBump (name nameTwin names =>
      followsCtorArgs (goal => followsPattern patternRuleFollows goal) modes name nameTwin names (kind =>
        kind == Equals || kind == ColonEq || kind == Colon))
    | False => followsPattern patternRuleFollows { modes, level = PatternTupleComponent }

theorem followsLetPattern ∀ (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => letPattern modes) (() => letPattern modes) :=
  byWalking [followsCtorAhead, followsLetPatternOf]

theorem followsLetStatement ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes):
    Parse.Follows SameCode LetsAlike (() => letStatement self modes) (() => letStatement selfTwin modes) :=
  followsThenEq followsHere (found =>
    match found with
      | (index, depth) => Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
        Parse.followsThen (followsLetPattern modes) (bound boundTwin patterns =>
          Parse.followsThen
            (followsThenEq (followsAt modes Colon) (atColon => followsLetAnnotation knot modes atColon))
            (annotation annotationTwin annotations =>
              followsThenEq (followsAt modes Equals) (atEquals =>
                followsLetEquals knot expects modes depth keyword keywordTwin bound boundTwin patterns annotation
                    annotationTwin annotations atEquals)))))

theorem followsLetEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (binding twin: Let)
    (lets: LetsAlike binding twin)
    (semicolon semicolonTwin: Comments) (atEnd: Bool):
    Parse.Follows SameCode ExprsAlike (() => letEnd self modes binding semicolon atEnd) (() =>
      letEnd selfTwin modes twin semicolonTwin atEnd) :=
  match atEnd with
    | True => followsFatalAny "`let` needs a body after `;`: `(let x := e; body)`" (() =>
      Syntax.fatal "`let` needs a body after `;`: `(let x := e; body)`")
    | False =>
      Parse.followsMap
        (body => LetIn binding semicolon body)
        (body => LetIn twin semicolonTwin body)
        (followsFull knot modes)
        (body bodyTwin bodies => alikeLetIn binding twin lets semicolon semicolonTwin body bodyTwin bodies)

theorem followsLetBodyOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (binding twin: Let)
    (lets: LetsAlike binding twin) (atSemi: Bool):
    Parse.Follows SameCode ExprsAlike (() => letBodyOf self modes binding atSemi) (() =>
      letBodyOf selfTwin modes twin atSemi) :=
  match atSemi with
    | False => followsFail modes "`;` after the value of `let`" (() => modes.fail "`;` after the value of `let`")
    | True => Parse.followsThen followsFixedFrom (semicolon semicolonTwin semicolons =>
      Parse.followsThen followsLeft (seen others same =>
        rewrite deafOfStripped letAtEnd letAtEndDeaf seen others same then
          followsLetEnd knot modes binding twin lets semicolon semicolonTwin (letAtEnd others)))

theorem followsLetBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (binding twin: Let)
    (lets: LetsAlike binding twin):
    Parse.Follows SameCode ExprsAlike (() => letBody self modes binding) (() => letBody selfTwin modes twin) :=
  byWalking [followsLetBodyOf]

-- A line of a block.

theorem followsStatementValue ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (inlines: ExprInlineFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode StatementsAlike (() => statementValue self modes) (() => statementValue selfTwin modes) :=
  byWalking [] then alikeExprStatement _ _ exprInlineValueFacts

theorem followsLetStatementEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (bodies: LetBodyFollows self selfTwin)
    (modes: Modes) (binding twin: Let)
    (lets: LetsAlike binding twin) (atSemi: Bool):
    Parse.Follows SameCode StatementsAlike (() => letStatementEnd self modes binding atSemi) (() =>
      letStatementEnd selfTwin modes twin atSemi) :=
  byWalking [bodies modes binding twin lets, alikeLetStatement binding twin lets] then alikeExprStatement _ _
      letBodyValueFacts

theorem followsLocalAttributed ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (definitions: DefinitionPartsFollows self selfTwin)
    (allowed: Modes) (attributes twinAttributes: List Attributes)
    (alike: AttributesAlike attributes twinAttributes):
    Parse.Follows SameCode StatementsAlike
      (() => localAttributed self allowed attributes (allowed.at KwDef) (allowed.at KwTheorem))
      (() => localAttributed selfTwin allowed twinAttributes (allowed.at KwDef) (allowed.at KwTheorem)) :=
  followsThenEq (followsAt allowed KwDef) (atDef =>
    followsThenEq (followsAt allowed KwTheorem) (atTheorem =>
      match atDef || atTheorem with
        | True => followsLocalDef definitions allowed attributes twinAttributes alike
        | False => followsFatalAny (misplaced "a statement that isn't a local definition") (() =>
          Syntax.fatal (misplaced "a statement that isn't a local definition"))))

theorem followsAttributedLocal ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (definitions: DefinitionPartsFollows self selfTwin)
    (modes: Modes) (attributes twinAttributes: List Attributes)
    (alike: AttributesAlike attributes twinAttributes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode StatementsAlike (() => attributedLocal self modes attributes items) (() =>
      attributedLocal selfTwin modes twinAttributes others) :=
  rewrite deafOfStripped (allowedAt modes) (allowedAtDeaf modes) items others same then
    followsLocalAttributed definitions (allowedAt modes others) attributes twinAttributes alike

theorem followsStatementOther ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin) (attributesOfFact: AttributesOfFollows)
    (definitions: DefinitionPartsFollows self selfTwin)
    (modes: Modes) (kind: Tok):
    Parse.Follows SameCode StatementsAlike (() => statementOther self modes kind) (() =>
      statementOther selfTwin modes kind) :=
  byWalking [followsLetStatementEnd, followsLocalDef, followsAttributedLocal, followsFatalAny]

theorem followsStatementOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inlines: ExprInlineFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin) (attributesOfFact: AttributesOfFollows)
    (definitions: DefinitionPartsFollows self selfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode StatementsAlike (() => statementOn self modes seen) (() =>
      statementOn selfTwin modes seen) :=
  byWalking [followsStatementOther, followsStatementValue]

theorem followsStatement ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inlines: ExprInlineFollows self selfTwin)
    (lets: LetStatementFollows self selfTwin)
    (bodies: LetBodyFollows self selfTwin) (attributesOfFact: AttributesOfFollows)
    (definitions: DefinitionPartsFollows self selfTwin):
    StatementFollows self selfTwin :=
  modes =>
    followsPeeked modes (seen => statementOn self modes seen) (seen => statementOn selfTwin modes seen) (seen =>
      followsStatementOn knot inlines lets bodies attributesOfFact definitions modes seen)

-- Handler clauses and `match induct` arms: the trees.

theorem alikeReturnClause ∀ (bar barTwin keyword keywordTwin: Comments) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (arrow arrowTwin: Comments) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ClauseAlike
      (ReturnClause bar keyword name arrow body)
      (ReturnClause barTwin keywordTwin nameTwin arrowTwin bodyTwin) :=
  calc blankClauses (walkClauses blankPure [ReturnClause bar keyword name arrow body])
    _ = [ReturnClause Comments.none Comments.none name.blank Comments.none (body.walk blankPure)] := byComputing
    _ = [ReturnClause Comments.none Comments.none nameTwin.blank Comments.none (bodyTwin.walk blankPure)] :=
      rewrite names, bodies
    _ = blankClauses (walkClauses blankPure [ReturnClause barTwin keywordTwin nameTwin arrowTwin bodyTwin]) :=
      byComputing

theorem alikeOperationClause ∀ (bar barTwin: Comments) (operation operationTwin: Word)
    (operations: WordsAlike operation operationTwin) (argument argumentTwin: Pattern)
    (arguments: PatternsAlike argument argumentTwin)
    (comma commaTwin: Comments) (continuation continuationTwin: Word)
    (continuations: WordsAlike continuation continuationTwin)
    (arrow arrowTwin: Comments) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ClauseAlike
      (OperationClause bar operation argument comma continuation arrow body)
      (OperationClause barTwin operationTwin argumentTwin commaTwin continuationTwin arrowTwin bodyTwin) :=
  calc blankClauses (walkClauses blankPure [OperationClause bar operation argument comma continuation arrow body])
    _ = [
        OperationClause Comments.none operation.blank
          (argument.walk blankPure)
          Comments.none
          continuation.blank
          Comments.none
          (body.walk blankPure)
      ] := byComputing
    _ = [
        OperationClause Comments.none operationTwin.blank
          (argumentTwin.walk blankPure)
          Comments.none
          continuationTwin.blank
          Comments.none
          (bodyTwin.walk blankPure)
      ] := rewrite operations, arguments, continuations, bodies
    _ = blankClauses
        (walkClauses blankPure [
          OperationClause barTwin operationTwin argumentTwin commaTwin continuationTwin arrowTwin bodyTwin
        ]) := byComputing

theorem clausesBlankCons ∀ (clause: HandlerClause) (rest: List HandlerClause):
    blankClauses (walkClauses blankPure [clause, ..rest])
      = blankClauses (walkClauses blankPure [clause]) ++ blankClauses (walkClauses blankPure rest) :=
  match clause with | ReturnClause _ _ _ _ _ | OperationClause _ _ _ _ _ _ _ => byComputing

theorem clausesBlank ∀ (clauses twins: List HandlerClause)
    (alike: List.All2 ClauseAlike clauses twins):
    blankClauses (walkClauses blankPure clauses) = blankClauses (walkClauses blankPure twins) :=
  List.all2Join
    [f := list => blankClauses (walkClauses blankPure list)]
    [key := clause => blankClauses (walkClauses blankPure [clause])]
    (k rest => k ++ rest)
    clausesBlankCons
    (x y same => same)
    clauses
    twins
    alike

theorem alikeHandle ∀ (keyword keywordTwin: Comments) (computation computationTwin: Expr)
    (computations: ExprsAlike computation computationTwin)
    (withKeyword withKeywordTwin: Comments) (clauses twins: List HandlerClause)
    (alike: List.All2 ClauseAlike clauses twins):
    ExprsAlike
      (Handle keyword computation withKeyword clauses)
      (Handle keywordTwin computationTwin withKeywordTwin twins) :=
  calc (Handle keyword computation withKeyword clauses).walk blankPure
    _ = Handle Comments.none
        (computation.walk blankPure)
        Comments.none
        (blankClauses (walkClauses blankPure clauses)) := byComputing
    _ = Handle Comments.none
        (computationTwin.walk blankPure)
        Comments.none
        (blankClauses (walkClauses blankPure twins)) := rewrite computations, clausesBlank clauses twins alike
    _ = (Handle keywordTwin computationTwin withKeywordTwin twins).walk blankPure := byComputing

theorem alikeReify ∀ (keyword keywordTwin reify reifyTwin: Comments) (computation computationTwin: Expr)
    (computations: ExprsAlike computation computationTwin)
    (withKeyword withKeywordTwin: Comments) (clauses twins: List HandlerClause)
    (alike: List.All2 ClauseAlike clauses twins):
    ExprsAlike
      (Reify keyword reify computation withKeyword clauses)
      (Reify keywordTwin reifyTwin computationTwin withKeywordTwin twins) :=
  calc (Reify keyword reify computation withKeyword clauses).walk blankPure
    _ = Reify Comments.none Comments.none
        (computation.walk blankPure)
        Comments.none
        (blankClauses (walkClauses blankPure clauses)) := byComputing
    _ = Reify Comments.none Comments.none
        (computationTwin.walk blankPure)
        Comments.none
        (blankClauses (walkClauses blankPure twins)) := rewrite computations, clausesBlank clauses twins alike
    _ = (Reify keywordTwin reifyTwin computationTwin withKeywordTwin twins).walk blankPure := byComputing

theorem namesBlank ∀ (words twins: List Word)
    (alike: List.All2 WordsAlike words twins):
    blankWords words = blankWords twins :=
  List.all2Join
    [f := blankWords]
    [key := word => word.blank]
    (k rest => [k, ..rest])
    (x rest => byComputing)
    (x y same => same)
    words
    twins
    alike

theorem alikeInductArm ∀ (bar barTwin: Comments) (case caseTwin: Word)
    (kinds: WordsAlike case caseTwin) (names twins: List Word)
    (alike: List.All2 WordsAlike names twins)
    (arrow arrowTwin: Comments) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    InductArmAlike { bar, case, names, arrow, body } {
      bar = barTwin,
      case = caseTwin,
      names = twins,
      arrow = arrowTwin,
      body = bodyTwin
    } :=
  calc blankInductArms (walkInductArms blankPure [{ bar, case, names, arrow, body }])
    _ = [
        {
          bar = Comments.none,
          case = case.blank,
          names = blankWords names,
          arrow = Comments.none,
          body = body.walk blankPure
        }
      ] := byComputing
    _ = [
        {
          bar = Comments.none,
          case = caseTwin.blank,
          names = blankWords twins,
          arrow = Comments.none,
          body = bodyTwin.walk blankPure
        }
      ] := rewrite kinds, namesBlank names twins alike, bodies
    _ = blankInductArms
        (walkInductArms blankPure [
          { bar = barTwin, case = caseTwin, names = twins, arrow = arrowTwin, body = bodyTwin }
        ]) := byComputing

theorem inductArmsBlankCons ∀ (arm: InductArm) (rest: List InductArm):
    blankInductArms (walkInductArms blankPure [arm, ..rest])
      = blankInductArms (walkInductArms blankPure [arm]) ++ blankInductArms (walkInductArms blankPure rest) :=
  match arm with | { bar, case, names, arrow, body } => byComputing

theorem inductArmsBlank ∀ (arms twins: List InductArm)
    (alike: List.All2 InductArmAlike arms twins):
    blankInductArms (walkInductArms blankPure arms) = blankInductArms (walkInductArms blankPure twins) :=
  List.all2Join
    [f := list => blankInductArms (walkInductArms blankPure list)]
    [key := arm => blankInductArms (walkInductArms blankPure [arm])]
    (k rest => k ++ rest)
    inductArmsBlankCons
    (x y same => same)
    arms
    twins
    alike

theorem alikeInduct ∀ (keyword keywordTwin induct inductTwin: Comments) (call callTwin: Expr)
    (calls: ExprsAlike call callTwin)
    (withKeyword withKeywordTwin: Comments) (arms twins: List InductArm)
    (alike: List.All2 InductArmAlike arms twins):
    ExprsAlike
      (Induct keyword induct call withKeyword arms)
      (Induct keywordTwin inductTwin callTwin withKeywordTwin twins) :=
  calc (Induct keyword induct call withKeyword arms).walk blankPure
    _ = Induct Comments.none Comments.none
        (call.walk blankPure)
        Comments.none
        (blankInductArms (walkInductArms blankPure arms)) := byComputing
    _ = Induct Comments.none Comments.none
        (callTwin.walk blankPure)
        Comments.none
        (blankInductArms (walkInductArms blankPure twins)) := rewrite calls, inductArmsBlank arms twins alike
    _ = (Induct keywordTwin inductTwin callTwin withKeywordTwin twins).walk blankPure := byComputing

-- Handlers.

theorem followsHandlerName ∀ (lowers: LowerQualifiedFollows) (modes: Modes) (what: Text) (underscore: Bool):
    Parse.Follows SameCode WordsAlike (() => handlerName modes what underscore) (() =>
      handlerName modes what underscore) :=
  byWalking [followsLower]

theorem followsOperationEnd ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes) (bar barTwin: Comments) (operation operationTwin: Word)
    (operations: WordsAlike operation operationTwin) (argument argumentTwin: Pattern)
    (arguments: PatternsAlike argument argumentTwin)
    (comma commaTwin: Comments) (continuation continuationTwin: Word)
    (continuations: WordsAlike continuation continuationTwin) (atComma: Bool):
    Parse.Follows SameCode ClauseAlike
      (() => operationEnd self modes bar operation argument comma continuation atComma)
      (() => operationEnd selfTwin modes barTwin operationTwin argumentTwin commaTwin continuationTwin atComma) :=
  byWalking [followsFatalAny] then alikeOperationClause bar barTwin operation operationTwin operations argument
      argumentTwin arguments comma commaTwin continuation continuationTwin continuations arrow arrowTwin _ _
      fullValueFacts

theorem followsOperationClause ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (modes: Modes)
    (bar barTwin: Comments) (operation operationTwin: Word)
    (operations: WordsAlike operation operationTwin) (argument argumentTwin: Pattern)
    (arguments: PatternsAlike argument argumentTwin) (atArrow: Bool):
    Parse.Follows SameCode ClauseAlike (() => operationClause self modes bar operation argument atArrow) (() =>
      operationClause selfTwin modes barTwin operationTwin argumentTwin atArrow) :=
  match atArrow with
    | True => followsFatalAny "name the continuation: `| ${operation.text} x, k => …`" (() =>
      Syntax.fatal "name the continuation: `| ${operationTwin.text} x, k => …`")
    | False => Parse.followsThen (expects modes Comma "`,` and a name for the continuation") (comma commaTwin commas =>
      Parse.followsThen
        (followsThenEq (followsAt modes Underscore) (underscore =>
          followsHandlerName lowers modes "a name for the continuation" underscore))
        (continuation continuationTwin continuations =>
          followsThenEq (followsAt modes Comma) (atComma =>
            followsOperationEnd knot expects modes bar barTwin operation operationTwin operations argument argumentTwin
                arguments comma commaTwin continuation continuationTwin continuations atComma)))

theorem followsHandlerClauseOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (modes: Modes)
    (bar barTwin: Comments) (atReturn: Bool):
    Parse.Follows SameCode ClauseAlike (() => handlerClauseOf self modes bar atReturn) (() =>
      handlerClauseOf selfTwin modes barTwin atReturn) :=
  match atReturn with
    | True => Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
      Parse.followsThen
        (followsThenEq (followsAt modes Underscore) (underscore =>
          followsHandlerName lowers modes "a name for the result" underscore))
        (name nameTwin names =>
          Parse.followsThen (expects modes FatArrow "`=>`") (arrow arrowTwin arrows =>
            Parse.followsMap
              (body => ReturnClause bar keyword name arrow body)
              (body => ReturnClause barTwin keywordTwin nameTwin arrowTwin body)
              (followsFull knot modes)
              (body bodyTwin bodies =>
                alikeReturnClause bar barTwin keyword keywordTwin name nameTwin names arrow arrowTwin body bodyTwin
                    bodies))))
    | False => Parse.followsThen (lowers modes "an operation, or `return`") (op opTwin ops =>
      Parse.followsThen (patternOfFollows modes) (arg argTwin args =>
        followsThenEq (followsAt modes FatArrow) (atArrow =>
          followsOperationClause knot expects lowers modes bar barTwin op opTwin ops arg argTwin args atArrow)))

theorem followsHandlerClause ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (modes: Modes) (bar barTwin: Comments):
    Parse.Follows SameCode ClauseAlike (() => handlerClause self modes bar) (() =>
      handlerClause selfTwin modes barTwin) :=
  followsThenEq (followsAt modes KwReturn) (atReturn =>
    followsHandlerClauseOf knot expects lowers modes bar barTwin atReturn)

theorem followsClausesFrom ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (fuel: Nat) (modes: Modes)
    (column: Option Nat) (found foundTwin: List HandlerClause)
    (founds: List.All2 ClauseAlike found foundTwin):
    Parse.Follows SameCode (List.All2 ClauseAlike) (() => clausesFrom fuel self modes column found) (() =>
      clausesFrom fuel selfTwin modes column foundTwin) :=
  followsThenEq (followsArmColumn column) (columned =>
    match columned with
      | (lined, next) => followsThenEq (followsAt modes Pipe) (atPipe =>
        match fuel with
          | Zero => Parse.followsDone (List.all2Reverse found foundTwin founds)
          | Succ more =>
            match atPipe && lined with
              | True => Parse.followsThen followsFixedFrom (bar barTwin bars =>
                Parse.followsThen
                  (followsHandlerClause knot expects lowers modes bar barTwin)
                  (clause clauseTwin clauses =>
                    followsClausesFrom knot expects lowers more modes next
                      [clause, ..found]
                      [clauseTwin, ..foundTwin]
                      (Both clauses founds)))
              | False => Parse.followsDone (List.all2Reverse found foundTwin founds)))

theorem followsHandlerClausesEnd ∀ (modes: Modes) (clauses twins: List HandlerClause)
    (alike: List.All2 ClauseAlike clauses twins):
    Parse.Follows SameCode (List.All2 ClauseAlike) (() => handlerClausesEnd modes clauses) (() =>
      handlerClausesEnd modes twins) :=
  rewrite List.all2IsEmpty clauses twins alike then
    match twins.isEmpty with
      | True => followsFail modes "`|` and a handler clause" (() => modes.fail "`|` and a handler clause")
      | False => Parse.followsDone alike

theorem followsHandlerClauses ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (modes: Modes):
    Parse.Follows SameCode (List.All2 ClauseAlike) (() => handlerClauses self modes) (() =>
      handlerClauses selfTwin modes) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks =>
    rewrite <- marks.right.right then
      Parse.followsThen
        (followsClausesFrom knot expects lowers (here.left + 1) modes None [] [] Trivial)
        (clauses twins alike => followsHandlerClausesEnd modes clauses twins alike))

theorem followsHandleExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (modes: Modes):
    Parse.Follows SameCode ExprsAlike (() => handleExpr self modes) (() => handleExpr selfTwin modes) :=
  byWalking [followsFixedFrom, followsHandlerClauses] then alikeHandle keyword keywordTwin computation computationTwin
      computationFacts withKeyword withKeywordTwin _ _ handlerClausesValueFacts

theorem followsReifyComma ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (modes: Modes)
    (keyword keywordTwin reify reifyTwin: Comments) (computation computationTwin: Expr)
    (computations: ExprsAlike computation computationTwin) (comma: Bool):
    Parse.Follows SameCode ExprsAlike (() => reifyComma self modes keyword reify computation comma) (() =>
      reifyComma selfTwin modes keywordTwin reifyTwin computationTwin comma) :=
  byWalking [followsFatalAny, followsHandlerClauses] then alikeReify keyword keywordTwin reify reifyTwin computation
      computationTwin computations withKeyword withKeywordTwin _ _ handlerClausesValueFacts

theorem followsReifyExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows)
    (modes: Modes) (keyword keywordTwin reify reifyTwin: Comments):
    Parse.Follows SameCode ExprsAlike (() => reifyExpr self modes keyword reify) (() =>
      reifyExpr selfTwin modes keywordTwin reifyTwin) :=
  byWalking [followsReifyComma]

-- `match induct`.

theorem followsCaseNames ∀ (fuel: Nat) (modes: Modes) (found foundTwin: List Word)
    (founds: List.All2 WordsAlike found foundTwin):
    Parse.Follows SameCode (List.All2 WordsAlike) (() => caseNames fuel modes found) (() =>
      caseNames fuel modes foundTwin) :=
  followsPeeked modes
    (seen => caseNamesOn fuel modes found seen)
    (seen => caseNamesOn fuel modes foundTwin seen)
    (seen =>
      match fuel, seen with
        | Succ more, Some Lower => Parse.followsThen (followsLower modes "a name") (name nameTwin names =>
          followsCaseNames more modes [name, ..found] [nameTwin, ..foundTwin] (Both names founds))
        | Succ more, Some Underscore => Parse.followsThen followsBump (name nameTwin names =>
          followsCaseNames more modes [name, ..found] [nameTwin, ..foundTwin] (Both names founds))
        | _, _ => Parse.followsDone (List.all2Reverse found foundTwin founds))

theorem followsInductArms ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (fuel: Nat) (modes: Modes) (column: Option Nat) (found foundTwin: List InductArm)
    (founds: List.All2 InductArmAlike found foundTwin):
    Parse.Follows SameCode (List.All2 InductArmAlike) (() => inductArms fuel self modes column found) (() =>
      inductArms fuel selfTwin modes column foundTwin) :=
  followsThenEq (followsArmColumn column) (columned =>
    match columned with
      | (lined, next) => followsThenEq (followsAt modes Pipe) (atPipe =>
        match fuel with
          | Zero => Parse.followsDone (List.all2Reverse found foundTwin founds)
          | Succ more =>
            match atPipe && lined with
              | True => Parse.followsThen followsFixedFrom (bar barTwin bars =>
                Parse.followsThen (followsLower modes "the name of a case of `f.induct`") (label labelTwin labels =>
                  Parse.followsThen Parse.followsMark (here hereTwin marks =>
                    rewrite <- marks.right.right then
                      Parse.followsThen
                        (followsCaseNames (here.left + 1) modes [] [] Trivial)
                        (names namesTwin nameses =>
                          Parse.followsThen (expects modes FatArrow "`=>`") (arrow arrowTwin arrows =>
                            Parse.followsThen (followsFull knot modes) (body bodyTwin bodies =>
                              followsInductArms knot expects more modes next
                                [{ bar, case = label, names, arrow, body }, ..found]
                                [
                                  {
                                    bar = barTwin,
                                    case = labelTwin,
                                    names = namesTwin,
                                    arrow = arrowTwin,
                                    body = bodyTwin
                                  },
                                  ..foundTwin
                                ]
                                (Both
                                  (alikeInductArm bar barTwin label labelTwin labels names namesTwin nameses arrow
                                      arrowTwin body bodyTwin bodies)
                                  founds)))))))
              | False => Parse.followsDone (List.all2Reverse found foundTwin founds)))

theorem followsInductEnd ∀ (modes: Modes) (keyword keywordTwin induct inductTwin: Comments) (call callTwin: Expr)
    (calls: ExprsAlike call callTwin)
    (withKeyword withKeywordTwin: Comments) (arms twins: List InductArm)
    (alike: List.All2 InductArmAlike arms twins):
    Parse.Follows SameCode ExprsAlike (() => inductEnd modes keyword induct call withKeyword arms) (() =>
      inductEnd modes keywordTwin inductTwin callTwin withKeywordTwin twins) :=
  rewrite List.all2IsEmpty arms twins alike then
    match twins.isEmpty with
      | True => followsFail modes "`|` and an alternative named after a case" (() =>
        modes.fail "`|` and an alternative named after a case")
      | False =>
        Parse.followsDone
          (alikeInduct keyword keywordTwin induct inductTwin call callTwin calls withKeyword withKeywordTwin arms twins
              alike)

theorem followsInductComma ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes) (keyword keywordTwin induct inductTwin: Comments) (call callTwin: Expr)
    (calls: ExprsAlike call callTwin) (comma: Bool):
    Parse.Follows SameCode ExprsAlike (() => inductComma self modes keyword induct call comma) (() =>
      inductComma selfTwin modes keywordTwin inductTwin callTwin comma) :=
  match comma with
    | True => followsFatalAny "`match induct` takes one call, with nothing else to match" (() =>
      Syntax.fatal "`match induct` takes one call, with nothing else to match")
    | False => Parse.followsThen (expects modes KwWith "`with`") (withKeyword withKeywordTwin withKeywords =>
      Parse.followsThen Parse.followsMark (here hereTwin marks =>
        rewrite <- marks.right.right then
          Parse.followsThen
            (followsInductArms knot expects (here.left + 1) modes None [] [] Trivial)
            (arms twins alike =>
              followsInductEnd modes keyword keywordTwin induct inductTwin call callTwin calls withKeyword
                  withKeywordTwin arms twins alike)))

theorem followsInductExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes) (keyword keywordTwin induct inductTwin: Comments):
    Parse.Follows SameCode ExprsAlike (() => inductExpr self modes keyword induct) (() =>
      inductExpr selfTwin modes keywordTwin inductTwin) :=
  byWalking [followsInductComma]

-- `calc`: the trees.

def StepsAlike (found twin: (List CalcStep, Bool, Bool)): Prop :=
  PairAlike (List.All2 StepAlike) (PairAlike Same Same) found twin

theorem alikeStep ∀ (underscore underscoreTwin: Comments) (relation relationTwin: Word)
    (relations: WordsAlike relation relationTwin) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin) (proof proofTwin: Option (Comments, Expr))
    (proofs: CommentedAlike proof proofTwin):
    StepAlike { underscore, relation, operand, proof } {
      underscore = underscoreTwin,
      relation = relationTwin,
      operand = operandTwin,
      proof = proofTwin
    } :=
  calc blankCalcSteps (walkSteps blankPure [{ underscore, relation, operand, proof }])
    _ = [
        {
          underscore = Comments.none,
          relation = relation.blank,
          operand = operand.walk blankPure,
          proof = blankAfter (walkAfter blankPure proof)
        }
      ] := byComputing
    _ = [
        {
          underscore = Comments.none,
          relation = relationTwin.blank,
          operand = operandTwin.walk blankPure,
          proof = blankAfter (walkAfter blankPure proofTwin)
        }
      ] := rewrite relations, operands, afterBlank proof proofTwin proofs
    _ = blankCalcSteps
        (walkSteps blankPure [
          { underscore = underscoreTwin, relation = relationTwin, operand = operandTwin, proof = proofTwin }
        ]) := byComputing

theorem stepsBlankCons ∀ (step: CalcStep) (rest: List CalcStep):
    blankCalcSteps (walkSteps blankPure [step, ..rest])
      = blankCalcSteps (walkSteps blankPure [step]) ++ blankCalcSteps (walkSteps blankPure rest) :=
  match step with | { underscore, relation, operand, proof } => byComputing

theorem blankCalcStepsAlike ∀ (steps twins: List CalcStep)
    (alike: List.All2 StepAlike steps twins):
    blankCalcSteps (walkSteps blankPure steps) = blankCalcSteps (walkSteps blankPure twins) :=
  List.all2Join
    [f := list => blankCalcSteps (walkSteps blankPure list)]
    [key := step => blankCalcSteps (walkSteps blankPure [step])]
    (k rest => k ++ rest)
    stepsBlankCons
    (x y same => same)
    steps
    twins
    alike

theorem alikeCalc ∀ (keyword keywordTwin: Comments) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (steps twins: List CalcStep)
    (alike: List.All2 StepAlike steps twins):
    ExprsAlike (Calc keyword first steps) (Calc keywordTwin firstTwin twins) :=
  calc (Calc keyword first steps).walk blankPure
    _ = Calc Comments.none (first.walk blankPure) (blankCalcSteps (walkSteps blankPure steps)) := byComputing
    _ = Calc Comments.none (firstTwin.walk blankPure) (blankCalcSteps (walkSteps blankPure twins)) :=
      rewrite firsts, blankCalcStepsAlike steps twins alike
    _ = (Calc keywordTwin firstTwin twins).walk blankPure := byComputing

-- `calc`.

theorem followsCalcProof ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (colonEq: Bool):
    Parse.Follows SameCode CommentedAlike (() => calcProof self modes colonEq) (() =>
      calcProof selfTwin modes colonEq) :=
  byWalking [followsFixedFrom]

theorem followsStepSign ∀ (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode Same (() => stepSign modes seen) (() => stepSign modes seen) :=
  match seen with
    | Some Equals | Some Le | Some Lt | Some Ge | Some Gt => Parse.followsDone byComputing
    | Some NotEq | Some EqEq => followsFatalAny calcRelations (() => Syntax.fatal calcRelations)
    | _ => followsFail modes "`=`, `<=`, `<`, `>=` or `>` after `_`" (() =>
      modes.fail "`=`, `<=`, `<`, `>=` or `>` after `_`")

def CalcRest (self selfTwin: Goal → {Parse Item} Expr) (more: Nat) (modes: Modes) (indent place: Nat): Prop :=
  ∀ (found foundTwin: List CalcStep) (ascending descending: Bool) => List.All2 StepAlike found foundTwin
    → Parse.Follows SameCode StepsAlike
      (() => calcSteps more self modes indent (Some place) found ascending descending)
      (() => calcSteps more selfTwin modes indent (Some place) foundTwin ascending descending)

theorem followsCalcRecord ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (more: Nat) (modes: Modes) (indent place: Nat) (found foundTwin: List CalcStep)
    (founds: List.All2 StepAlike found foundTwin)
    (ascending descending: Bool) (underscore underscoreTwin: Comments) (relation relationTwin: Word)
    (relations: WordsAlike relation relationTwin) (operand operandTwin: Expr)
    (operands: ExprsAlike operand operandTwin) (colonEq: Bool)
    (rest: CalcRest self selfTwin more modes indent place):
    Parse.Follows SameCode StepsAlike
      (() => calcRecord more self modes indent place found ascending descending underscore relation operand colonEq)
      (() =>
        calcRecord more selfTwin modes indent place foundTwin ascending descending underscoreTwin relationTwin
            operandTwin colonEq) :=
  byWalking [followsCalcProof] then (
    alikeStep underscore underscoreTwin relation relationTwin relations operand operandTwin operands proof proofTwin
        proofFacts,
    founds
  )

theorem followsCalcRelation ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin)
    (more: Nat) (modes: Modes) (indent place: Nat) (found foundTwin: List CalcStep)
    (founds: List.All2 StepAlike found foundTwin)
    (ascending descending: Bool) (underscore underscoreTwin: Comments)
    (rest: CalcRest self selfTwin more modes indent place):
    Parse.Follows SameCode StepsAlike
      (() => calcRelation more self modes indent place found ascending descending underscore)
      (() => calcRelation more selfTwin modes indent place foundTwin ascending descending underscoreTwin) :=
  byWalking [followsCalcRecord]

theorem followsCalcLine ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin)
    (more: Nat) (modes: Modes) (indent place: Nat) (found foundTwin: List CalcStep)
    (founds: List.All2 StepAlike found foundTwin) (ascending descending: Bool)
    (rest: CalcRest self selfTwin more modes indent place):
    Parse.Follows SameCode StepsAlike (() => calcLine more self modes indent place found ascending descending) (() =>
      calcLine more selfTwin modes indent place foundTwin ascending descending) :=
  Parse.followsThen followsFixedFrom (underscore underscoreTwin underscores =>
    followsThenEq
      (followsPeeked modes (seen => stepSign modes seen) (seen => stepSign modes seen) (seen =>
        followsStepSign modes seen))
      (signs =>
        match signs with
          | (up, down) =>
            followsCalcRelation knot operands more modes indent place found foundTwin founds
              (ascending || up)
              (descending || down)
              underscore
              underscoreTwin
              rest))

theorem followsCalcSteps ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin)
    (fuel: Nat) (modes: Modes) (indent: Nat) (column: Option Nat) (found foundTwin: List CalcStep)
    (founds: List.All2 StepAlike found foundTwin) (ascending descending: Bool):
    Parse.Follows SameCode StepsAlike (() => calcSteps fuel self modes indent column found ascending descending) (() =>
      calcSteps fuel selfTwin modes indent column foundTwin ascending descending) :=
  followsOn
    (seen => calcStep fuel self modes indent column found ascending descending (calcNextOn modes indent seen))
    (seen => calcStep fuel selfTwin modes indent column foundTwin ascending descending (calcNextOn modes indent seen))
    (seen others same =>
      rewrite deafOfStripped (calcNextOn modes indent) (calcNextOnDeaf modes indent) seen others same then
        match fuel, calcNextOn modes indent others with
          | Succ more, Some place =>
            match column with
              | Some first =>
                match first != place with
                  | True => followsFatalAny "this step isn't lined up with the steps above it" (() =>
                    Syntax.fatal "this step isn't lined up with the steps above it")
                  | False =>
                    followsCalcLine knot operands more modes indent place found foundTwin founds ascending descending
                      (found foundTwin ascending descending founds =>
                        followsCalcSteps knot operands more modes indent
                          (Some place)
                          found
                          foundTwin
                          founds
                          ascending
                          descending)
              | None =>
                followsCalcLine knot operands more modes indent place found foundTwin founds ascending descending
                  (found foundTwin ascending descending founds =>
                    followsCalcSteps knot operands more modes indent
                      (Some place)
                      found
                      foundTwin
                      founds
                      ascending
                      descending)
          | _, _ => Parse.followsDone (List.all2Reverse found foundTwin founds, (byComputing, byComputing)))

theorem followsCalcEnd ∀ (inner: Modes) (keyword keywordTwin: Comments) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (steps twins: List CalcStep)
    (alike: List.All2 StepAlike steps twins) (ascending descending: Bool):
    Parse.Follows SameCode ExprsAlike (() => calcEnd inner keyword first steps ascending descending) (() =>
      calcEnd inner keywordTwin firstTwin twins ascending descending) :=
  rewrite List.all2IsEmpty steps twins alike then
    match twins.isEmpty with
      | True => followsFail inner "a step `_ = e` on the next line, indented past `calc`" (() =>
        inner.fail "a step `_ = e` on the next line, indented past `calc`")
      | False =>
        match ascending && descending with
          | True => followsFatalAny "a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`" (() =>
            Syntax.fatal "a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`")
          | False => Parse.followsDone (alikeCalc keyword keywordTwin first firstTwin firsts steps twins alike)

theorem followsCalcBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin)
    (inner: Modes) (indent: Nat) (keyword keywordTwin: Comments) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin):
    Parse.Follows SameCode ExprsAlike (() => calcBody self inner indent keyword first) (() =>
      calcBody selfTwin inner indent keywordTwin firstTwin) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks =>
    rewrite <- marks.right.right then
      Parse.followsThen
        (followsCalcSteps knot operands (here.left + 1) inner indent None [] [] Trivial False False)
        (found foundTwin alike =>
          match found, foundTwin with
            | (steps, ascending, descending), (twins, ascendingTwin, descendingTwin) =>
              rewrite <- alike.right.left, <- alike.right.right then
                followsCalcEnd inner keyword keywordTwin first firstTwin firsts steps twins alike.left ascending
                    descending))

theorem followsCalcAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin)
    (inner: Modes) (indent: Nat) (keyword keywordTwin: Comments) (first firstTwin: Expr)
    (firsts: ExprsAlike first firstTwin) (seen: Option Tok):
    Parse.Follows SameCode ExprsAlike (() => calcAfter self inner indent keyword first seen) (() =>
      calcAfter selfTwin inner indent keywordTwin firstTwin seen) :=
  match seen with
    | Some kind =>
      match kind.isComparison with
        | True => followsFatalAny "`calc` starts with one expression; each relation goes on a line of its own" (() =>
          Syntax.fatal "`calc` starts with one expression; each relation goes on a line of its own")
        | False => followsCalcBody knot operands inner indent keyword keywordTwin first firstTwin firsts
    | None => followsCalcBody knot operands inner indent keyword keywordTwin first firstTwin firsts

theorem followsCalcIndented ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin)
    (modes: Modes) (indent: Nat):
    Parse.Follows SameCode ExprsAlike (() => calcIndented self modes indent) (() =>
      calcIndented selfTwin modes indent) :=
  Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
    Parse.followsThen (operands { modes | inCalc = True }.sealed) (first firstTwin firsts =>
      followsPeeked
        { modes | inCalc = True }
        (seen => calcAfter self { modes | inCalc = True } indent keyword first seen)
        (seen => calcAfter selfTwin { modes | inCalc = True } indent keywordTwin firstTwin seen)
        (seen =>
          followsCalcAfter knot operands
            { modes | inCalc = True }
            indent
            keyword
            keywordTwin
            first
            firstTwin
            firsts
            seen)))

theorem followsCalcExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (operands: CalcOperandFollows self selfTwin):
    CalcFollows self selfTwin :=
  modes => followsThenEq followsHeadIndent (indent => followsCalcIndented knot operands modes indent)

-- `rewrite`: the trees.

def ReverseAlike (found twin: Option (Comments, Comments)): Prop :=
  Option.Alike (PairAlike Anything Anything) found twin

theorem reverseBlank ∀ (found twin: Option (Comments, Comments))
    (alike: ReverseAlike found twin):
    blankReverse found = blankReverse twin :=
  match found, twin with
    | None, None => byComputing
    | Some (first, second), Some (firstTwin, secondTwin) => byComputing

theorem alikeRule ∀ (reverse reverseTwin: Option (Comments, Comments))
    (reverses: ReverseAlike reverse reverseTwin) (rule ruleTwin: Expr)
    (rules: ExprsAlike rule ruleTwin):
    RuleAlike { reverse, rule } { reverse = reverseTwin, rule = ruleTwin } :=
  calc blankRuleList (walkRuleList blankPure [{ reverse, rule }])
    _ = [{ reverse = blankReverse reverse, rule = rule.walk blankPure }] := byComputing
    _ = [{ reverse = blankReverse reverseTwin, rule = ruleTwin.walk blankPure }] :=
      rewrite reverseBlank reverse reverseTwin reverses, rules
    _ = blankRuleList (walkRuleList blankPure [{ reverse = reverseTwin, rule = ruleTwin }]) := byComputing

theorem ruleListBlankCons ∀ (rule: RewriteRule) (rest: List RewriteRule):
    blankRuleList (walkRuleList blankPure [rule, ..rest])
      = blankRuleList (walkRuleList blankPure [rule]) ++ blankRuleList (walkRuleList blankPure rest) :=
  match rule with | { reverse, rule } => byComputing

theorem ruleListBlank ∀ (rules twins: List RewriteRule)
    (alike: List.All2 RuleAlike rules twins):
    blankRuleList (walkRuleList blankPure rules) = blankRuleList (walkRuleList blankPure twins) :=
  List.all2Join
    [f := list => blankRuleList (walkRuleList blankPure list)]
    [key := rule => blankRuleList (walkRuleList blankPure [rule])]
    (k rest => k ++ rest)
    ruleListBlankCons
    (x y same => same)
    rules
    twins
    alike

theorem alikeRuleList ∀ (rules twins: List RewriteRule)
    (alike: List.All2 RuleAlike rules twins):
    RulesAlike (RuleList rules) (RuleList twins) :=
  calc (walkRules blankPure (RuleList rules)).blank
    _ = RuleList (blankRuleList (walkRuleList blankPure rules)) := byComputing
    _ = RuleList (blankRuleList (walkRuleList blankPure twins)) := rewrite ruleListBlank rules twins alike
    _ = (walkRules blankPure (RuleList twins)).blank := byComputing

theorem alikeRepeatedly ∀ (word wordTwin: Comments) (set twin: RuleSet)
    (alike: RuleSetAlike set twin):
    RulesAlike (Repeatedly word set) (Repeatedly wordTwin twin) :=
  calc (walkRules blankPure (Repeatedly word set)).blank
    _ = Repeatedly Comments.none (walkRuleSet blankPure set) := byComputing
    _ = Repeatedly Comments.none (walkRuleSet blankPure twin) := rewrite alike
    _ = (walkRules blankPure (Repeatedly wordTwin twin)).blank := byComputing

theorem alikeRuleSet ∀ (open openTwin: Comments) (rules twins: List RewriteRule)
    (alike: List.All2 RuleAlike rules twins)
    (trailingComma: Bool) (close closeTwin: Comments):
    RuleSetAlike { open, rules, trailingComma, close } {
      open = openTwin,
      rules = twins,
      trailingComma,
      close = closeTwin
    } :=
  calc walkRuleSet blankPure { open, rules, trailingComma, close }
    _ = {
        open = Comments.none,
        rules = blankRuleList (walkRuleList blankPure rules),
        trailingComma,
        close = Comments.none
      } := byComputing
    _ = {
        open = Comments.none,
        rules = blankRuleList (walkRuleList blankPure twins),
        trailingComma,
        close = Comments.none
      } := rewrite ruleListBlank rules twins alike
    _ = walkRuleSet blankPure { open = openTwin, rules = twins, trailingComma, close = closeTwin } := byComputing

theorem alikeRewrite ∀ (keyword keywordTwin: Comments) (rules twinRules: Rules)
    (ruleses: RulesAlike rules twinRules) (target targetTwin: Option (Comments, Expr))
    (targets: CommentedAlike target targetTwin) (body bodyTwin: Option (Comments, Expr))
    (bodies: CommentedAlike body bodyTwin):
    ExprsAlike (Rewrite keyword rules target body) (Rewrite keywordTwin twinRules targetTwin bodyTwin) :=
  calc (Rewrite keyword rules target body).walk blankPure
    _ = Rewrite Comments.none
        (walkRules blankPure rules).blank
        (blankAfter (walkAfter blankPure target))
        (blankAfter (walkAfter blankPure body)) := byComputing
    _ = Rewrite Comments.none
        (walkRules blankPure twinRules).blank
        (blankAfter (walkAfter blankPure targetTwin))
        (blankAfter (walkAfter blankPure bodyTwin)) :=
      rewrite ruleses, afterBlank target targetTwin targets, afterBlank body bodyTwin bodies
    _ = (Rewrite keywordTwin twinRules targetTwin bodyTwin).walk blankPure := byComputing

theorem alikeCases ∀ (keyword keywordTwin thenKeyword thenKeywordTwin: Comments) (body bodyTwin: Expr)
    (bodies: ExprsAlike body bodyTwin):
    ExprsAlike (Cases keyword thenKeyword body) (Cases keywordTwin thenKeywordTwin bodyTwin) :=
  calc (Cases keyword thenKeyword body).walk blankPure
    _ = Cases Comments.none Comments.none (body.walk blankPure) := byComputing
    _ = Cases Comments.none Comments.none (bodyTwin.walk blankPure) := rewrite bodies
    _ = (Cases keywordTwin thenKeywordTwin bodyTwin).walk blankPure := byComputing

-- `rewrite`: the look-aheads.

theorem followsReverseOn ∀ (modes: Modes) (less: Bool) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode Same (() => reverseOn modes less items) (() => reverseOn modes less others) :=
  match items, others with
    | [], [] => Parse.followsDone byComputing
    | [first], [firstTwin] => Parse.followsDone byComputing
    | [first, minus, ..rest], [firstTwin, minusTwin, ..restTwin] =>
      match less with
        | True => followsThenEq (followsPeekAt modes 1) (second =>
          Parse.followsDone (Eq.cong (glued => reverseMinus glued second) (gluedSame minus minusTwin same.right.left)))
        | False => Parse.followsDone byComputing
    | [first], [firstTwin, minusTwin, ..restTwin] => same.right.impossible
    | [first, minus, ..rest], [firstTwin] => same.right.impossible

theorem followsReverseAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => reverseAhead modes) (() => reverseAhead modes) :=
  byWalking [followsReverseOn]

theorem followsReverseIf ∀ (reverse: Bool):
    Parse.Follows SameCode ReverseAlike (() => reverseIf reverse) (() => reverseIf reverse) :=
  byWalking [followsFixedFrom]

theorem followsReverseOf ∀ (modes: Modes):
    Parse.Follows SameCode ReverseAlike (() => reverseOf modes) (() => reverseOf modes) :=
  byWalking [followsReverseAhead, followsReverseIf]

theorem followsRepeatedlyOn ∀ (outer: Modes) (word: Bool):
    Parse.Follows SameCode Same (() => repeatedlyOn outer word) (() => repeatedlyOn outer word) :=
  byWalking [followsPeekAt]

theorem followsRepeatedlyAhead ∀ (outer: Modes):
    Parse.Follows SameCode Same (() => repeatedlyAhead outer) (() => repeatedlyAhead outer) :=
  byWalking [followsWordAhead, followsRepeatedlyOn]

theorem followsOwnLineAt ∀ (wanted: Tok) (column: Nat):
    Parse.Follows SameCode Same (() => ownLineAt wanted column) (() => ownLineAt wanted column) :=
  followsLook (ownLineOn wanted column) (ownLineOnDeaf wanted column)

theorem followsStartsOn ∀ (here: Bool) (wanted: Tok) (column: Nat):
    Parse.Follows SameCode Same (() => startsOn here wanted column) (() => startsOn here wanted column) :=
  byWalking [followsOwnLineAt]

theorem followsStartsAt ∀ (modes: Modes) (wanted: Tok) (column: Nat):
    Parse.Follows SameCode Same (() => startsAt modes wanted column) (() => startsAt modes wanted column) :=
  byWalking [followsStartsOn]

-- `rewrite`.

theorem followsRewriteBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (column: Nat) (keyword keywordTwin: Comments) (rules twinRules: Rules)
    (ruleses: RulesAlike rules twinRules) (target targetTwin: Option (Comments, Expr))
    (targets: CommentedAlike target targetTwin) (hasThen: Bool):
    Parse.Follows SameCode ExprsAlike (() => rewriteBody self modes column keyword rules target hasThen) (() =>
      rewriteBody selfTwin modes column keywordTwin twinRules targetTwin hasThen) :=
  byWalking [
    followsFixedFrom,
    alikeRewrite keyword keywordTwin rules twinRules ruleses target targetTwin targets None None Trivial
  ] then alikeRewrite keyword keywordTwin rules twinRules ruleses target targetTwin targets _ _ (
    thenKeywordFacts,
    bodyFacts
  )

theorem followsRewriteOldIn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (column: Nat) (keyword keywordTwin: Comments) (rules twinRules: Rules)
    (ruleses: RulesAlike rules twinRules) (target targetTwin: Option (Comments, Expr))
    (targets: CommentedAlike target targetTwin) (old: Bool):
    Parse.Follows SameCode ExprsAlike (() => rewriteOldIn self modes column keyword rules target old) (() =>
      rewriteOldIn selfTwin modes column keywordTwin twinRules targetTwin old) :=
  byWalking [followsFatalAny, followsStartsAt, followsRewriteBody]

theorem followsRewriteThen ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (column: Nat) (keyword keywordTwin: Comments) (rules twinRules: Rules)
    (ruleses: RulesAlike rules twinRules) (target targetTwin: Option (Comments, Expr))
    (targets: CommentedAlike target targetTwin):
    Parse.Follows SameCode ExprsAlike (() => rewriteThen self modes column keyword rules target) (() =>
      rewriteThen selfTwin modes column keywordTwin twinRules targetTwin) :=
  byWalking [followsStartsAt, followsRewriteOldIn]

theorem followsTargetOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (appends: AppendExprFollows self selfTwin)
    (modes: Modes) (written writtenTwin: Comments):
    Parse.Follows SameCode CommentedAlike (() => targetOf self modes written) (() =>
      targetOf selfTwin modes writtenTwin) :=
  byWalking [followsHere]

theorem followsTargetAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (appends: AppendExprFollows self selfTwin)
    (modes: Modes) (written writtenTwin: Comments) (seen: Option Tok):
    Parse.Follows SameCode CommentedAlike (() => targetAfter self modes written seen) (() =>
      targetAfter selfTwin modes writtenTwin seen) :=
  byWalking [followsFatalAny, followsTargetOf]

theorem followsRewriteTargetIf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (appends: AppendExprFollows self selfTwin)
    (modes: Modes) (atAhead: Bool):
    Parse.Follows SameCode CommentedAlike (() => rewriteTargetIf self modes atAhead) (() =>
      rewriteTargetIf selfTwin modes atAhead) :=
  match atAhead with
    | True => Parse.followsThen followsFixedFrom (written writtenTwin writtens =>
      followsThenEq (followsPeek modes) (seen => followsTargetAfter appends modes written writtenTwin seen))
    | False => Parse.followsDone Trivial

theorem followsRewriteTarget ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (appends: AppendExprFollows self selfTwin) (modes: Modes):
    Parse.Follows SameCode CommentedAlike (() => rewriteTarget self modes) (() => rewriteTarget selfTwin modes) :=
  followsThenEq (followsWordAhead modes "at") (atAhead => followsRewriteTargetIf appends modes atAhead)

theorem followsRewriteRule ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (appends: AppendExprFollows self selfTwin)
    (modes: Modes) (found foundTwin: List RewriteRule)
    (founds: List.All2 RuleAlike found foundTwin):
    Parse.Follows SameCode (List.All2 RuleAlike) (() => rewriteRule self modes found) (() =>
      rewriteRule selfTwin modes foundTwin) :=
  byWalking [followsReverseOf, followsHere] then (
    alikeRule reverse reverseTwin reverseFacts rule ruleTwin ruleFacts,
    founds
  )

theorem followsRewriteRules ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (appends: AppendExprFollows self selfTwin)
    (fuel: Nat) (modes: Modes) (found foundTwin: List RewriteRule)
    (founds: List.All2 RuleAlike found foundTwin):
    Parse.Follows SameCode (List.All2 RuleAlike) (() => rewriteRules fuel self modes found) (() =>
      rewriteRules fuel selfTwin modes foundTwin) :=
  Parse.followsThen (followsRewriteRule appends modes found foundTwin founds) (done doneTwin dones =>
    followsThenEq (followsAt modes Comma) (comma =>
      match fuel with
        | Succ more =>
          match comma with
            | True => Parse.followsThen followsBump (comma commaTwin commas =>
              followsRewriteRules appends more modes done doneTwin dones)
            | False => Parse.followsDone (List.all2Reverse done doneTwin dones)
        | Zero => Parse.followsDone (List.all2Reverse done doneTwin dones)))

def SetRulesAlike (found twin: (List RewriteRule, Bool)): Prop := PairAlike (List.All2 RuleAlike) Same found twin

theorem followsSetRule ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (found foundTwin: List RewriteRule)
    (founds: List.All2 RuleAlike found foundTwin):
    Parse.Follows SameCode (List.All2 RuleAlike) (() => setRule self modes found) (() =>
      setRule selfTwin modes foundTwin) :=
  byWalking [followsReverseOf] then (alikeRule reverse reverseTwin reverseFacts rule ruleTwin ruleFacts, founds)

theorem followsSetRules ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (fuel: Nat) (modes: Modes) (found foundTwin: List RewriteRule)
    (founds: List.All2 RuleAlike found foundTwin):
    Parse.Follows SameCode SetRulesAlike (() => setRules fuel self modes found) (() =>
      setRules fuel selfTwin modes foundTwin) :=
  Parse.followsThen (followsSetRule knot modes found foundTwin founds) (done doneTwin dones =>
    followsThenEq (followsAt modes Comma) (comma =>
      match fuel with
        | Succ more =>
          match comma with
            | True => Parse.followsThen followsBump (written writtenTwin writtens =>
              followsThenEq (followsAt modes RBracket) (closed =>
                match closed with
                  | True => Parse.followsDone (List.all2Reverse done doneTwin dones, byComputing)
                  | False => followsSetRules knot more modes done doneTwin dones))
            | False => Parse.followsDone (List.all2Reverse done doneTwin dones, byComputing)
        | Zero => Parse.followsDone (List.all2Reverse done doneTwin dones, byComputing)))

theorem followsRuleSetAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes) (open openTwin: Comments) (empty: Bool):
    Parse.Follows SameCode RuleSetAlike (() => ruleSetAfter self modes open empty) (() =>
      ruleSetAfter selfTwin modes openTwin empty) :=
  match empty with
    | True => followsFatalAny "`rewrite repeatedly` needs at least one rule between its brackets" (() =>
      Syntax.fatal "`rewrite repeatedly` needs at least one rule between its brackets")
    | False => Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsSetRules knot (here.left + 1) modes.inBrackets [] [] Trivial)
          (found foundTwin alike =>
            match found, foundTwin with
              | (rules, trailing), (twins, trailingTwin) =>
                rewrite <- alike.right then
                  Parse.followsThen (expects modes.inBrackets RBracket "`,` or `]`") (close closeTwin closes =>
                    Parse.followsDone (alikeRuleSet open openTwin rules twins alike.left trailing close closeTwin))))

theorem followsRuleSet ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (modes: Modes):
    Parse.Follows SameCode RuleSetAlike (() => ruleSet self modes) (() => ruleSet selfTwin modes) :=
  byWalking [followsFixedFrom, followsRuleSetAfter]

theorem followsRewriteRulesOf ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (expects: ExpectFixedFollows)
    (appends: AppendExprFollows self selfTwin)
    (outer: Modes) (repeatedly: Bool):
    Parse.Follows SameCode RulesAlike (() => rewriteRulesOf self outer repeatedly) (() =>
      rewriteRulesOf selfTwin outer repeatedly) :=
  match repeatedly with
    | True => Parse.followsThen followsFixedFrom (written writtenTwin writtens =>
      Parse.followsMap
        (set => Repeatedly written set)
        (set => Repeatedly writtenTwin set)
        (followsRuleSet knot expects outer)
        (set twin sets => alikeRepeatedly written writtenTwin set twin sets))
    | False => Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsMap
          (found => RuleList found)
          (found => RuleList found)
          (followsRewriteRules appends (here.left + 1) outer [] [] Trivial)
          (found twins alike => alikeRuleList found twins alike))

theorem followsRewriteWith ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (expects: ExpectFixedFollows)
    (appends: AppendExprFollows self selfTwin)
    (outer: Modes) (column: Nat) (keyword keywordTwin: Comments) (repeatedly: Bool):
    Parse.Follows SameCode ExprsAlike (() => rewriteWith self outer column keyword repeatedly) (() =>
      rewriteWith selfTwin outer column keywordTwin repeatedly) :=
  Parse.followsThen (followsRewriteRulesOf knot expects appends outer repeatedly) (rules twinRules ruleses =>
    Parse.followsThen (followsRewriteTarget appends outer) (target targetTwin targets =>
      followsRewriteThen knot outer column keyword keywordTwin rules twinRules ruleses target targetTwin targets))

theorem followsRewriteAfter ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (expects: ExpectFixedFollows)
    (appends: AppendExprFollows self selfTwin)
    (outer: Modes) (column: Nat) (keyword keywordTwin: Comments):
    Parse.Follows SameCode ExprsAlike (() => rewriteAfter self outer column keyword) (() =>
      rewriteAfter selfTwin outer column keywordTwin) :=
  followsThenEq (followsRepeatedlyAhead outer) (repeatedly =>
    followsRewriteWith knot expects appends outer column keyword keywordTwin repeatedly)

theorem followsRewriteExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (expects: ExpectFixedFollows)
    (appends: AppendExprFollows self selfTwin):
    RewriteFollows self selfTwin :=
  modes =>
    followsThenEq followsColumnHere (column =>
      Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
        followsRewriteAfter knot expects appends
          { modes | rewriteRule = None, rewriteAt = False }
          column
          keyword
          keywordTwin))

-- `cases` and the body after `then`.

theorem followsCasesThen ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (atThen: Bool):
    Parse.Follows SameCode ExprsAlike (() => casesThen self modes keyword atThen) (() =>
      casesThen selfTwin modes keywordTwin atThen) :=
  byWalking [followsFixedFrom, alikeAtom KwCases keyword keywordTwin keywords] then alikeCases keyword.comments
      keywordTwin.comments thenKeyword thenKeywordTwin _ _ selfValueFacts

theorem followsCasesIn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Word)
    (keywords: WordsAlike keyword keywordTwin) (atIn: Bool):
    Parse.Follows SameCode ExprsAlike (() => casesIn self modes keyword atIn) (() =>
      casesIn selfTwin modes keywordTwin atIn) :=
  byWalking [followsFatalAny, followsCasesThen]

theorem followsCasesExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    CasesFollows self selfTwin :=
  modes =>
    Parse.followsThen followsBump (keyword keywordTwin keywords =>
      followsThenEq (followsAt modes KwIn) (atIn => followsCasesIn knot modes keyword keywordTwin keywords atIn))

-- Walks: `byWalking [items] then t`.

theorem alikeWalk ∀ (keyword keywordTwin: Comments) (items itemsTwin: Expr)
    (itemses: ExprsAlike items itemsTwin) (body bodyTwin: Option (Comments, Expr))
    (bodies: CommentedAlike body bodyTwin):
    ExprsAlike (Walk keyword items body) (Walk keywordTwin itemsTwin bodyTwin) :=
  calc (Walk keyword items body).walk blankPure
    _ = Walk Comments.none (items.walk blankPure) (blankAfter (walkAfter blankPure body)) := byComputing
    _ = Walk Comments.none (itemsTwin.walk blankPure) (blankAfter (walkAfter blankPure bodyTwin)) :=
      rewrite itemses, afterBlank body bodyTwin bodies
    _ = (Walk keywordTwin itemsTwin bodyTwin).walk blankPure := byComputing

theorem followsWalkBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (keyword keywordTwin: Comments) (items itemsTwin: Expr)
    (itemses: ExprsAlike items itemsTwin) (hasThen: Bool):
    Parse.Follows SameCode ExprsAlike (() => walkBody self modes keyword items hasThen) (() =>
      walkBody selfTwin modes keywordTwin itemsTwin hasThen) :=
  byWalking [followsFixedFrom, alikeWalk keyword keywordTwin items itemsTwin itemses None None Trivial] then alikeWalk
      keyword keywordTwin items itemsTwin itemses _ _
      (thenKeywordFacts, bodyFacts)

theorem followsWalkFacts ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (modes: Modes) (column: Nat) (keyword keywordTwin: Comments) (items itemsTwin: Expr)
    (itemses: ExprsAlike items itemsTwin):
    Parse.Follows SameCode ExprsAlike (() => walkFacts self modes column keyword items) (() =>
      walkFacts selfTwin modes column keywordTwin itemsTwin) :=
  let spreads: hasSpread items = hasSpread itemsTwin := calc hasSpread items
    _ = hasSpread (items.walk blankPure) := hasSpreadDeaf items
    _ = hasSpread (itemsTwin.walk blankPure) := rewrite itemses
    _ = hasSpread itemsTwin := Eq.flipped (hasSpreadDeaf itemsTwin)
  rewrite spreads then
    match hasSpread itemsTwin with
      | True => followsFatalAny "a list of facts can't have a `..` spread" (() =>
        Syntax.fatal "a list of facts can't have a `..` spread")
      | False => followsThenEq (followsStartsAt modes KwThen column) (hasThen =>
        followsWalkBody knot modes keyword keywordTwin items itemsTwin itemses hasThen)

theorem followsWalkExpr ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    WalkFollows self selfTwin :=
  modes =>
    followsThenEq followsColumnHere (column =>
      Parse.followsThen followsFixedFrom (keyword keywordTwin keywords =>
        Parse.followsThen (followsListExpr knot modes) (list listTwin lists =>
          followsWalkFacts knot modes column keyword keywordTwin list listTwin lists)))

theorem followsThenBodyOn ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (blocks: BlockFollows self selfTwin)
    (exprs: ExprFollows self selfTwin)
    (modes: Modes) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode ExprsAlike (() => thenBodyOn self modes items) (() => thenBodyOn selfTwin modes others) :=
  match items, others with
    | [], [] => exprs modes
    | [next, ..rest], [other, ..restTwin] =>
      let ends: modes.endsConstruct next = modes.endsConstruct other :=
        deafItem (modes.endsConstruct) (endsConstructDeaf modes) next other same.left
      let guards: (next.leaf.token.lineStart
        && modes.allow != Some next.index
        && !modes.endsConstruct next
        && modes.limit == Some next.leaf.token.column)
        = (other.leaf.token.lineStart
          && modes.allow != Some other.index
          && !modes.endsConstruct other
          && modes.limit == Some other.leaf.token.column) :=
        rewrite ends,
            lineStartSame next other same.left,
            indexSameOf next other same.left,
            columnSame next other same.left
      let columns: next.leaf.token.column = other.leaf.token.column := columnSame next other same.left
      match first: next.leaf.token.lineStart
        && modes.allow != Some next.index
        && !modes.endsConstruct next
        && modes.limit == Some next.leaf.token.column, second: other.leaf.token.lineStart
        && modes.allow != Some other.index
        && !modes.endsConstruct other
        && modes.limit == Some other.leaf.token.column with
        | True, True => rewrite columns then blocks modes other.leaf.token.column True
        | False, False => exprs modes

theorem followsThenBody ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (blocks: BlockFollows self selfTwin)
    (exprs: ExprFollows self selfTwin):
    ThenBodyFollows self selfTwin :=
  modes =>
    followsOn (seen => thenBodyOn self modes seen) (seen => thenBodyOn selfTwin modes seen) (seen others same =>
      followsThenBodyOn blocks exprs modes seen others same)

-- The facts that `Syntax/FollowsForms.sw` and its continuations state about this file's functions (`StatementFollows`
-- and the rest), proved from the knot, the facts about `Syntax/DeclParser.sw`'s functions and those proved here.

theorem letStatementFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (expects: ExpectFixedFollows):
    LetStatementFollows self selfTwin :=
  modes => followsLetStatement knot expects modes

theorem letBodyFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin):
    LetBodyFollows self selfTwin :=
  modes binding twin alike => followsLetBody knot modes binding twin alike

theorem handleFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows):
    HandleFollows self selfTwin :=
  modes => followsHandleExpr knot expects lowers modes

theorem inductFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin) (expects: ExpectFixedFollows):
    InductFollows self selfTwin :=
  modes keyword keywordTwin word wordTwin => followsInductExpr knot expects modes keyword keywordTwin word wordTwin

theorem reifyFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows):
    ReifyFollows self selfTwin :=
  modes keyword keywordTwin word wordTwin =>
    followsReifyExpr knot expects lowers modes keyword keywordTwin word wordTwin

theorem appendExprFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows):
    AppendExprFollows self selfTwin :=
  modes => followsAppendExpr (matchFactsOf knot (inductFollows knot expects) (reifyFollows knot expects lowers)) modes

theorem rewriteFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows):
    RewriteFollows self selfTwin :=
  followsRewriteExpr knot expects (appendExprFollows knot expects lowers)

theorem calcOperandFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    CalcOperandFollows self selfTwin :=
  let header: HeaderFacts self selfTwin := { knot = knot, groups = groups, binders = binders }
  let matched := matchFactsOf knot (inductFollows knot expects) (reifyFollows knot expects lowers)
  let lambdas := lambdaFactsOf matched header
  modes =>
    Parse.followsThen (followsPipedRange lambdas modes) (piped pipedTwin pipeds =>
      followsLogicAfter (quantifierFactsOf (ifFactsOf lambdas) header results) modes piped pipedTwin pipeds)

theorem calcFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    CalcFollows self selfTwin :=
  followsCalcExpr knot (calcOperandFollows knot expects lowers groups binders results)

--| The tier 3 of the statement facts, built from the knot, the facts about `Syntax/DeclParser.sw`'s functions and the
--| header's, pi's and result type's.
def keywordFactsOf [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    KeywordFacts self selfTwin :=
  {
    below = {
      below = {
        below = { knot = knot, groups = groups, binders = binders },
        inducts = inductFollows knot expects,
        reifies = reifyFollows knot expects lowers
      },
      pis = pis,
      results = results
    },
    handles = handleFollows knot expects lowers,
    lets = letStatementFollows knot expects,
    bodies = letBodyFollows knot,
    calcs = calcFollows knot expects lowers groups binders results,
    rewrites = rewriteFollows knot expects lowers,
    casings = followsCasesExpr knot,
    walks = followsWalkExpr knot
  }

theorem exprInlineFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    ExprInlineFollows self selfTwin :=
  modes => followsExprInline (keywordFactsOf knot expects lowers groups binders pis results) modes

theorem statementFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (attributesOfFact: AttributesOfFollows)
    (definitions: DefinitionPartsFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    StatementFollows self selfTwin :=
  followsStatement knot
    (exprInlineFollows knot expects lowers groups binders pis results)
    (letStatementFollows knot expects)
    (letBodyFollows knot)
    attributesOfFact
    definitions

theorem thenBodyFollows ∀ [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (expects: ExpectFixedFollows) (lowers: LowerQualifiedFollows) (attributesOfFact: AttributesOfFollows)
    (definitions: DefinitionPartsFollows self selfTwin)
    (groups: HeaderGroupFollows self selfTwin)
    (binders: BinderTypeFollows self selfTwin)
    (pis: PiExprFollows self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    ThenBodyFollows self selfTwin :=
  let statements := statementFollows knot expects lowers attributesOfFact definitions groups binders pis results
  followsThenBody (modes column many => followsBlock statements modes column many) (modes =>
    followsExpr
      { below = keywordFactsOf knot expects lowers groups binders pis results, statements = statements }
      modes)
