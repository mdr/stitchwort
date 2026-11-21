--| The traversal with steps that can fail, against blanking (SW-4162): traversing a tree with its comments blanked
--| (`walk blankPure`) fails with the same message as traversing the tree, or finishes with the result blanked, when
--| each step does so on a node and its blanked form (`Blanks`). One theorem a traversal function, `…Blanks`, stated
--| on the form the function's input takes inside a blanked tree (`blankArms (walkArms blankPure arms)` for a match's
--| arms). `Fmt.Walk`'s `…Ok` family covers steps that can't fail; the lowering's checks can, so `loweringDeaf`
--| (`Syntax.DeafProofs`) rests on this family. Each arm follows the traversal's arm: one `Fail.toResultAlikeN` call for
--| each `seqN`, or, where the arm rebuilds a node and hands it to a step, one `Fail.toResultRebuildsN` call (imported
--| as `rebuildsN`); a change to the traversal needs the same change here. A data declaration's indices and body
--| have a lemma each (`indicesPartBlanks`, `bodyPartBlanks`), since the traversal computes them inline.
namespace Fmt.TraverseFail
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Std.Fail (
  toResultRebuilds1 as rebuilds1,
  toResultRebuilds2 as rebuilds2,
  toResultRebuilds3 as rebuilds3,
  toResultRebuilds4 as rebuilds4
)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)

--| Each of `on`'s steps, on a node blanked, fails as on the node, or finishes with its result blanked: the step
--| doesn't read comments, and keeps the blanking of what it returns.
type Blanks (on: Steps) = {
  expr: ∀ (z: Expr) => Fail.toResult (() => on.expr (z.walk blankPure))
    = (Fail.toResult (() => on.expr z)).map (x => x.walk blankPure),
  pattern: ∀ (z: Pattern) => Fail.toResult (() => on.pattern (z.walk blankPure))
    = (Fail.toResult (() => on.pattern z)).map (x => x.walk blankPure),
  header: ∀ (z: Header) => Fail.toResult (() => on.header (walkHeader blankPure z))
    = (Fail.toResult (() => on.header z)).map (x => walkHeader blankPure x),
  decl: ∀ (z: Decl) => Fail.toResult (() => on.decl (z.walk blankPure))
    = (Fail.toResult (() => on.decl z)).map (x => x.walk blankPure),
  fields: ∀ (z: Fields) => Fail.toResult (() => on.fields (z.walk blankPure))
    = (Fail.toResult (() => on.fields z)).map (x => x.walk blankPure),
  attributes: ∀ (z: Attributes) => Fail.toResult (() => on.attributes (blankAttributes z))
    = (Fail.toResult (() => on.attributes z)).map (x => blankAttributes x),
  ruleSet: ∀ (z: RuleSet) => Fail.toResult (() => on.ruleSet (walkRuleSet blankPure z))
    = (Fail.toResult (() => on.ruleSet z)).map (x => walkRuleSet blankPure x)
}

--| Traversing a blanked tree is blanking the traversed tree, failures included. By induction alongside the
--| traversal: each arm rebuilds its node around its children's runs, which agree with theirs on the blanked forms
--| (the induction hypotheses), so the node's run does by [`rebuilds1`] to [`rebuilds3`] and `Blanks`. The arms are
--| grouped by the children they traverse.
theorem exprBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Expr):
    runExpr on (input.walk blankPure) = (runExpr on input).map (x => x.walk blankPure) :=
  match input with
    | Atom _ _ | Unit _ _ | Universe _ _ | Include _ _ => deaf.expr input
    | Paren _ a _ | Spread _ a | RecordField _ _ a | NamedArg _ _ _ a _ | Section a | Prefix _ a | Facts _ _ a =>
      rebuilds1 deaf.expr (exprBlanks on deaf a) (v1 => byComputing)
    | Tuple _ a _ _ | ListOf _ a _ _ => rebuilds1 deaf.expr (exprsBlanks on deaf a) (v1 => byComputing)
    | FieldAccess a _ _ => rebuilds1 deaf.expr (optionalBlanks deaf a) (v1 => byComputing)
    | Interpolated a => rebuilds1 deaf.expr (piecesBlanks on deaf a) (v1 => byComputing)
    | ClauseLambda _ _ a => rebuilds1 deaf.expr (armsBlanks on deaf a) (v1 => byComputing)
    | Cases _ _ a => rebuilds1 deaf.expr (afterBlanks deaf a) (v1 => byComputing)
    | CtorFields a b | Infix _ a _ b | Annotation _ a _ b _ =>
      rebuilds2 deaf.expr (exprBlanks on deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
    | App a b => rebuilds2 deaf.expr (exprBlanks on deaf a) (exprsBlanks on deaf b) (v1 v2 => byComputing)
    | Record _ a b _ _ => rebuilds2 deaf.expr (beforeBlanks on deaf a) (exprsBlanks on deaf b) (v1 v2 => byComputing)
    | OperatorSection _ a _ b _ =>
      rebuilds2 deaf.expr (optionalBlanks deaf a) (optionalBlanks deaf b) (v1 v2 => byComputing)
    | Chain a b => rebuilds2 deaf.expr (exprBlanks on deaf a) (linksBlanks on deaf b) (v1 v2 => byComputing)
    | Binding _ _ a _ b => rebuilds2 deaf.expr (paramsBlanks on deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
    | Match _ a _ b => rebuilds2 deaf.expr (scrutineesBlanks on deaf a) (armsBlanks on deaf b) (v1 v2 => byComputing)
    | FunctionType a _ b => rebuilds2 deaf.expr (groupBlanks deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
    | Effect a b => rebuilds2 deaf.expr (rowBlanks on deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
    | LetIn a _ b => rebuilds2 deaf.expr (letBlanks on deaf a) (exprBlanks on deaf b) (v1 v2 => byComputing)
    | Handle _ a _ b | Reify _ _ a _ b =>
      rebuilds2 deaf.expr (exprBlanks on deaf a) (clausesBlanks on deaf b) (v1 v2 => byComputing)
    | Induct _ _ a _ b => rebuilds2 deaf.expr (exprBlanks on deaf a) (inductArmsBlanks on deaf b) (v1 v2 => byComputing)
    | Calc _ a b => rebuilds2 deaf.expr (exprBlanks on deaf a) (calcStepsBlanks on deaf b) (v1 v2 => byComputing)
    | Walk _ a b => rebuilds2 deaf.expr (exprBlanks on deaf a) (afterBlanks deaf b) (v1 v2 => byComputing)
    | If _ _ a _ b _ c =>
      rebuilds3 deaf.expr (exprBlanks on deaf a) (exprBlanks on deaf b) (exprBlanks on deaf c) (v1 v2 v3 => byComputing)
    | Block a b c =>
      rebuilds3 deaf.expr (statementBlanks on deaf a) (statementsBlanks on deaf b) (exprBlanks on deaf c) (v1 v2 v3 =>
        byComputing)
    | Rewrite _ a b c =>
      rebuilds3 deaf.expr (rulesBlanks on deaf a) (afterBlanks deaf b) (afterBlanks deaf c) (v1 v2 v3 => byComputing)

theorem statementsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Statement):
    runStatements on (blankStatements (walkStatements blankPure input))
      = (runStatements on input).map (x => blankStatements (walkStatements blankPure x)) :=
  match input with
    | [] => byComputing
    | [first, ..rest] =>
      Fail.toResultAlike2 (statementBlanks on deaf first) (statementsBlanks on deaf rest) (v1 v2 => byComputing)

theorem statementBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Statement):
    runStatement on ((walkStatement blankPure input).blank)
      = (runStatement on input).map (x => (walkStatement blankPure x).blank) :=
  match input with
    | LetStatement binding => Fail.toResultAlike1 (letBlanks on deaf binding) (v1 => byComputing)
    | LocalDef attributes header body =>
      Fail.toResultAlike3
        (attributesBlanks on deaf attributes)
        (headerBlanks on deaf header)
        (defBodyBlanks on deaf body)
        (v1 v2 v3 => byComputing)
    | ExprStatement value => Fail.toResultAlike1 (exprBlanks on deaf value) (v1 => byComputing)

theorem letBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Let):
    runLet on ((walkLet blankPure input).blank) = (runLet on input).map (x => (walkLet blankPure x).blank) :=
  match input with
    | { keyword, pattern, annotation, colonEq, value } =>
      Fail.toResultAlike3
        (patternBlanks on deaf pattern)
        (afterBlanks deaf annotation)
        (exprBlanks on deaf value)
        (v1 v2 v3 => byComputing)

theorem clausesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List HandlerClause):
    runClauses on (blankClauses (walkClauses blankPure input))
      = (runClauses on input).map (x => blankClauses (walkClauses blankPure x)) :=
  match input with
    | [] => byComputing
    | [ReturnClause bar keyword name arrow body, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf body) (clausesBlanks on deaf rest) (v1 v2 => byComputing)
    | [OperationClause bar operation argument comma continuation arrow body, ..rest] =>
      Fail.toResultAlike3
        (patternBlanks on deaf argument)
        (exprBlanks on deaf body)
        (clausesBlanks on deaf rest)
        (v1 v2 v3 => byComputing)

theorem inductArmsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List InductArm):
    runInductArms on (blankInductArms (walkInductArms blankPure input))
      = (runInductArms on input).map (x => blankInductArms (walkInductArms blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf body) (inductArmsBlanks on deaf rest) (v1 v2 => byComputing)

theorem calcStepsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List CalcStep):
    runCalcSteps on (blankCalcSteps (walkSteps blankPure input))
      = (runCalcSteps on input).map (x => blankCalcSteps (walkSteps blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] =>
      Fail.toResultAlike3
        (exprBlanks on deaf operand)
        (afterBlanks deaf proof)
        (calcStepsBlanks on deaf rest)
        (v1 v2 v3 => byComputing)

theorem rulesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Rules):
    runRules on ((walkRules blankPure input).blank) = (runRules on input).map (x => (walkRules blankPure x).blank) :=
  match input with
    | RuleList rules => Fail.toResultAlike1 (ruleListBlanks on deaf rules) (v1 => byComputing)
    | Repeatedly word set => Fail.toResultAlike1 (ruleSetBlanks on deaf set) (v1 => byComputing)

theorem ruleSetBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: RuleSet):
    runRuleSet on (walkRuleSet blankPure input) = (runRuleSet on input).map (x => walkRuleSet blankPure x) :=
  match input with
    | { open, rules, trailingComma, close } =>
      Fail.toResultAlike1Let
        [g2 := v1 => { open = Comments.none, rules = v1, trailingComma, close = Comments.none }]
        (ruleListBlanks on deaf rules)
        (v1 => deaf.ruleSet ({ open, rules = v1, trailingComma, close }))

theorem ruleListBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List RewriteRule):
    runRuleList on (blankRuleList (walkRuleList blankPure input))
      = (runRuleList on input).map (x => blankRuleList (walkRuleList blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf rule) (ruleListBlanks on deaf rest) (v1 v2 => byComputing)

theorem rowBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Row):
    runRow on ((walkRow blankPure input).blank) = (runRow on input).map (x => (walkRow blankPure x).blank) :=
  match input with
    | { open, abilities, variable, close } => Fail.toResultAlike1 (exprsBlanks on deaf abilities) (v1 => byComputing)

theorem exprsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Expr):
    runExprs on (walkExprs blankPure input) = (runExprs on input).map (x => walkExprs blankPure x) :=
  match input with
    | [] => byComputing
    | [first, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf first) (exprsBlanks on deaf rest) (v1 v2 => byComputing)

theorem linksBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List (Word, Expr)):
    runLinks on (blankLinks (walkLinks blankPure input))
      = (runLinks on input).map (x => blankLinks (walkLinks blankPure x)) :=
  match input with
    | [] => byComputing
    | [(operator, operand), ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf operand) (linksBlanks on deaf rest) (v1 v2 => byComputing)

theorem piecesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Piece):
    runPieces on (blankPieces (walkPieces blankPure input))
      = (runPieces on input).map (x => blankPieces (walkPieces blankPure x)) :=
  match input with
    | [] => byComputing
    | [TextPiece word, ..rest] => Fail.toResultAlike1 (piecesBlanks on deaf rest) (v1 => byComputing)
    | [Interpolation open value close, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf value) (piecesBlanks on deaf rest) (v1 v2 => byComputing)

theorem scrutineesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Scrutinee):
    runScrutinees on (blankScrutinees (walkScrutinees blankPure input))
      = (runScrutinees on input).map (x => blankScrutinees (walkScrutinees blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ name, value }, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf value) (scrutineesBlanks on deaf rest) (v1 v2 => byComputing)

theorem armsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Arm):
    runArms on (blankArms (walkArms blankPure input))
      = (runArms on input).map (x => blankArms (walkArms blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] =>
      Fail.toResultAlike4
        (patternsBlanks on deaf patterns)
        (guardBlanks on deaf guard)
        (afterWordBlanks on deaf body)
        (armsBlanks on deaf rest)
        (v1 v2 v3 v4 => byComputing)

theorem paramsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Param):
    runParams on (blankParams (walkParams blankPure input))
      = (runParams on input).map (x => blankParams (walkParams blankPure x)) :=
  match input with
    | [] => byComputing
    | [NameParam word, ..rest] => Fail.toResultAlike1 (paramsBlanks on deaf rest) (v1 => byComputing)
    | [PatternParam pattern, ..rest] =>
      Fail.toResultAlike2 (patternBlanks on deaf pattern) (paramsBlanks on deaf rest) (v1 v2 => byComputing)
    | [Grouped group, ..rest] =>
      Fail.toResultAlike2 (groupBlanks deaf group) (paramsBlanks on deaf rest) (v1 v2 => byComputing)
    | [TypedPattern open pattern colon annotation close, ..rest] =>
      Fail.toResultAlike3
        (patternBlanks on deaf pattern)
        (exprBlanks on deaf annotation)
        (paramsBlanks on deaf rest)
        (v1 v2 v3 => byComputing)

theorem groupBlanks ∀ [on: Steps]
    (deaf: Blanks on) (input: Group):
    runGroup on ((input.walk blankPure).blank) = (runGroup on input).map (x => (x.walk blankPure).blank) :=
  match input with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
      Fail.toResultAlike3
        (attributesBlanks on deaf attributes)
        (optionalBlanks deaf annotation)
        (afterBlanks deaf default)
        (v1 v2 v3 => byComputing)

theorem patternBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Pattern):
    runPattern on (input.walk blankPure) = (runPattern on input).map (x => x.walk blankPure) :=
  match input with
    | PatternWord _ _ | PatternNegative _ _ | PatternAbsurd _ _ => deaf.pattern input
    | PatternCtor _ a | PatternTuple _ a _ _ => rebuilds1 deaf.pattern (patternsBlanks on deaf a) (v1 => byComputing)
    | PatternCtorFields _ a | PatternRecord a =>
      rebuilds1 deaf.pattern (fieldsPatternBlanks on deaf a) (v1 => byComputing)
    | PatternNamed _ _ _ a _ | PatternParen _ a _ =>
      rebuilds1 deaf.pattern (patternBlanks on deaf a) (v1 => byComputing)
    | PatternList _ a _ b _ =>
      rebuilds2 deaf.pattern (patternsBlanks on deaf a) (tailBlanks on deaf b) (v1 v2 => byComputing)
    | PatternOr a b =>
      rebuilds2 deaf.pattern (patternBlanks on deaf a) (patternLinksBlanks on deaf b) (v1 v2 => byComputing)
    | PatternAppend a _ b =>
      rebuilds2 deaf.pattern (patternBlanks on deaf a) (patternBlanks on deaf b) (v1 v2 => byComputing)

theorem patternsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Pattern):
    runPatterns on (walkPatterns blankPure input) = (runPatterns on input).map (x => walkPatterns blankPure x) :=
  match input with
    | [] => byComputing
    | [first, ..rest] =>
      Fail.toResultAlike2 (patternBlanks on deaf first) (patternsBlanks on deaf rest) (v1 v2 => byComputing)

theorem patternLinksBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List (Word, Pattern)):
    runPatternLinks on (blankLinks (walkPatternLinks blankPure input))
      = (runPatternLinks on input).map (x => blankLinks (walkPatternLinks blankPure x)) :=
  match input with
    | [] => byComputing
    | [(bar, alternative), ..rest] =>
      Fail.toResultAlike2 (patternBlanks on deaf alternative) (patternLinksBlanks on deaf rest) (v1 v2 => byComputing)

theorem fieldsPatternBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: FieldsPattern):
    runFieldsPattern on ((walkFields blankPure input).blank)
      = (runFieldsPattern on input).map (x => (walkFields blankPure x).blank) :=
  match input with
    | { open, fields, trailingComma, rest, close } =>
      Fail.toResultAlike1 (fieldPatternsBlanks on deaf fields) (v1 => byComputing)

theorem fieldPatternsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List FieldPattern):
    runFieldPatterns on (blankFieldPatterns (walkFieldPatterns blankPure input))
      = (runFieldPatterns on input).map (x => blankFieldPatterns (walkFieldPatterns blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ name, value = Some (equals, pattern) }, ..rest] =>
      Fail.toResultAlike2 (patternBlanks on deaf pattern) (fieldPatternsBlanks on deaf rest) (v1 v2 => byComputing)
    | [{ name, value = None }, ..rest] => Fail.toResultAlike1 (fieldPatternsBlanks on deaf rest) (v1 => byComputing)

--| The traversal's work on a data declaration's indices, as `Decl.traverse` does it inline.
def indicesPart (on: Steps) (indices: Option Indices): {Fail} Option Indices := match indices with
  | Some { colon, steps, last } => Some { colon, steps = traverseIndices on steps, last = last.traverse on }
  | None => None

--| A data declaration's indices as walking with `blankPure` leaves them, and then `blankDecl` blanking them.
def blankedIndices (indices: Option Indices): Option Indices :=
  (match indices with
        | Some { colon, steps, last } => Some { colon, steps = walkIndices blankPure steps, last = last.walk blankPure }
        | None => None).map Indices.blank

--| The traversal's work on a data declaration's body, as `Decl.traverse` does it inline.
def bodyPart (on: Steps) (body: DataBody): {Fail} DataBody := match body with
  | Abstract => Abstract
  | Synonym equals annotation => Synonym equals (annotation.traverse on)
  | RecordBody equals fields => RecordBody equals (fields.traverse on)
  | Sum equals constructors => Sum equals (traverseConstructors on constructors)

--| A data declaration's body as walking with `blankPure` leaves it, and then `blankDecl` blanking it.
def blankedBody (body: DataBody): DataBody :=
  (match body with
    | Abstract => Abstract
    | Synonym equals annotation => Synonym equals (annotation.walk blankPure)
    | RecordBody equals fields => RecordBody equals (fields.walk blankPure)
    | Sum equals constructors => Sum equals (walkConstructors blankPure constructors)).blank

--| The traversal of a data declaration's body, blanked, fails as on the body or finishes with the result blanked:
--| the run on what the body holds does (`exprBlanks`, `fieldsBlanks`, `constructorsBlanks`).
theorem bodyPartBlanks ∀ (on: Steps)
    (deaf: Blanks on) (body: DataBody):
    Fail.toResult (() => bodyPart on (blankedBody body)) = (Fail.toResult (() => bodyPart on body)).map blankedBody :=
  match body with
    | Abstract => byComputing
    | Synonym equals annotation => Fail.toResultAlike1 (exprBlanks on deaf annotation) (w1 => byComputing)
    | RecordBody equals fields => Fail.toResultAlike1 (fieldsBlanks deaf fields) (w1 => byComputing)
    | Sum equals constructors => Fail.toResultAlike1 (constructorsBlanks on deaf constructors) (w1 => byComputing)

--| The traversal of a data declaration's indices, blanked, fails as on the indices or finishes with the result
--| blanked: the steps' (`indicesBlanks`) and the last expression's (`exprBlanks`) runs do.
theorem indicesPartBlanks ∀ (on: Steps)
    (deaf: Blanks on) (indices: Option Indices):
    Fail.toResult (() => indicesPart on (blankedIndices indices))
      = (Fail.toResult (() => indicesPart on indices)).map blankedIndices :=
  match indices with
    | Some { colon, steps, last } =>
      Fail.toResultAlike2 (indicesBlanks on deaf steps) (exprBlanks on deaf last) (w1 w2 => byComputing)
    | None => byComputing

theorem declBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Decl):
    runDecl on (input.walk blankPure) = (runDecl on input).map (x => x.walk blankPure) :=
  match input with
    | Namespace _ _ | Import _ _ _ _ _ => deaf.decl input
    | Definition a b c =>
      rebuilds3 deaf.decl (attributesBlanks on deaf a) (headerBlanks on deaf b) (defBodyBlanks on deaf c) (v1 v2 v3 =>
        byComputing)
    | Data a _ _ _ b c d =>
      rebuilds4 deaf.decl
        (attributesBlanks on deaf a)
        (groupsBlanks on deaf b)
        (indicesPartBlanks on deaf c)
        (bodyPartBlanks on deaf d)
        (v1 v2 v3 v4 => byComputing)
    | Ability _ _ a _ b =>
      rebuilds2 deaf.decl (groupsBlanks on deaf a) (operationsBlanks on deaf b) (v1 v2 => byComputing)
    | Test _ _ _ a => rebuilds1 deaf.decl (exprBlanks on deaf a) (v1 => byComputing)
    | RuleSetDecl _ _ _ a => rebuilds1 deaf.decl (ruleSetBlanks on deaf a) (v1 => byComputing)

theorem headerBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Header):
    runHeader on (walkHeader blankPure input) = (runHeader on input).map (x => walkHeader blankPure x) :=
  match input with
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
      Fail.toResultAlike3Let
        [g2 := v1 v2 v3 =>
          {
            exportKeyword = blankComments exportKeyword,
            opaqueKeyword = blankComments opaqueKeyword,
            kind,
            keyword = Comments.none,
            name = name.blank,
            forallKeyword = forallKeyword.map Word.blank,
            params = v1,
            colon = Comments.none,
            result = v2,
            decreasingClause = v3,
            unfoldingClause = blankUnfolding unfoldingClause
          }]
        (groupsBlanks on deaf params)
        (exprBlanks on deaf result)
        (afterBlanks deaf decreasingClause)
        (v1 v2 v3 =>
          deaf.header
            ({
              exportKeyword,
              opaqueKeyword,
              kind,
              keyword,
              name,
              forallKeyword,
              params = v1,
              colon,
              result = v2,
              decreasingClause = v3,
              unfoldingClause
            }))

theorem defBodyBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: DefBody):
    runDefBody on ((walkDefBody blankPure input).blank)
      = (runDefBody on input).map (x => (walkDefBody blankPure x).blank) :=
  match input with
    | Primitive => byComputing
    | Assigned colonEq value => Fail.toResultAlike1 (exprBlanks on deaf value) (v1 => byComputing)
    | Arms arms => Fail.toResultAlike1 (armsBlanks on deaf arms) (v1 => byComputing)

theorem groupsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Group):
    runGroups on (blankGroups (walkGroups blankPure input))
      = (runGroups on input).map (x => blankGroups (walkGroups blankPure x)) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => Fail.toResultAlike2 (groupBlanks deaf first) (groupsBlanks on deaf rest) (v1 v2 => byComputing)

theorem indicesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List (Index, Word)):
    runIndices on (blankIndexSteps (walkIndices blankPure input))
      = (runIndices on input).map (x => blankIndexSteps (walkIndices blankPure x)) :=
  match input with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] =>
      Fail.toResultAlike2 (groupBlanks deaf binder) (indicesBlanks on deaf rest) (v1 v2 => byComputing)
    | [(IndexType annotation, arrow), ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf annotation) (indicesBlanks on deaf rest) (v1 v2 => byComputing)

theorem fieldsBlanks ∀ [on: Steps]
    (deaf: Blanks on) (input: Fields):
    runFields on (input.walk blankPure) = (runFields on input).map (x => x.walk blankPure) :=
  match input with
    | { open, fields, trailingComma, close } =>
      Fail.toResultAlike1Let
        [g2 := v1 => { open = Comments.none, fields = v1, trailingComma, close = Comments.none }]
        (fieldListBlanks on deaf fields)
        (v1 => deaf.fields ({ open, fields = v1, trailingComma, close }))

theorem fieldListBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Field):
    runFieldList on (blankFieldList (walkFieldList blankPure input))
      = (runFieldList on input).map (x => blankFieldList (walkFieldList blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] =>
      Fail.toResultAlike4
        (attributesBlanks on deaf attributes)
        (exprBlanks on deaf annotation)
        (afterBlanks deaf default)
        (fieldListBlanks on deaf rest)
        (v1 v2 v3 v4 => byComputing)

theorem constructorsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Constructor):
    runConstructors on (blankConstructors (walkConstructors blankPure input))
      = (runConstructors on input).map (x => blankConstructors (walkConstructors blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] =>
      Fail.toResultAlike4
        (attributesBlanks on deaf attributes)
        (partsBlanks on deaf fields)
        (afterBlanks deaf result)
        (constructorsBlanks on deaf rest)
        (v1 v2 v3 v4 => byComputing)

theorem partsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List ConstructorPart):
    runParts on (blankParts (walkParts blankPure input))
      = (runParts on input).map (x => blankParts (walkParts blankPure x)) :=
  match input with
    | [] => byComputing
    | [PartGroup group, ..rest] =>
      Fail.toResultAlike2 (groupBlanks deaf group) (partsBlanks on deaf rest) (v1 v2 => byComputing)
    | [PartFields fields, ..rest] =>
      Fail.toResultAlike2 (fieldsBlanks deaf fields) (partsBlanks on deaf rest) (v1 v2 => byComputing)

theorem operationsBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Operation):
    runOperations on (blankOperations (walkOperations blankPure input))
      = (runOperations on input).map (x => blankOperations (walkOperations blankPure x)) :=
  match input with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] =>
      Fail.toResultAlike2 (exprBlanks on deaf annotation) (operationsBlanks on deaf rest) (v1 v2 => byComputing)

theorem attributesBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: List Attributes):
    runAttributes on (walkAttributes blankPure input)
      = (runAttributes on input).map (x => walkAttributes blankPure x) :=
  match input with
    | [] => byComputing
    | [first, ..rest] =>
      Fail.toResultAlike2 (deaf.attributes first) (attributesBlanks on deaf rest) (v1 v2 => byComputing)

theorem optionalBlanks ∀ [on: Steps]
    (deaf: Blanks on) (input: Option Expr):
    runOptional on (walkOptional blankPure input) = (runOptional on input).map (x => walkOptional blankPure x) :=
  match input with
    | Some value => Fail.toResultAlike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

theorem afterBlanks ∀ [on: Steps]
    (deaf: Blanks on) (input: Option (Comments, Expr)):
    runAfter on (blankAfter (walkAfter blankPure input))
      = (runAfter on input).map (x => blankAfter (walkAfter blankPure x)) :=
  match input with
    | Some (word, value) => Fail.toResultAlike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

theorem afterWordBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Word, Expr)):
    runAfter on (blankAfterWord (walkAfter blankPure input))
      = (runAfter on input).map (x => blankAfterWord (walkAfter blankPure x)) :=
  match input with
    | Some (word, value) => Fail.toResultAlike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

theorem guardBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option Guard):
    runGuard on ((walkGuard blankPure input).map Guard.blank)
      = (runGuard on input).map (x => (walkGuard blankPure x).map Guard.blank) :=
  match input with
    | Some { keyword, binder, condition } => Fail.toResultAlike1 (exprBlanks on deaf condition) (v1 => byComputing)
    | None => byComputing

theorem tailBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Word, Pattern)):
    runTail on (blankAfterWord (walkTail blankPure input))
      = (runTail on input).map (x => blankAfterWord (walkTail blankPure x)) :=
  match input with
    | Some (dots, rest) => Fail.toResultAlike1 (patternBlanks on deaf rest) (v1 => byComputing)
    | None => byComputing

theorem beforeBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Option (Expr, Word)):
    runBefore on (blankBase (walkBefore blankPure input))
      = (runBefore on input).map (x => blankBase (walkBefore blankPure x)) :=
  match input with
    | Some (value, word) => Fail.toResultAlike1 (exprBlanks on deaf value) (v1 => byComputing)
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
