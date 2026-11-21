--| The traversal with steps that can fail, against blanking (SW-4162): traversing a tree with its comments blanked
--| (`walk blankPure`) fails with the same message as traversing the tree, or finishes with the result blanked, when
--| each step does so on a node and its blanked form (`Blanks`). One theorem a traversal function, `…Blanks`, stated
--| on the form the function's input takes inside a blanked tree (`blankArms (walkArms blankPure arms)` for a match's
--| arms). `Fmt.Walk`'s `…Ok` family covers steps that can't fail; the lowering's checks can, so `loweringDeaf`
--| (`Syntax.DeafProofs`) rests on this family. The arms were generated from the `…Ok` family's, one `alikeN` call
--| for each `seqN`; a change to the traversal needs the same change here.
namespace Fmt.TraverseFail
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
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

-- The shapes of `Fmt.Walk`'s `seqN`, `seqNk` and `seqNj`, for two runs: one on a node's children and one on their
-- blanked forms. Each child's run on the blanked form fails as the original's does or finishes with the original's
-- result blanked (`hN`); then the arm does too, given that the rest of the arm does for every result (`step`).

--| Traversing a blanked tree is blanking the traversed tree, failures included. By induction alongside the
--| traversal: in each arm the children's runs on their blanked forms agree with theirs (the induction hypotheses),
--| so the arm's binds do (`alikeN`, `alikeNk`, `alikeNj`), and then the step does by `Blanks`.
theorem exprBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Expr):
    runExpr on (input.walk blankPure) = (runExpr on input).map (x => x.walk blankPure) :=
  match input with
    | Atom _ _ | Unit _ _ | Universe _ _ | Include _ _ => deaf.expr input
    | Paren open inner close =>
      Fail.toResultAlike1Then (exprBlanks on deaf inner) (v1 => deaf.expr (Paren open v1 close))
    | Tuple open items trailingComma close =>
      Fail.toResultAlike1Then (exprsBlanks on deaf items) (v1 => deaf.expr (Tuple open v1 trailingComma close))
    | ListOf open items trailingComma close =>
      Fail.toResultAlike1Then (exprsBlanks on deaf items) (v1 => deaf.expr (ListOf open v1 trailingComma close))
    | Spread dots list => Fail.toResultAlike1Then (exprBlanks on deaf list) (v1 => deaf.expr (Spread dots v1))
    | Record open base fields trailingComma close =>
      Fail.toResultAlike2Then (beforeBlanks on deaf base) (exprsBlanks on deaf fields) (v1 v2 =>
        deaf.expr (Record open v1 v2 trailingComma close))
    | RecordField name equals value =>
      Fail.toResultAlike1Then (exprBlanks on deaf value) (v1 => deaf.expr (RecordField name equals v1))
    | CtorFields ctor record => Fail.toResultAlike2Then (exprBlanks on deaf ctor) (exprBlanks on deaf record) (v1 v2 =>
      deaf.expr (CtorFields v1 v2))
    | App head arguments =>
      Fail.toResultAlike2Then (exprBlanks on deaf head) (exprsBlanks on deaf arguments) (v1 v2 => deaf.expr (App v1 v2))
    | NamedArg open name colonEq value close =>
      Fail.toResultAlike1Then (exprBlanks on deaf value) (v1 => deaf.expr (NamedArg open name colonEq v1 close))
    | FieldAccess target dot field =>
      Fail.toResultAlike1Then (optionalBlanks deaf target) (v1 => deaf.expr (FieldAccess v1 dot field))
    | Section body => Fail.toResultAlike1Then (exprBlanks on deaf body) (v1 => deaf.expr (Section v1))
    | OperatorSection open left operator right close =>
      Fail.toResultAlike2Then (optionalBlanks deaf left) (optionalBlanks deaf right) (v1 v2 =>
        deaf.expr (OperatorSection open v1 operator v2 close))
    | Infix kind left operator right =>
      Fail.toResultAlike2Then (exprBlanks on deaf left) (exprBlanks on deaf right) (v1 v2 =>
        deaf.expr (Infix kind v1 operator v2))
    | Chain first rest =>
      Fail.toResultAlike2Then (exprBlanks on deaf first) (linksBlanks on deaf rest) (v1 v2 => deaf.expr (Chain v1 v2))
    | Prefix operator operand =>
      Fail.toResultAlike1Then (exprBlanks on deaf operand) (v1 => deaf.expr (Prefix operator v1))
    | Binding kind keyword params arrow body =>
      Fail.toResultAlike2Then (paramsBlanks on deaf params) (exprBlanks on deaf body) (v1 v2 =>
        deaf.expr (Binding kind keyword v1 arrow v2))
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      Fail.toResultAlike3Then
        (exprBlanks on deaf condition)
        (exprBlanks on deaf whenTrue)
        (exprBlanks on deaf whenFalse)
        (v1 v2 v3 => deaf.expr (If keyword binder v1 thenKeyword v2 elseKeyword v3))
    | Annotation open value colon annotation close =>
      Fail.toResultAlike2Then (exprBlanks on deaf value) (exprBlanks on deaf annotation) (v1 v2 =>
        deaf.expr (Annotation open v1 colon v2 close))
    | Interpolated pieces => Fail.toResultAlike1Then (piecesBlanks on deaf pieces) (v1 => deaf.expr (Interpolated v1))
    | Match keyword scrutinees withKeyword arms =>
      Fail.toResultAlike2Then (scrutineesBlanks on deaf scrutinees) (armsBlanks on deaf arms) (v1 v2 =>
        deaf.expr (Match keyword v1 withKeyword v2))
    | ClauseLambda keyword word arms =>
      Fail.toResultAlike1Then (armsBlanks on deaf arms) (v1 => deaf.expr (ClauseLambda keyword word v1))
    | Facts kind keyword facts =>
      Fail.toResultAlike1Then (exprBlanks on deaf facts) (v1 => deaf.expr (Facts kind keyword v1))
    | FunctionType binder arrow result =>
      Fail.toResultAlike2Then (groupBlanks deaf binder) (exprBlanks on deaf result) (v1 v2 =>
        deaf.expr (FunctionType v1 arrow v2))
    | Effect row result =>
      Fail.toResultAlike2Then (rowBlanks on deaf row) (exprBlanks on deaf result) (v1 v2 => deaf.expr (Effect v1 v2))
    | Block first rest result =>
      Fail.toResultAlike3Then
        (statementBlanks on deaf first)
        (statementsBlanks on deaf rest)
        (exprBlanks on deaf result)
        (v1 v2 v3 => deaf.expr (Block v1 v2 v3))
    | LetIn binding semicolon body =>
      Fail.toResultAlike2Then (letBlanks on deaf binding) (exprBlanks on deaf body) (v1 v2 =>
        deaf.expr (LetIn v1 semicolon v2))
    | Handle keyword computation withKeyword clauses =>
      Fail.toResultAlike2Then (exprBlanks on deaf computation) (clausesBlanks on deaf clauses) (v1 v2 =>
        deaf.expr (Handle keyword v1 withKeyword v2))
    | Reify keyword reifyWord computation withKeyword clauses =>
      Fail.toResultAlike2Then (exprBlanks on deaf computation) (clausesBlanks on deaf clauses) (v1 v2 =>
        deaf.expr (Reify keyword reifyWord v1 withKeyword v2))
    | Induct keyword inductWord call withKeyword arms =>
      Fail.toResultAlike2Then (exprBlanks on deaf call) (inductArmsBlanks on deaf arms) (v1 v2 =>
        deaf.expr (Induct keyword inductWord v1 withKeyword v2))
    | Calc keyword first steps =>
      Fail.toResultAlike2Then (exprBlanks on deaf first) (calcStepsBlanks on deaf steps) (v1 v2 =>
        deaf.expr (Calc keyword v1 v2))
    | Rewrite keyword rules target body =>
      Fail.toResultAlike3Then (rulesBlanks on deaf rules) (afterBlanks deaf target) (afterBlanks deaf body) (v1 v2 v3 =>
        deaf.expr (Rewrite keyword v1 v2 v3))
    | Cases keyword targets body =>
      Fail.toResultAlike1Then (afterBlanks deaf body) (v1 => deaf.expr (Cases keyword targets v1))
    | Walk keyword items body => Fail.toResultAlike2Then (exprBlanks on deaf items) (afterBlanks deaf body) (v1 v2 =>
      deaf.expr (Walk keyword v1 v2))

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
    | PatternWord kind word => deaf.pattern (PatternWord kind word)
    | PatternCtor name arguments =>
      Fail.toResultAlike1Then (patternsBlanks on deaf arguments) (v1 => deaf.pattern (PatternCtor name v1))
    | PatternCtorFields name fields =>
      Fail.toResultAlike1Then (fieldsPatternBlanks on deaf fields) (v1 => deaf.pattern (PatternCtorFields name v1))
    | PatternRecord fields =>
      Fail.toResultAlike1Then (fieldsPatternBlanks on deaf fields) (v1 => deaf.pattern (PatternRecord v1))
    | PatternTuple open items trailingComma close => Fail.toResultAlike1Then (patternsBlanks on deaf items) (v1 =>
      deaf.pattern (PatternTuple open v1 trailingComma close))
    | PatternList open items trailingComma tail close =>
      Fail.toResultAlike2Then (patternsBlanks on deaf items) (tailBlanks on deaf tail) (v1 v2 =>
        deaf.pattern (PatternList open v1 trailingComma v2 close))
    | PatternNamed open name colonEq value close => Fail.toResultAlike1Then (patternBlanks on deaf value) (v1 =>
      deaf.pattern (PatternNamed open name colonEq v1 close))
    | PatternOr first rest =>
      Fail.toResultAlike2Then (patternBlanks on deaf first) (patternLinksBlanks on deaf rest) (v1 v2 =>
        deaf.pattern (PatternOr v1 v2))
    | PatternParen open inner close =>
      Fail.toResultAlike1Then (patternBlanks on deaf inner) (v1 => deaf.pattern (PatternParen open v1 close))
    | PatternNegative minus number => deaf.pattern (PatternNegative minus number)
    | PatternAbsurd open close => deaf.pattern (PatternAbsurd open close)
    | PatternAppend start operator rest =>
      Fail.toResultAlike2Then (patternBlanks on deaf start) (patternBlanks on deaf rest) (v1 v2 =>
        deaf.pattern (PatternAppend v1 operator v2))

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

theorem declBlanks ∀ (on: Steps)
    (deaf: Blanks on) (input: Decl):
    runDecl on (input.walk blankPure) = (runDecl on input).map (x => x.walk blankPure) :=
  match input with
    | Namespace keyword name => deaf.decl (Namespace keyword name)
    | Import keyword path open imported close => deaf.decl (Import keyword path open imported close)
    | Definition attributes header body =>
      Fail.toResultAlike3Then
        (attributesBlanks on deaf attributes)
        (headerBlanks on deaf header)
        (defBodyBlanks on deaf body)
        (v1 v2 v3 => deaf.decl (Definition v1 v2 v3))
    | Data attributes isInterface keyword name params indices body =>
      match indices with
        | Some { colon, steps, last } =>
          match body with
            | Abstract =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlike2 (indicesBlanks on deaf steps) (exprBlanks on deaf last) (w1 w2 => byComputing))
                (Fail.toResultAlikePure byComputing)
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Synonym equals annotation =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlike2 (indicesBlanks on deaf steps) (exprBlanks on deaf last) (w1 w2 => byComputing))
                (Fail.toResultAlike1 [g2 := w1 => Synonym Comments.none w1] (exprBlanks on deaf annotation) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | RecordBody equals fields =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlike2 (indicesBlanks on deaf steps) (exprBlanks on deaf last) (w1 w2 => byComputing))
                (Fail.toResultAlike1 [g2 := w1 => RecordBody Comments.none w1] (fieldsBlanks deaf fields) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Sum equals constructors =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlike2 (indicesBlanks on deaf steps) (exprBlanks on deaf last) (w1 w2 => byComputing))
                (Fail.toResultAlike1 [g2 := w1 => Sum Comments.none w1] (constructorsBlanks on deaf constructors) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
        | None =>
          match body with
            | Abstract =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlikePure byComputing)
                (Fail.toResultAlikePure byComputing)
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Synonym equals annotation =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlikePure byComputing)
                (Fail.toResultAlike1 [g2 := w1 => Synonym Comments.none w1] (exprBlanks on deaf annotation) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | RecordBody equals fields =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlikePure byComputing)
                (Fail.toResultAlike1 [g2 := w1 => RecordBody Comments.none w1] (fieldsBlanks deaf fields) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
            | Sum equals constructors =>
              Fail.toResultAlike4Then
                [g2 := v1 v2 v3 v4 => Data v1 isInterface Comments.none name.blank v2 v3 v4]
                (attributesBlanks on deaf attributes)
                (groupsBlanks on deaf params)
                (Fail.toResultAlikePure byComputing)
                (Fail.toResultAlike1 [g2 := w1 => Sum Comments.none w1] (constructorsBlanks on deaf constructors) (w1 =>
                  byComputing))
                (v1 v2 v3 v4 => deaf.decl (Data v1 isInterface keyword name v2 v3 v4))
    | Ability keyword name params whereKeyword operations =>
      Fail.toResultAlike2Then (groupsBlanks on deaf params) (operationsBlanks on deaf operations) (v1 v2 =>
        deaf.decl (Ability keyword name v1 whereKeyword v2))
    | Test keyword name colonEq body =>
      Fail.toResultAlike1Then (exprBlanks on deaf body) (v1 => deaf.decl (Test keyword name colonEq v1))
    | RuleSetDecl keyword name colonEq set =>
      Fail.toResultAlike1Then (ruleSetBlanks on deaf set) (v1 => deaf.decl (RuleSetDecl keyword name colonEq v1))

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
