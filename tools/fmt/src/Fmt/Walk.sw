--| The traversal lemma (SW-3877). `walk` is a pure copy of the traversal
--| (`Syntax/Traverse.sw`), arm for arm, with steps that can't fail
--| (`Pure`). Two families of facts, one theorem per traversal function:
--|
--| - `…Ok`: with steps that finish as a `Pure`'s do (`Agrees`), the
--|   traversal finishes with the walk's result;
--| - `…Twice`: walking with `s` and then `m` is walking with `m`, when each
--|   of `s`'s steps keeps what walking with `m` gives of the whole node it
--|   rewrites (`Keeps`, the strong form: the step may rebuild the node's
--|   descendants).
--|
--| Together, `applyKeeps`: such a pass keeps what applying `m`'s steps
--| gives a file. A change to the traversal needs the same change here; the
--| `…Ok` theorems fail until it is made. The proofs were generated, one
--| `seqN` call or `rewrite` an arm.
namespace Fmt.Walk
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)

--| `Steps` that can't fail.
type Pure = {
  expr: Expr → Expr,
  pattern: Pattern → Pattern,
  header: Header → Header,
  decl: Decl → Decl,
  fields: Fields → Fields,
  attributes: Attributes → Attributes,
  ruleSet: RuleSet → RuleSet
}

def Expr.walk (expr: Expr) (on: Pure): Expr :=
  let rebuilt := match expr with
    | Atom kind word => Atom kind word
    | Paren open inner close => Paren open (inner.walk on) close
    | Unit open close => Unit open close
    | Universe keyword level => Universe keyword level
    | Include keyword path => Include keyword path
    | Tuple open items trailingComma close => Tuple open (walkExprs on items) trailingComma close
    | ListOf open items trailingComma close => ListOf open (walkExprs on items) trailingComma close
    | Spread dots list => Spread dots (list.walk on)
    | Record open base fields trailingComma close =>
      let based := walkBefore on base
      Record open based (walkExprs on fields) trailingComma close
    | RecordField name equals value => RecordField name equals (value.walk on)
    | CtorFields ctor record =>
      let ctor' := ctor.walk on
      CtorFields ctor' (record.walk on)
    | App head arguments =>
      let head' := head.walk on
      App head' (walkExprs on arguments)
    | NamedArg open name colonEq value close => NamedArg open name colonEq (value.walk on) close
    | FieldAccess target dot field =>
      let target' := walkOptional on target
      FieldAccess target' dot field
    | Section body => Section (body.walk on)
    | OperatorSection open left operator right close =>
      let left' := walkOptional on left
      let right' := walkOptional on right
      OperatorSection open left' operator right' close
    | Infix kind left operator right =>
      let left' := left.walk on
      Infix kind left' operator (right.walk on)
    | Chain first rest =>
      let first' := first.walk on
      Chain first' (walkLinks on rest)
    | Prefix operator operand => Prefix operator (operand.walk on)
    | Binding kind keyword params arrow body =>
      let params' := walkParams on params
      Binding kind keyword params' arrow (body.walk on)
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      let condition' := condition.walk on
      let whenTrue' := whenTrue.walk on
      If keyword binder condition' thenKeyword whenTrue' elseKeyword (whenFalse.walk on)
    | Annotation open value colon annotation close =>
      let value' := value.walk on
      Annotation open value' colon (annotation.walk on) close
    | Interpolated pieces => Interpolated (walkPieces on pieces)
    | Match keyword scrutinees withKeyword arms =>
      let scrutinees' := walkScrutinees on scrutinees
      Match keyword scrutinees' withKeyword (walkArms on arms)
    | ClauseLambda keyword word arms => ClauseLambda keyword word (walkArms on arms)
    | Facts kind keyword facts => Facts kind keyword (facts.walk on)
    | FunctionType binder arrow result =>
      let binder' := binder.walk on
      FunctionType binder' arrow (result.walk on)
    | Effect row result =>
      let row' := walkRow on row
      Effect row' (result.walk on)
    | Block first rest result =>
      let first' := walkStatement on first
      let rest' := walkStatements on rest
      Block first' rest' (result.walk on)
    | LetIn binding semicolon body =>
      let binding' := walkLet on binding
      LetIn binding' semicolon (body.walk on)
    | Handle keyword computation withKeyword clauses =>
      let computation' := computation.walk on
      Handle keyword computation' withKeyword (walkClauses on clauses)
    | Reify keyword reify computation withKeyword clauses =>
      let computation' := computation.walk on
      Reify keyword reify computation' withKeyword (walkClauses on clauses)
    | Induct keyword induct call withKeyword arms =>
      let call' := call.walk on
      Induct keyword induct call' withKeyword (walkInductArms on arms)
    | Calc keyword first steps =>
      let first' := first.walk on
      Calc keyword first' (walkSteps on steps)
    | Rewrite keyword rules target body =>
      let rules' := walkRules on rules
      let target' := walkAfter on target
      Rewrite keyword rules' target' (walkAfter on body)
    | Cases keyword targets body => Cases keyword targets (walkAfter on body)
    | Walk keyword items body =>
      let items' := items.walk on
      Walk keyword items' (walkAfter on body)
  on.expr rebuilt

def walkStatements (on: Pure) (input: List Statement): List Statement := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := walkStatement on first
    [first', ..walkStatements on rest]

def walkStatement (on: Pure) (input: Statement): Statement := match input with
  | LetStatement binding => LetStatement (walkLet on binding)
  | LocalDef attributes header body =>
    let attributes' := walkAttributes on attributes
    let header' := walkHeader on header
    LocalDef attributes' header' (walkDefBody on body)
  | ExprStatement value => ExprStatement (value.walk on)

def walkLet (on: Pure) (input: Let): Let := match input with
  | { keyword, pattern, annotation, colonEq, value } =>
    let pattern' := pattern.walk on
    let annotation' := walkAfter on annotation
    let value' := value.walk on
    { keyword, pattern = pattern', annotation = annotation', colonEq, value = value' }

def walkClauses (on: Pure) (input: List HandlerClause): List HandlerClause := match input with
  | [] => []
  | [ReturnClause bar keyword name arrow body, ..rest] =>
    let body' := body.walk on
    [ReturnClause bar keyword name arrow body', ..walkClauses on rest]
  | [OperationClause bar operation argument comma continuation arrow body, ..rest] =>
    let argument' := argument.walk on
    let body' := body.walk on
    [OperationClause bar operation argument' comma continuation arrow body', ..walkClauses on rest]

def walkInductArms (on: Pure) (input: List InductArm): List InductArm := match input with
  | [] => []
  | [{ bar, case, names, arrow, body }, ..rest] =>
    let body' := body.walk on
    [{ bar, case, names, arrow, body = body' }, ..walkInductArms on rest]

def walkSteps (on: Pure) (input: List CalcStep): List CalcStep := match input with
  | [] => []
  | [{ underscore, relation, operand, proof }, ..rest] =>
    let operand' := operand.walk on
    let proof' := walkAfter on proof
    [{ underscore, relation, operand = operand', proof = proof' }, ..walkSteps on rest]

def walkRules (on: Pure) (input: Rules): Rules := match input with
  | RuleList rules => RuleList (walkRuleList on rules)
  | Repeatedly word set => Repeatedly word (walkRuleSet on set)

def walkRuleSet (on: Pure) (input: RuleSet): RuleSet := match input with
  | { open, rules, trailingComma, close } =>
    let rules' := walkRuleList on rules
    on.ruleSet { open, rules = rules', trailingComma, close }

def walkRuleList (on: Pure) (input: List RewriteRule): List RewriteRule := match input with
  | [] => []
  | [{ reverse, rule }, ..rest] =>
    let rule' := rule.walk on
    [{ reverse, rule = rule' }, ..walkRuleList on rest]

def walkRow (on: Pure) (input: Row): Row := match input with
  | { open, abilities, variable, close } =>
    let abilities': List Expr := walkExprs on abilities
    { open, abilities = abilities', variable, close }

def walkExprs (on: Pure) (input: List Expr): List Expr := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := first.walk on
    [first', ..walkExprs on rest]

def walkLinks (on: Pure) (input: List (Word, Expr)): List (Word, Expr) := match input with
  | [] => []
  | [(operator, operand), ..rest] =>
    let operand' := operand.walk on
    [(operator, operand'), ..walkLinks on rest]

def walkPieces (on: Pure) (input: List Piece): List Piece := match input with
  | [] => []
  | [TextPiece word, ..rest] => [TextPiece word, ..walkPieces on rest]
  | [Interpolation open value close, ..rest] =>
    let value' := value.walk on
    [Interpolation open value' close, ..walkPieces on rest]

def walkScrutinees (on: Pure) (input: List Scrutinee): List Scrutinee := match input with
  | [] => []
  | [{ name, value }, ..rest] =>
    let value' := value.walk on
    [{ name, value = value' }, ..walkScrutinees on rest]

def walkArms (on: Pure) (input: List Arm): List Arm := match input with
  | [] => []
  | [{ bar, patterns, guard, body }, ..rest] =>
    let patterns' := walkPatterns on patterns
    let guard' := walkGuard on guard
    let body' := walkAfter on body
    [{ bar, patterns = patterns', guard = guard', body = body' }, ..walkArms on rest]

def walkParams (on: Pure) (input: List Param): List Param := match input with
  | [] => []
  | [NameParam word, ..rest] => [NameParam word, ..walkParams on rest]
  | [PatternParam pattern, ..rest] =>
    let pattern' := pattern.walk on
    [PatternParam pattern', ..walkParams on rest]
  | [Grouped group, ..rest] =>
    let group' := group.walk on
    [Grouped group', ..walkParams on rest]
  | [TypedPattern open pattern colon annotation close, ..rest] =>
    let pattern' := pattern.walk on
    let annotation' := annotation.walk on
    [TypedPattern open pattern' colon annotation' close, ..walkParams on rest]

def Group.walk (group: Group) (on: Pure): Group := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
    let attributes' := walkAttributes on attributes
    let annotation' := walkOptional on annotation
    let default' := walkAfter on default
    {
      kind,
      implicit,
      open,
      attributes = attributes',
      auto,
      names,
      colon,
      annotation = annotation',
      default = default',
      close,
      bare
    }

def Pattern.walk (pattern: Pattern) (on: Pure): Pattern :=
  let rebuilt := match pattern with
    | PatternWord kind word => PatternWord kind word
    | PatternCtor name arguments => PatternCtor name (walkPatterns on arguments)
    | PatternCtorFields name fields => PatternCtorFields name (walkFields on fields)
    | PatternRecord fields => PatternRecord (walkFields on fields)
    | PatternTuple open items trailingComma close => PatternTuple open (walkPatterns on items) trailingComma close
    | PatternList open items trailingComma tail close =>
      let items' := walkPatterns on items
      let tail' := walkTail on tail
      PatternList open items' trailingComma tail' close
    | PatternNamed open name colonEq value close => PatternNamed open name colonEq (value.walk on) close
    | PatternOr first rest =>
      let first' := first.walk on
      PatternOr first' (walkPatternLinks on rest)
    | PatternParen open inner close => PatternParen open (inner.walk on) close
    | PatternNegative minus number => PatternNegative minus number
    | PatternAbsurd open close => PatternAbsurd open close
    | PatternAppend start operator rest =>
      let start' := start.walk on
      PatternAppend start' operator (rest.walk on)
  on.pattern rebuilt

def walkPatterns (on: Pure) (input: List Pattern): List Pattern := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := first.walk on
    [first', ..walkPatterns on rest]

def walkPatternLinks (on: Pure) (input: List (Word, Pattern)): List (Word, Pattern) := match input with
  | [] => []
  | [(bar, alternative), ..rest] =>
    let alternative' := alternative.walk on
    [(bar, alternative'), ..walkPatternLinks on rest]

def walkFields (on: Pure) (input: FieldsPattern): FieldsPattern := match input with
  | { open, fields, trailingComma, rest, close } =>
    let fields' := walkFieldPatterns on fields
    { open, fields = fields', trailingComma, rest, close }

def walkFieldPatterns (on: Pure) (input: List FieldPattern): List FieldPattern := match input with
  | [] => []
  | [{ name, value = Some (equals, pattern) }, ..rest] =>
    let pattern' := pattern.walk on
    [{ name, value = Some (equals, pattern') }, ..walkFieldPatterns on rest]
  | [{ name, value = None }, ..rest] => [{ name, value = None }, ..walkFieldPatterns on rest]

--| A declaration with every expression and pattern in it traversed.
def Decl.walk (decl: Decl) (on: Pure): Decl :=
  let ex := (expr: Expr) => expr.walk on
  let groups := (list: List Group) => walkGroups on list
  let rebuilt := match decl with
    | Namespace keyword name => Namespace keyword name
    | Import keyword path open imported close => Import keyword path open imported close
    | Definition attributes header body =>
      let attributes' := walkAttributes on attributes
      let header' := walkHeader on header
      Definition attributes' header' (walkDefBody on body)
    | Data attributes isInterface keyword name params indices body =>
      let attributes' := walkAttributes on attributes
      let params' := groups params
      let indices' := match indices with
        | Some { colon, steps, last } =>
          let steps' := walkIndices on steps
          Some { colon, steps = steps', last = ex last }
        | None => None
      let body' := match body with
        | Abstract => Abstract
        | Synonym equals annotation => Synonym equals (ex annotation)
        | RecordBody equals fields => RecordBody equals (fields.walk on)
        | Sum equals constructors => Sum equals (walkConstructors on constructors)
      Data attributes' isInterface keyword name params' indices' body'
    | Ability keyword name params whereKeyword operations =>
      let params' := groups params
      Ability keyword name params' whereKeyword (walkOperations on operations)
    | Test keyword name colonEq body => Test keyword name colonEq (ex body)
    | RuleSetDecl keyword name colonEq set => RuleSetDecl keyword name colonEq (walkRuleSet on set)
  on.decl rebuilt

def walkHeader (on: Pure) (input: Header): Header := match input with
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
    let params' := walkGroups on params
    let result' := result.walk on
    let decreasing' := walkAfter on decreasingClause
    on.header {
      exportKeyword,
      opaqueKeyword,
      kind,
      keyword,
      name,
      forallKeyword,
      params = params',
      colon,
      result = result',
      decreasingClause = decreasing',
      unfoldingClause
    }

def walkDefBody (on: Pure) (input: DefBody): DefBody := match input with
  | Primitive => Primitive
  | Assigned colonEq value =>
    let value' := value.walk on
    Assigned colonEq value'
  | Arms arms => Arms (walkArms on arms)

def walkGroups (on: Pure) (input: List Group): List Group := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := first.walk on
    [first', ..walkGroups on rest]

def walkIndices (on: Pure) (input: List (Index, Word)): List (Index, Word) := match input with
  | [] => []
  | [(IndexBinder binder, arrow), ..rest] =>
    let binder' := binder.walk on
    [(IndexBinder binder', arrow), ..walkIndices on rest]
  | [(IndexType annotation, arrow), ..rest] =>
    let annotation' := annotation.walk on
    [(IndexType annotation', arrow), ..walkIndices on rest]

def Fields.walk (fields: Fields) (on: Pure): Fields := match fields with
  | { open, fields, trailingComma, close } =>
    let fields' := walkFieldList on fields
    on.fields { open, fields = fields', trailingComma, close }

def walkFieldList (on: Pure) (input: List Field): List Field := match input with
  | [] => []
  | [{ attributes, name, colon, annotation, default }, ..rest] =>
    let attributes' := walkAttributes on attributes
    let annotation' := annotation.walk on
    let default' := walkAfter on default
    [{ attributes = attributes', name, colon, annotation = annotation', default = default' }, ..walkFieldList on rest]

def walkConstructors (on: Pure) (input: List Constructor): List Constructor := match input with
  | [] => []
  | [{ bar, attributes, name, fields, result }, ..rest] =>
    let attributes' := walkAttributes on attributes
    let fields' := walkParts on fields
    let result' := walkAfter on result
    [{ bar, attributes = attributes', name, fields = fields', result = result' }, ..walkConstructors on rest]

def walkParts (on: Pure) (input: List ConstructorPart): List ConstructorPart := match input with
  | [] => []
  | [PartGroup group, ..rest] =>
    let group' := group.walk on
    [PartGroup group', ..walkParts on rest]
  | [PartFields fields, ..rest] =>
    let fields' := fields.walk on
    [PartFields fields', ..walkParts on rest]

def walkOperations (on: Pure) (input: List Operation): List Operation := match input with
  | [] => []
  | [{ name, colon, annotation }, ..rest] =>
    let annotation' := annotation.walk on
    [{ name, colon, annotation = annotation' }, ..walkOperations on rest]

def walkAttributes (on: Pure) (input: List Attributes): List Attributes := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := on.attributes first
    [first', ..walkAttributes on rest]

def walkOptional (on: Pure) (input: Option Expr): Option Expr := match input with
  | Some value =>
    let value' := value.walk on
    Some value'
  | None => None

--| A part after a token: a default after `:=`, a body after `=>`.
def walkAfter (on: Pure) (input: Option (k, Expr)): Option (k, Expr) := match input with
  | Some (word, value) =>
    let value' := value.walk on
    Some (word, value')
  | None => None

def walkGuard (on: Pure) (input: Option Guard): Option Guard := match input with
  | Some { keyword, binder, condition } =>
    let condition' := condition.walk on
    Some { keyword, binder, condition = condition' }
  | None => None

def walkTail (on: Pure) (input: Option (Word, Pattern)): Option (Word, Pattern) := match input with
  | Some (dots, rest) =>
    let rest' := rest.walk on
    Some (dots, rest')
  | None => None

--| A record update's base, before its `|`.
def walkBefore (on: Pure) (input: Option (Expr, k)): Option (Expr, k) := match input with
  | Some (value, word) =>
    let value' := value.walk on
    Some (value', word)
  | None => None

-- The pure copy stands in for the traversal.

--| Each of `on`'s steps finishes, with what `p`'s gives.
type Agrees (on: Steps) (p: Pure) = {
  expr: ∀ (z: Expr) => Fail.toResult (() => on.expr z) = Ok (p.expr z),
  pattern: ∀ (z: Pattern) => Fail.toResult (() => on.pattern z) = Ok (p.pattern z),
  header: ∀ (z: Header) => Fail.toResult (() => on.header z) = Ok (p.header z),
  decl: ∀ (z: Decl) => Fail.toResult (() => on.decl z) = Ok (p.decl z),
  fields: ∀ (z: Fields) => Fail.toResult (() => on.fields z) = Ok (p.fields z),
  attributes: ∀ (z: Attributes) => Fail.toResult (() => on.attributes z) = Ok (p.attributes z),
  ruleSet: ∀ (z: RuleSet) => Fail.toResult (() => on.ruleSet z) = Ok (p.ruleSet z)
}

--| Each of `s`'s steps keeps what walking with `m` gives of the node it
--| rewrites: the strong form, where `s` may rebuild the node's descendants
--| too, since the whole node is walked with `m` again.
type Keeps (s m: Pure) = {
  expr: ∀ (z: Expr) => (s.expr z).walk m = z.walk m,
  pattern: ∀ (z: Pattern) => (s.pattern z).walk m = z.walk m,
  header: ∀ (z: Header) => walkHeader m (s.header z) = walkHeader m z,
  decl: ∀ (z: Decl) => (s.decl z).walk m = z.walk m,
  fields: ∀ (z: Fields) => (s.fields z).walk m = z.walk m,
  attributes: ∀ (z: Attributes) => m.attributes (s.attributes z) = m.attributes z,
  ruleSet: ∀ (z: RuleSet) => walkRuleSet m (s.ruleSet z) = walkRuleSet m z
}

-- Running finished computations in order, with a pure function of their
-- results and then a step: the shapes the traversal's arms elaborate to
-- (`seqNk` for a node built and then given to a step, `seqNj` for a step
-- applied in the arm's own `let`s).

def runExpr (on: Steps) (input: Expr): Result (Expr) Text := Fail.toResult (() => input.traverse on)

def runStatements (on: Steps) (input: List Statement): Result (List Statement) Text :=
  Fail.toResult (() => traverseStatements on input)

def runStatement (on: Steps) (input: Statement): Result (Statement) Text :=
  Fail.toResult (() => traverseStatement on input)

def runLet (on: Steps) (input: Let): Result (Let) Text := Fail.toResult (() => traverseLet on input)

def runClauses (on: Steps) (input: List HandlerClause): Result (List HandlerClause) Text :=
  Fail.toResult (() => traverseClauses on input)

def runInductArms (on: Steps) (input: List InductArm): Result (List InductArm) Text :=
  Fail.toResult (() => traverseInductArms on input)

def runCalcSteps (on: Steps) (input: List CalcStep): Result (List CalcStep) Text :=
  Fail.toResult (() => traverseSteps on input)

def runRules (on: Steps) (input: Rules): Result (Rules) Text := Fail.toResult (() => traverseRules on input)

def runRuleSet (on: Steps) (input: RuleSet): Result (RuleSet) Text := Fail.toResult (() => traverseRuleSet on input)

def runRuleList (on: Steps) (input: List RewriteRule): Result (List RewriteRule) Text :=
  Fail.toResult (() => traverseRuleList on input)

def runRow (on: Steps) (input: Row): Result (Row) Text := Fail.toResult (() => traverseRow on input)

def runExprs (on: Steps) (input: List Expr): Result (List Expr) Text := Fail.toResult (() => traverseExprs on input)

def runLinks (on: Steps) (input: List (Word, Expr)): Result (List (Word, Expr)) Text :=
  Fail.toResult (() => traverseLinks on input)

def runPieces (on: Steps) (input: List Piece): Result (List Piece) Text := Fail.toResult (() => traversePieces on input)

def runScrutinees (on: Steps) (input: List Scrutinee): Result (List Scrutinee) Text :=
  Fail.toResult (() => traverseScrutinees on input)

def runArms (on: Steps) (input: List Arm): Result (List Arm) Text := Fail.toResult (() => traverseArms on input)

def runParams (on: Steps) (input: List Param): Result (List Param) Text := Fail.toResult (() => traverseParams on input)

def runGroup (on: Steps) (input: Group): Result (Group) Text := Fail.toResult (() => input.traverse on)

def runPattern (on: Steps) (input: Pattern): Result (Pattern) Text := Fail.toResult (() => input.traverse on)

def runPatterns (on: Steps) (input: List Pattern): Result (List Pattern) Text :=
  Fail.toResult (() => traversePatterns on input)

def runPatternLinks (on: Steps) (input: List (Word, Pattern)): Result (List (Word, Pattern)) Text :=
  Fail.toResult (() => traversePatternLinks on input)

def runFieldsPattern (on: Steps) (input: FieldsPattern): Result (FieldsPattern) Text :=
  Fail.toResult (() => traverseFields on input)

def runFieldPatterns (on: Steps) (input: List FieldPattern): Result (List FieldPattern) Text :=
  Fail.toResult (() => traverseFieldPatterns on input)

def runDecl (on: Steps) (input: Decl): Result (Decl) Text := Fail.toResult (() => input.traverse on)

def runHeader (on: Steps) (input: Header): Result (Header) Text := Fail.toResult (() => traverseHeader on input)

def runDefBody (on: Steps) (input: DefBody): Result (DefBody) Text := Fail.toResult (() => traverseDefBody on input)

def runGroups (on: Steps) (input: List Group): Result (List Group) Text := Fail.toResult (() => traverseGroups on input)

def runIndices (on: Steps) (input: List (Index, Word)): Result (List (Index, Word)) Text :=
  Fail.toResult (() => traverseIndices on input)

def runFields (on: Steps) (input: Fields): Result (Fields) Text := Fail.toResult (() => input.traverse on)

def runFieldList (on: Steps) (input: List Field): Result (List Field) Text :=
  Fail.toResult (() => traverseFieldList on input)

def runConstructors (on: Steps) (input: List Constructor): Result (List Constructor) Text :=
  Fail.toResult (() => traverseConstructors on input)

def runParts (on: Steps) (input: List ConstructorPart): Result (List ConstructorPart) Text :=
  Fail.toResult (() => traverseParts on input)

def runOperations (on: Steps) (input: List Operation): Result (List Operation) Text :=
  Fail.toResult (() => traverseOperations on input)

def runAttributes (on: Steps) (input: List Attributes): Result (List Attributes) Text :=
  Fail.toResult (() => traverseAttributes on input)

def runOptional (on: Steps) (input: Option Expr): Result (Option Expr) Text :=
  Fail.toResult (() => traverseOptional on input)

def runAfter (on: Steps) (input: Option (k, Expr)): Result (Option (k, Expr)) Text :=
  Fail.toResult (() => traverseAfter on input)

def runGuard (on: Steps) (input: Option Guard): Result (Option Guard) Text :=
  Fail.toResult (() => traverseGuard on input)

def runTail (on: Steps) (input: Option (Word, Pattern)): Result (Option (Word, Pattern)) Text :=
  Fail.toResult (() => traverseTail on input)

def runBefore (on: Steps) (input: Option (Expr, k)): Result (Option (Expr, k)) Text :=
  Fail.toResult (() => traverseBefore on input)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem exprOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Expr): runExpr on input = Ok (input.walk p) :=
  match input with
    | Atom kind word => agree.expr (Atom kind word)
    | Paren open inner close =>
      rewrite Fail.toResultSeq1Then (exprOk on p agree inner), agree.expr (Paren open (inner.walk p) close)
    | Unit open close => agree.expr (Unit open close)
    | Universe keyword level => agree.expr (Universe keyword level)
    | Include keyword path => agree.expr (Include keyword path)
    | Tuple open items trailingComma close =>
      rewrite Fail.toResultSeq1Then (exprsOk on p agree items),
          agree.expr (Tuple open (walkExprs p items) trailingComma close)
    | ListOf open items trailingComma close =>
      rewrite Fail.toResultSeq1Then (exprsOk on p agree items),
          agree.expr (ListOf open (walkExprs p items) trailingComma close)
    | Spread dots list => rewrite Fail.toResultSeq1Then (exprOk on p agree list), agree.expr (Spread dots (list.walk p))
    | Record open base fields trailingComma close =>
      rewrite Fail.toResultSeq2Then (beforeOk on p agree base) (exprsOk on p agree fields),
          agree.expr (Record open (walkBefore p base) (walkExprs p fields) trailingComma close)
    | RecordField name equals value =>
      rewrite Fail.toResultSeq1Then (exprOk on p agree value), agree.expr (RecordField name equals (value.walk p))
    | CtorFields ctor record =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree ctor) (exprOk on p agree record),
          agree.expr (CtorFields (ctor.walk p) (record.walk p))
    | App head arguments =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree head) (exprsOk on p agree arguments),
          agree.expr (App (head.walk p) (walkExprs p arguments))
    | NamedArg open name colonEq value close =>
      rewrite Fail.toResultSeq1Then (exprOk on p agree value),
          agree.expr (NamedArg open name colonEq (value.walk p) close)
    | FieldAccess target dot field =>
      rewrite Fail.toResultSeq1Then (optionalOk on p agree target),
          agree.expr (FieldAccess (walkOptional p target) dot field)
    | Section body => rewrite Fail.toResultSeq1Then (exprOk on p agree body), agree.expr (Section (body.walk p))
    | OperatorSection open left operator right close =>
      rewrite Fail.toResultSeq2Then (optionalOk on p agree left) (optionalOk on p agree right),
          agree.expr (OperatorSection open (walkOptional p left) operator (walkOptional p right) close)
    | Infix kind left operator right =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree left) (exprOk on p agree right),
          agree.expr (Infix kind (left.walk p) operator (right.walk p))
    | Chain first rest =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree first) (linksOk on p agree rest),
          agree.expr (Chain (first.walk p) (walkLinks p rest))
    | Prefix operator operand =>
      rewrite Fail.toResultSeq1Then (exprOk on p agree operand), agree.expr (Prefix operator (operand.walk p))
    | Binding kind keyword params arrow body =>
      rewrite Fail.toResultSeq2Then (paramsOk on p agree params) (exprOk on p agree body),
          agree.expr (Binding kind keyword (walkParams p params) arrow (body.walk p))
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      rewrite Fail.toResultSeq3Then
            (exprOk on p agree condition)
            (exprOk on p agree whenTrue)
            (exprOk on p agree whenFalse),
          agree.expr (If keyword binder (condition.walk p) thenKeyword (whenTrue.walk p) elseKeyword (whenFalse.walk p))
    | Annotation open value colon annotation close =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree value) (exprOk on p agree annotation),
          agree.expr (Annotation open (value.walk p) colon (annotation.walk p) close)
    | Interpolated pieces =>
      rewrite Fail.toResultSeq1Then (piecesOk on p agree pieces), agree.expr (Interpolated (walkPieces p pieces))
    | Match keyword scrutinees withKeyword arms =>
      rewrite Fail.toResultSeq2Then (scrutineesOk on p agree scrutinees) (armsOk on p agree arms),
          agree.expr (Match keyword (walkScrutinees p scrutinees) withKeyword (walkArms p arms))
    | ClauseLambda keyword word arms =>
      rewrite Fail.toResultSeq1Then (armsOk on p agree arms), agree.expr (ClauseLambda keyword word (walkArms p arms))
    | Facts kind keyword facts =>
      rewrite Fail.toResultSeq1Then (exprOk on p agree facts), agree.expr (Facts kind keyword (facts.walk p))
    | FunctionType binder arrow result =>
      rewrite Fail.toResultSeq2Then (groupOk on p agree binder) (exprOk on p agree result),
          agree.expr (FunctionType (binder.walk p) arrow (result.walk p))
    | Effect row result =>
      rewrite Fail.toResultSeq2Then (rowOk on p agree row) (exprOk on p agree result),
          agree.expr (Effect (walkRow p row) (result.walk p))
    | Block first rest result =>
      rewrite Fail.toResultSeq3Then
            (statementOk on p agree first)
            (statementsOk on p agree rest)
            (exprOk on p agree result),
          agree.expr (Block (walkStatement p first) (walkStatements p rest) (result.walk p))
    | LetIn binding semicolon body =>
      rewrite Fail.toResultSeq2Then (letOk on p agree binding) (exprOk on p agree body),
          agree.expr (LetIn (walkLet p binding) semicolon (body.walk p))
    | Handle keyword computation withKeyword clauses =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree computation) (clausesOk on p agree clauses),
          agree.expr (Handle keyword (computation.walk p) withKeyword (walkClauses p clauses))
    | Reify keyword reifyWord computation withKeyword clauses =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree computation) (clausesOk on p agree clauses),
          agree.expr (Reify keyword reifyWord (computation.walk p) withKeyword (walkClauses p clauses))
    | Induct keyword inductWord call withKeyword arms =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree call) (inductArmsOk on p agree arms),
          agree.expr (Induct keyword inductWord (call.walk p) withKeyword (walkInductArms p arms))
    | Calc keyword first steps =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree first) (calcStepsOk on p agree steps),
          agree.expr (Calc keyword (first.walk p) (walkSteps p steps))
    | Rewrite keyword rules target body =>
      rewrite Fail.toResultSeq3Then (rulesOk on p agree rules) (afterOk on p agree target) (afterOk on p agree body),
          agree.expr (Rewrite keyword (walkRules p rules) (walkAfter p target) (walkAfter p body))
    | Cases keyword targets body =>
      rewrite Fail.toResultSeq1Then (afterOk on p agree body), agree.expr (Cases keyword targets (walkAfter p body))
    | Walk keyword items body =>
      rewrite Fail.toResultSeq2Then (exprOk on p agree items) (afterOk on p agree body),
          agree.expr (Walk keyword (items.walk p) (walkAfter p body))

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem statementsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Statement):
    runStatements on input = Ok (walkStatements p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => Fail.toResultSeq2 (statementOk on p agree first) (statementsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem statementOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Statement):
    runStatement on input = Ok (walkStatement p input) :=
  match input with
    | LetStatement binding => Fail.toResultSeq1 (letOk on p agree binding)
    | LocalDef attributes header body =>
      Fail.toResultSeq3 (attributesOk on p agree attributes) (headerOk on p agree header) (defBodyOk on p agree body)
    | ExprStatement value => Fail.toResultSeq1 (exprOk on p agree value)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem letOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Let): runLet on input = Ok (walkLet p input) :=
  match input with
    | { keyword, pattern, annotation, colonEq, value } =>
      Fail.toResultSeq3 (patternOk on p agree pattern) (afterOk on p agree annotation) (exprOk on p agree value)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem clausesOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List HandlerClause):
    runClauses on input = Ok (walkClauses p input) :=
  match input with
    | [] => byComputing
    | [ReturnClause bar keyword name arrow body, ..rest] =>
      Fail.toResultSeq2 (exprOk on p agree body) (clausesOk on p agree rest)
    | [OperationClause bar operation argument comma continuation arrow body, ..rest] =>
      Fail.toResultSeq3 (patternOk on p agree argument) (exprOk on p agree body) (clausesOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem inductArmsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List InductArm):
    runInductArms on input = Ok (walkInductArms p input) :=
  match input with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] =>
      Fail.toResultSeq2 (exprOk on p agree body) (inductArmsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem calcStepsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List CalcStep):
    runCalcSteps on input = Ok (walkSteps p input) :=
  match input with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] =>
      Fail.toResultSeq3 (exprOk on p agree operand) (afterOk on p agree proof) (calcStepsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem rulesOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Rules):
    runRules on input = Ok (walkRules p input) :=
  match input with
    | RuleList rules => Fail.toResultSeq1 (ruleListOk on p agree rules)
    | Repeatedly word set => Fail.toResultSeq1 (ruleSetOk on p agree set)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem ruleSetOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: RuleSet):
    runRuleSet on input = Ok (walkRuleSet p input) :=
  match input with
    | { open, rules, trailingComma, close } =>
      rewrite Fail.toResultSeq1Let [k := on.ruleSet] (ruleListOk on p agree rules),
          agree.ruleSet ({ open, rules = (walkRuleList p rules), trailingComma, close })

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem ruleListOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List RewriteRule):
    runRuleList on input = Ok (walkRuleList p input) :=
  match input with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] => Fail.toResultSeq2 (exprOk on p agree rule) (ruleListOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem rowOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Row): runRow on input = Ok (walkRow p input) :=
  match input with | { open, abilities, variable, close } => Fail.toResultSeq1 (exprsOk on p agree abilities)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem exprsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Expr):
    runExprs on input = Ok (walkExprs p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => Fail.toResultSeq2 (exprOk on p agree first) (exprsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem linksOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List (Word, Expr)):
    runLinks on input = Ok (walkLinks p input) :=
  match input with
    | [] => byComputing
    | [(operator, operand), ..rest] => Fail.toResultSeq2 (exprOk on p agree operand) (linksOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem piecesOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Piece):
    runPieces on input = Ok (walkPieces p input) :=
  match input with
    | [] => byComputing
    | [TextPiece word, ..rest] => Fail.toResultSeq1 (piecesOk on p agree rest)
    | [Interpolation open value close, ..rest] => Fail.toResultSeq2 (exprOk on p agree value) (piecesOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem scrutineesOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Scrutinee):
    runScrutinees on input = Ok (walkScrutinees p input) :=
  match input with
    | [] => byComputing
    | [{ name, value }, ..rest] => Fail.toResultSeq2 (exprOk on p agree value) (scrutineesOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem armsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Arm):
    runArms on input = Ok (walkArms p input) :=
  match input with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] =>
      Fail.toResultSeq4
        (patternsOk on p agree patterns)
        (guardOk on p agree guard)
        (afterOk on p agree body)
        (armsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem paramsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Param):
    runParams on input = Ok (walkParams p input) :=
  match input with
    | [] => byComputing
    | [NameParam word, ..rest] => Fail.toResultSeq1 (paramsOk on p agree rest)
    | [PatternParam pattern, ..rest] => Fail.toResultSeq2 (patternOk on p agree pattern) (paramsOk on p agree rest)
    | [Grouped group, ..rest] => Fail.toResultSeq2 (groupOk on p agree group) (paramsOk on p agree rest)
    | [TypedPattern open pattern colon annotation close, ..rest] =>
      Fail.toResultSeq3 (patternOk on p agree pattern) (exprOk on p agree annotation) (paramsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem groupOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Group): runGroup on input = Ok (input.walk p) :=
  match input with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
      Fail.toResultSeq3
        (attributesOk on p agree attributes)
        (optionalOk on p agree annotation)
        (afterOk on p agree default)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem patternOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Pattern):
    runPattern on input = Ok (input.walk p) :=
  match input with
    | PatternWord kind word => agree.pattern (PatternWord kind word)
    | PatternCtor name arguments =>
      rewrite Fail.toResultSeq1Then (patternsOk on p agree arguments),
          agree.pattern (PatternCtor name (walkPatterns p arguments))
    | PatternCtorFields name fields =>
      rewrite Fail.toResultSeq1Then (fieldsPatternOk on p agree fields),
          agree.pattern (PatternCtorFields name (walkFields p fields))
    | PatternRecord fields =>
      rewrite Fail.toResultSeq1Then (fieldsPatternOk on p agree fields),
          agree.pattern (PatternRecord (walkFields p fields))
    | PatternTuple open items trailingComma close =>
      rewrite Fail.toResultSeq1Then (patternsOk on p agree items),
          agree.pattern (PatternTuple open (walkPatterns p items) trailingComma close)
    | PatternList open items trailingComma tail close =>
      rewrite Fail.toResultSeq2Then (patternsOk on p agree items) (tailOk on p agree tail),
          agree.pattern (PatternList open (walkPatterns p items) trailingComma (walkTail p tail) close)
    | PatternNamed open name colonEq value close =>
      rewrite Fail.toResultSeq1Then (patternOk on p agree value),
          agree.pattern (PatternNamed open name colonEq (value.walk p) close)
    | PatternOr first rest =>
      rewrite Fail.toResultSeq2Then (patternOk on p agree first) (patternLinksOk on p agree rest),
          agree.pattern (PatternOr (first.walk p) (walkPatternLinks p rest))
    | PatternParen open inner close =>
      rewrite Fail.toResultSeq1Then (patternOk on p agree inner), agree.pattern (PatternParen open (inner.walk p) close)
    | PatternNegative minus number => agree.pattern (PatternNegative minus number)
    | PatternAbsurd open close => agree.pattern (PatternAbsurd open close)
    | PatternAppend start operator rest =>
      rewrite Fail.toResultSeq2Then (patternOk on p agree start) (patternOk on p agree rest),
          agree.pattern (PatternAppend (start.walk p) operator (rest.walk p))

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem patternsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Pattern):
    runPatterns on input = Ok (walkPatterns p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => Fail.toResultSeq2 (patternOk on p agree first) (patternsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem patternLinksOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List (Word, Pattern)):
    runPatternLinks on input = Ok (walkPatternLinks p input) :=
  match input with
    | [] => byComputing
    | [(bar, alternative), ..rest] =>
      Fail.toResultSeq2 (patternOk on p agree alternative) (patternLinksOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem fieldsPatternOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: FieldsPattern):
    runFieldsPattern on input = Ok (walkFields p input) :=
  match input with
    | { open, fields, trailingComma, rest, close } => Fail.toResultSeq1 (fieldPatternsOk on p agree fields)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem fieldPatternsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List FieldPattern):
    runFieldPatterns on input = Ok (walkFieldPatterns p input) :=
  match input with
    | [] => byComputing
    | [{ name, value = Some (equals, pattern) }, ..rest] =>
      Fail.toResultSeq2 (patternOk on p agree pattern) (fieldPatternsOk on p agree rest)
    | [{ name, value = None }, ..rest] => Fail.toResultSeq1 (fieldPatternsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem declOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Decl): runDecl on input = Ok (input.walk p) :=
  match input with
    | Namespace keyword name => agree.decl (Namespace keyword name)
    | Import keyword path open imported close => agree.decl (Import keyword path open imported close)
    | Definition attributes header body =>
      rewrite Fail.toResultSeq3Then
            (attributesOk on p agree attributes)
            (headerOk on p agree header)
            (defBodyOk on p agree body),
          agree.decl (Definition (walkAttributes p attributes) (walkHeader p header) (walkDefBody p body))
    | Data attributes isInterface keyword name params indices body =>
      match indices with
        | Some { colon, steps, last } =>
          match body with
            | Abstract =>
              rewrite Fail.toResultSeq3Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq2
                      [g := (w1 w2 => Some { colon, steps = w1, last = w2 })]
                      (indicesOk on p agree steps)
                      (exprOk on p agree last)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (Some { colon, steps = (walkIndices p steps), last = (last.walk p) })
                      (Abstract))
            | Synonym equals annotation =>
              rewrite Fail.toResultSeq4Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq2
                      [g := (w1 w2 => Some { colon, steps = w1, last = w2 })]
                      (indicesOk on p agree steps)
                      (exprOk on p agree last))
                    (Fail.toResultSeq1 [g := (w1 => Synonym equals w1)] (exprOk on p agree annotation)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (Some { colon, steps = (walkIndices p steps), last = (last.walk p) })
                      (Synonym equals (annotation.walk p)))
            | RecordBody equals fields =>
              rewrite Fail.toResultSeq4Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq2
                      [g := (w1 w2 => Some { colon, steps = w1, last = w2 })]
                      (indicesOk on p agree steps)
                      (exprOk on p agree last))
                    (Fail.toResultSeq1 [g := (w1 => RecordBody equals w1)] (fieldsOk on p agree fields)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (Some { colon, steps = (walkIndices p steps), last = (last.walk p) })
                      (RecordBody equals (fields.walk p)))
            | Sum equals constructors =>
              rewrite Fail.toResultSeq4Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq2
                      [g := (w1 w2 => Some { colon, steps = w1, last = w2 })]
                      (indicesOk on p agree steps)
                      (exprOk on p agree last))
                    (Fail.toResultSeq1 [g := (w1 => Sum equals w1)] (constructorsOk on p agree constructors)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (Some { colon, steps = (walkIndices p steps), last = (last.walk p) })
                      (Sum equals (walkConstructors p constructors)))
        | None =>
          match body with
            | Abstract =>
              rewrite Fail.toResultSeq2Then (attributesOk on p agree attributes) (groupsOk on p agree params),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (None)
                      (Abstract))
            | Synonym equals annotation =>
              rewrite Fail.toResultSeq3Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq1 [g := (w1 => Synonym equals w1)] (exprOk on p agree annotation)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (None)
                      (Synonym equals (annotation.walk p)))
            | RecordBody equals fields =>
              rewrite Fail.toResultSeq3Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq1 [g := (w1 => RecordBody equals w1)] (fieldsOk on p agree fields)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (None)
                      (RecordBody equals (fields.walk p)))
            | Sum equals constructors =>
              rewrite Fail.toResultSeq3Then
                    (attributesOk on p agree attributes)
                    (groupsOk on p agree params)
                    (Fail.toResultSeq1 [g := (w1 => Sum equals w1)] (constructorsOk on p agree constructors)),
                  agree.decl
                    (Data
                      (walkAttributes p attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups p params)
                      (None)
                      (Sum equals (walkConstructors p constructors)))
    | Ability keyword name params whereKeyword operations =>
      rewrite Fail.toResultSeq2Then (groupsOk on p agree params) (operationsOk on p agree operations),
          agree.decl (Ability keyword name (walkGroups p params) whereKeyword (walkOperations p operations))
    | Test keyword name colonEq body =>
      rewrite Fail.toResultSeq1Then (exprOk on p agree body), agree.decl (Test keyword name colonEq (body.walk p))
    | RuleSetDecl keyword name colonEq set =>
      rewrite Fail.toResultSeq1Then (ruleSetOk on p agree set),
          agree.decl (RuleSetDecl keyword name colonEq (walkRuleSet p set))

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem headerOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Header):
    runHeader on input = Ok (walkHeader p input) :=
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
      rewrite Fail.toResultSeq3Let
            [k := on.header]
            (groupsOk on p agree params)
            (exprOk on p agree result)
            (afterOk on p agree decreasingClause),
          agree.header
            ({
              exportKeyword,
              opaqueKeyword,
              kind,
              keyword,
              name,
              forallKeyword,
              params = (walkGroups p params),
              colon,
              result = (result.walk p),
              decreasingClause = (walkAfter p decreasingClause),
              unfoldingClause
            })

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem defBodyOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: DefBody):
    runDefBody on input = Ok (walkDefBody p input) :=
  match input with
    | Primitive => byComputing
    | Assigned colonEq value => Fail.toResultSeq1 (exprOk on p agree value)
    | Arms arms => Fail.toResultSeq1 (armsOk on p agree arms)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem groupsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Group):
    runGroups on input = Ok (walkGroups p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => Fail.toResultSeq2 (groupOk on p agree first) (groupsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem indicesOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List (Index, Word)):
    runIndices on input = Ok (walkIndices p input) :=
  match input with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] => Fail.toResultSeq2 (groupOk on p agree binder) (indicesOk on p agree rest)
    | [(IndexType annotation, arrow), ..rest] =>
      Fail.toResultSeq2 (exprOk on p agree annotation) (indicesOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem fieldsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Fields): runFields on input = Ok (input.walk p) :=
  match input with
    | { open, fields, trailingComma, close } =>
      rewrite Fail.toResultSeq1Let [k := on.fields] (fieldListOk on p agree fields),
          agree.fields ({ open, fields = (walkFieldList p fields), trailingComma, close })

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem fieldListOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Field):
    runFieldList on input = Ok (walkFieldList p input) :=
  match input with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] =>
      Fail.toResultSeq4
        (attributesOk on p agree attributes)
        (exprOk on p agree annotation)
        (afterOk on p agree default)
        (fieldListOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem constructorsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Constructor):
    runConstructors on input = Ok (walkConstructors p input) :=
  match input with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] =>
      Fail.toResultSeq4
        (attributesOk on p agree attributes)
        (partsOk on p agree fields)
        (afterOk on p agree result)
        (constructorsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem partsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List ConstructorPart):
    runParts on input = Ok (walkParts p input) :=
  match input with
    | [] => byComputing
    | [PartGroup group, ..rest] => Fail.toResultSeq2 (groupOk on p agree group) (partsOk on p agree rest)
    | [PartFields fields, ..rest] => Fail.toResultSeq2 (fieldsOk on p agree fields) (partsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem operationsOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Operation):
    runOperations on input = Ok (walkOperations p input) :=
  match input with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] =>
      Fail.toResultSeq2 (exprOk on p agree annotation) (operationsOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem attributesOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: List Attributes):
    runAttributes on input = Ok (walkAttributes p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => Fail.toResultSeq2 (agree.attributes first) (attributesOk on p agree rest)

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem optionalOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Option Expr):
    runOptional on input = Ok (walkOptional p input) :=
  match input with
    | Some value => Fail.toResultSeq1 (exprOk on p agree value)
    | None => byComputing

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem afterOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Option (k, Expr)):
    runAfter on input = Ok (walkAfter p input) :=
  match input with
    | Some (word, value) => Fail.toResultSeq1 (exprOk on p agree value)
    | None => byComputing

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem guardOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Option Guard):
    runGuard on input = Ok (walkGuard p input) :=
  match input with
    | Some { keyword, binder, condition } => Fail.toResultSeq1 (exprOk on p agree condition)
    | None => byComputing

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem tailOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Option (Word, Pattern)):
    runTail on input = Ok (walkTail p input) :=
  match input with
    | Some (dots, rest) => Fail.toResultSeq1 (patternOk on p agree rest)
    | None => byComputing

--| The traversal finishes, with the pure copy's result. By induction
--| alongside the traversal: in each arm the children's computations
--| finish (the induction hypotheses), so the arm's binds compute
--| (`seqN`, `seqNk`, `seqNj`), and then the step agrees.
theorem beforeOk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (input: Option (Expr, k)):
    runBefore on input = Ok (walkBefore p input) :=
  match input with
    | Some (value, word) => Fail.toResultSeq1 (exprOk on p agree value)
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem exprTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Expr): (input.walk s).walk m = input.walk m :=
  match input with
    | Atom kind word => rewrite keeps.expr (Atom kind word)
    | Paren open inner close => rewrite keeps.expr (Paren open (inner.walk s) close), exprTwice s m keeps inner
    | Unit open close => rewrite keeps.expr (Unit open close)
    | Universe keyword level => rewrite keeps.expr (Universe keyword level)
    | Include keyword path => rewrite keeps.expr (Include keyword path)
    | Tuple open items trailingComma close =>
      rewrite keeps.expr (Tuple open (walkExprs s items) trailingComma close), exprsTwice s m keeps items
    | ListOf open items trailingComma close =>
      rewrite keeps.expr (ListOf open (walkExprs s items) trailingComma close), exprsTwice s m keeps items
    | Spread dots list => rewrite keeps.expr (Spread dots (list.walk s)), exprTwice s m keeps list
    | Record open base fields trailingComma close =>
      rewrite keeps.expr (Record open (walkBefore s base) (walkExprs s fields) trailingComma close),
          beforeTwice s m keeps base,
          exprsTwice s m keeps fields
    | RecordField name equals value =>
      rewrite keeps.expr (RecordField name equals (value.walk s)), exprTwice s m keeps value
    | CtorFields ctor record =>
      rewrite keeps.expr (CtorFields (ctor.walk s) (record.walk s)),
          exprTwice s m keeps ctor,
          exprTwice s m keeps record
    | App head arguments =>
      rewrite keeps.expr (App (head.walk s) (walkExprs s arguments)),
          exprTwice s m keeps head,
          exprsTwice s m keeps arguments
    | NamedArg open name colonEq value close =>
      rewrite keeps.expr (NamedArg open name colonEq (value.walk s) close), exprTwice s m keeps value
    | FieldAccess target dot field =>
      rewrite keeps.expr (FieldAccess (walkOptional s target) dot field), optionalTwice s m keeps target
    | Section body => rewrite keeps.expr (Section (body.walk s)), exprTwice s m keeps body
    | OperatorSection open left operator right close =>
      rewrite keeps.expr (OperatorSection open (walkOptional s left) operator (walkOptional s right) close),
          optionalTwice s m keeps left,
          optionalTwice s m keeps right
    | Infix kind left operator right =>
      rewrite keeps.expr (Infix kind (left.walk s) operator (right.walk s)),
          exprTwice s m keeps left,
          exprTwice s m keeps right
    | Chain first rest =>
      rewrite keeps.expr (Chain (first.walk s) (walkLinks s rest)), exprTwice s m keeps first, linksTwice s m keeps rest
    | Prefix operator operand => rewrite keeps.expr (Prefix operator (operand.walk s)), exprTwice s m keeps operand
    | Binding kind keyword params arrow body =>
      rewrite keeps.expr (Binding kind keyword (walkParams s params) arrow (body.walk s)),
          paramsTwice s m keeps params,
          exprTwice s m keeps body
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      rewrite keeps.expr
            (If keyword binder (condition.walk s) thenKeyword (whenTrue.walk s) elseKeyword (whenFalse.walk s)),
          exprTwice s m keeps condition,
          exprTwice s m keeps whenTrue,
          exprTwice s m keeps whenFalse
    | Annotation open value colon annotation close =>
      rewrite keeps.expr (Annotation open (value.walk s) colon (annotation.walk s) close),
          exprTwice s m keeps value,
          exprTwice s m keeps annotation
    | Interpolated pieces => rewrite keeps.expr (Interpolated (walkPieces s pieces)), piecesTwice s m keeps pieces
    | Match keyword scrutinees withKeyword arms =>
      rewrite keeps.expr (Match keyword (walkScrutinees s scrutinees) withKeyword (walkArms s arms)),
          scrutineesTwice s m keeps scrutinees,
          armsTwice s m keeps arms
    | ClauseLambda keyword word arms =>
      rewrite keeps.expr (ClauseLambda keyword word (walkArms s arms)), armsTwice s m keeps arms
    | Facts kind keyword facts => rewrite keeps.expr (Facts kind keyword (facts.walk s)), exprTwice s m keeps facts
    | FunctionType binder arrow result =>
      rewrite keeps.expr (FunctionType (binder.walk s) arrow (result.walk s)),
          groupTwice s m keeps binder,
          exprTwice s m keeps result
    | Effect row result =>
      rewrite keeps.expr (Effect (walkRow s row) (result.walk s)), rowTwice s m keeps row, exprTwice s m keeps result
    | Block first rest result =>
      rewrite keeps.expr (Block (walkStatement s first) (walkStatements s rest) (result.walk s)),
          statementTwice s m keeps first,
          statementsTwice s m keeps rest,
          exprTwice s m keeps result
    | LetIn binding semicolon body =>
      rewrite keeps.expr (LetIn (walkLet s binding) semicolon (body.walk s)),
          letTwice s m keeps binding,
          exprTwice s m keeps body
    | Handle keyword computation withKeyword clauses =>
      rewrite keeps.expr (Handle keyword (computation.walk s) withKeyword (walkClauses s clauses)),
          exprTwice s m keeps computation,
          clausesTwice s m keeps clauses
    | Reify keyword reifyWord computation withKeyword clauses =>
      rewrite keeps.expr (Reify keyword reifyWord (computation.walk s) withKeyword (walkClauses s clauses)),
          exprTwice s m keeps computation,
          clausesTwice s m keeps clauses
    | Induct keyword inductWord call withKeyword arms =>
      rewrite keeps.expr (Induct keyword inductWord (call.walk s) withKeyword (walkInductArms s arms)),
          exprTwice s m keeps call,
          inductArmsTwice s m keeps arms
    | Calc keyword first steps =>
      rewrite keeps.expr (Calc keyword (first.walk s) (walkSteps s steps)),
          exprTwice s m keeps first,
          calcStepsTwice s m keeps steps
    | Rewrite keyword rules target body =>
      rewrite keeps.expr (Rewrite keyword (walkRules s rules) (walkAfter s target) (walkAfter s body)),
          rulesTwice s m keeps rules,
          afterTwice s m keeps target,
          afterTwice s m keeps body
    | Cases keyword targets body =>
      rewrite keeps.expr (Cases keyword targets (walkAfter s body)), afterTwice s m keeps body
    | Walk keyword items body =>
      rewrite keeps.expr (Walk keyword (items.walk s) (walkAfter s body)),
          exprTwice s m keeps items,
          afterTwice s m keeps body

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem statementsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Statement):
    walkStatements m (walkStatements s input) = walkStatements m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite statementTwice s m keeps first, statementsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem statementTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Statement):
    walkStatement m (walkStatement s input) = walkStatement m input :=
  match input with
    | LetStatement binding => rewrite letTwice s m keeps binding
    | LocalDef attributes header body =>
      rewrite attributesTwice s m keeps attributes, headerTwice s m keeps header, defBodyTwice s m keeps body
    | ExprStatement value => rewrite exprTwice s m keeps value

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem letTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Let): walkLet m (walkLet s input) = walkLet m input :=
  match input with
    | { keyword, pattern, annotation, colonEq, value } =>
      rewrite patternTwice s m keeps pattern, afterTwice s m keeps annotation, exprTwice s m keeps value

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem clausesTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List HandlerClause):
    walkClauses m (walkClauses s input) = walkClauses m input :=
  match input with
    | [] => byComputing
    | [ReturnClause bar keyword name arrow body, ..rest] =>
      rewrite exprTwice s m keeps body, clausesTwice s m keeps rest
    | [OperationClause bar operation argument comma continuation arrow body, ..rest] =>
      rewrite patternTwice s m keeps argument, exprTwice s m keeps body, clausesTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem inductArmsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List InductArm):
    walkInductArms m (walkInductArms s input) = walkInductArms m input :=
  match input with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] => rewrite exprTwice s m keeps body, inductArmsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem calcStepsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List CalcStep):
    walkSteps m (walkSteps s input) = walkSteps m input :=
  match input with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] =>
      rewrite exprTwice s m keeps operand, afterTwice s m keeps proof, calcStepsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem rulesTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Rules):
    walkRules m (walkRules s input) = walkRules m input :=
  match input with
    | RuleList rules => rewrite ruleListTwice s m keeps rules
    | Repeatedly word set => rewrite ruleSetTwice s m keeps set

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem ruleSetTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: RuleSet):
    walkRuleSet m (walkRuleSet s input) = walkRuleSet m input :=
  match input with
    | { open, rules, trailingComma, close } =>
      rewrite keeps.ruleSet ({ open, rules = (walkRuleList s rules), trailingComma, close }),
          ruleListTwice s m keeps rules

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem ruleListTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List RewriteRule):
    walkRuleList m (walkRuleList s input) = walkRuleList m input :=
  match input with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] => rewrite exprTwice s m keeps rule, ruleListTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem rowTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Row): walkRow m (walkRow s input) = walkRow m input :=
  match input with | { open, abilities, variable, close } => rewrite exprsTwice s m keeps abilities

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem exprsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Expr):
    walkExprs m (walkExprs s input) = walkExprs m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite exprTwice s m keeps first, exprsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem linksTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List (Word, Expr)):
    walkLinks m (walkLinks s input) = walkLinks m input :=
  match input with
    | [] => byComputing
    | [(operator, operand), ..rest] => rewrite exprTwice s m keeps operand, linksTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem piecesTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Piece):
    walkPieces m (walkPieces s input) = walkPieces m input :=
  match input with
    | [] => byComputing
    | [TextPiece word, ..rest] => rewrite piecesTwice s m keeps rest
    | [Interpolation open value close, ..rest] => rewrite exprTwice s m keeps value, piecesTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem scrutineesTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Scrutinee):
    walkScrutinees m (walkScrutinees s input) = walkScrutinees m input :=
  match input with
    | [] => byComputing
    | [{ name, value }, ..rest] => rewrite exprTwice s m keeps value, scrutineesTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem armsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Arm):
    walkArms m (walkArms s input) = walkArms m input :=
  match input with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] =>
      rewrite patternsTwice s m keeps patterns,
          guardTwice s m keeps guard,
          afterTwice s m keeps body,
          armsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem paramsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Param):
    walkParams m (walkParams s input) = walkParams m input :=
  match input with
    | [] => byComputing
    | [NameParam word, ..rest] => rewrite paramsTwice s m keeps rest
    | [PatternParam pattern, ..rest] => rewrite patternTwice s m keeps pattern, paramsTwice s m keeps rest
    | [Grouped group, ..rest] => rewrite groupTwice s m keeps group, paramsTwice s m keeps rest
    | [TypedPattern open pattern colon annotation close, ..rest] =>
      rewrite patternTwice s m keeps pattern, exprTwice s m keeps annotation, paramsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem groupTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Group): (input.walk s).walk m = input.walk m :=
  match input with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
      rewrite attributesTwice s m keeps attributes, optionalTwice s m keeps annotation, afterTwice s m keeps default

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem patternTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Pattern): (input.walk s).walk m = input.walk m :=
  match input with
    | PatternWord kind word => rewrite keeps.pattern (PatternWord kind word)
    | PatternCtor name arguments =>
      rewrite keeps.pattern (PatternCtor name (walkPatterns s arguments)), patternsTwice s m keeps arguments
    | PatternCtorFields name fields =>
      rewrite keeps.pattern (PatternCtorFields name (walkFields s fields)), fieldsPatternTwice s m keeps fields
    | PatternRecord fields =>
      rewrite keeps.pattern (PatternRecord (walkFields s fields)), fieldsPatternTwice s m keeps fields
    | PatternTuple open items trailingComma close =>
      rewrite keeps.pattern (PatternTuple open (walkPatterns s items) trailingComma close),
          patternsTwice s m keeps items
    | PatternList open items trailingComma tail close =>
      rewrite keeps.pattern (PatternList open (walkPatterns s items) trailingComma (walkTail s tail) close),
          patternsTwice s m keeps items,
          tailTwice s m keeps tail
    | PatternNamed open name colonEq value close =>
      rewrite keeps.pattern (PatternNamed open name colonEq (value.walk s) close), patternTwice s m keeps value
    | PatternOr first rest =>
      rewrite keeps.pattern (PatternOr (first.walk s) (walkPatternLinks s rest)),
          patternTwice s m keeps first,
          patternLinksTwice s m keeps rest
    | PatternParen open inner close =>
      rewrite keeps.pattern (PatternParen open (inner.walk s) close), patternTwice s m keeps inner
    | PatternNegative minus number => rewrite keeps.pattern (PatternNegative minus number)
    | PatternAbsurd open close => rewrite keeps.pattern (PatternAbsurd open close)
    | PatternAppend start operator rest =>
      rewrite keeps.pattern (PatternAppend (start.walk s) operator (rest.walk s)),
          patternTwice s m keeps start,
          patternTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem patternsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Pattern):
    walkPatterns m (walkPatterns s input) = walkPatterns m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite patternTwice s m keeps first, patternsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem patternLinksTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List (Word, Pattern)):
    walkPatternLinks m (walkPatternLinks s input) = walkPatternLinks m input :=
  match input with
    | [] => byComputing
    | [(bar, alternative), ..rest] => rewrite patternTwice s m keeps alternative, patternLinksTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem fieldsPatternTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: FieldsPattern):
    walkFields m (walkFields s input) = walkFields m input :=
  match input with | { open, fields, trailingComma, rest, close } => rewrite fieldPatternsTwice s m keeps fields

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem fieldPatternsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List FieldPattern):
    walkFieldPatterns m (walkFieldPatterns s input) = walkFieldPatterns m input :=
  match input with
    | [] => byComputing
    | [{ name, value = Some (equals, pattern) }, ..rest] =>
      rewrite patternTwice s m keeps pattern, fieldPatternsTwice s m keeps rest
    | [{ name, value = None }, ..rest] => rewrite fieldPatternsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem declTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Decl): (input.walk s).walk m = input.walk m :=
  match input with
    | Namespace keyword name => rewrite keeps.decl (Namespace keyword name)
    | Import keyword path open imported close => rewrite keeps.decl (Import keyword path open imported close)
    | Definition attributes header body =>
      rewrite keeps.decl (Definition (walkAttributes s attributes) (walkHeader s header) (walkDefBody s body)),
          attributesTwice s m keeps attributes,
          headerTwice s m keeps header,
          defBodyTwice s m keeps body
    | Data attributes isInterface keyword name params indices body =>
      match indices with
        | Some { colon, steps, last } =>
          match body with
            | Abstract =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (Some { colon, steps = (walkIndices s steps), last = (last.walk s) })
                      (Abstract)),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  indicesTwice s m keeps steps,
                  exprTwice s m keeps last
            | Synonym equals annotation =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (Some { colon, steps = (walkIndices s steps), last = (last.walk s) })
                      (Synonym equals (annotation.walk s))),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  indicesTwice s m keeps steps,
                  exprTwice s m keeps last,
                  exprTwice s m keeps annotation
            | RecordBody equals fields =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (Some { colon, steps = (walkIndices s steps), last = (last.walk s) })
                      (RecordBody equals (fields.walk s))),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  indicesTwice s m keeps steps,
                  exprTwice s m keeps last,
                  fieldsTwice s m keeps fields
            | Sum equals constructors =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (Some { colon, steps = (walkIndices s steps), last = (last.walk s) })
                      (Sum equals (walkConstructors s constructors))),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  indicesTwice s m keeps steps,
                  exprTwice s m keeps last,
                  constructorsTwice s m keeps constructors
        | None =>
          match body with
            | Abstract =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (None)
                      (Abstract)),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params
            | Synonym equals annotation =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (None)
                      (Synonym equals (annotation.walk s))),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  exprTwice s m keeps annotation
            | RecordBody equals fields =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (None)
                      (RecordBody equals (fields.walk s))),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  fieldsTwice s m keeps fields
            | Sum equals constructors =>
              rewrite keeps.decl
                    (Data
                      (walkAttributes s attributes)
                      isInterface
                      keyword
                      name
                      (walkGroups s params)
                      (None)
                      (Sum equals (walkConstructors s constructors))),
                  attributesTwice s m keeps attributes,
                  groupsTwice s m keeps params,
                  constructorsTwice s m keeps constructors
    | Ability keyword name params whereKeyword operations =>
      rewrite keeps.decl (Ability keyword name (walkGroups s params) whereKeyword (walkOperations s operations)),
          groupsTwice s m keeps params,
          operationsTwice s m keeps operations
    | Test keyword name colonEq body =>
      rewrite keeps.decl (Test keyword name colonEq (body.walk s)), exprTwice s m keeps body
    | RuleSetDecl keyword name colonEq set =>
      rewrite keeps.decl (RuleSetDecl keyword name colonEq (walkRuleSet s set)), ruleSetTwice s m keeps set

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem headerTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Header):
    walkHeader m (walkHeader s input) = walkHeader m input :=
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
      rewrite keeps.header
            ({
              exportKeyword,
              opaqueKeyword,
              kind,
              keyword,
              name,
              forallKeyword,
              params = (walkGroups s params),
              colon,
              result = (result.walk s),
              decreasingClause = (walkAfter s decreasingClause),
              unfoldingClause
            }),
          groupsTwice s m keeps params,
          exprTwice s m keeps result,
          afterTwice s m keeps decreasingClause

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem defBodyTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: DefBody):
    walkDefBody m (walkDefBody s input) = walkDefBody m input :=
  match input with
    | Primitive => byComputing
    | Assigned colonEq value => rewrite exprTwice s m keeps value
    | Arms arms => rewrite armsTwice s m keeps arms

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem groupsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Group):
    walkGroups m (walkGroups s input) = walkGroups m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite groupTwice s m keeps first, groupsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem indicesTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List (Index, Word)):
    walkIndices m (walkIndices s input) = walkIndices m input :=
  match input with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] => rewrite groupTwice s m keeps binder, indicesTwice s m keeps rest
    | [(IndexType annotation, arrow), ..rest] => rewrite exprTwice s m keeps annotation, indicesTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem fieldsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Fields): (input.walk s).walk m = input.walk m :=
  match input with
    | { open, fields, trailingComma, close } =>
      rewrite keeps.fields ({ open, fields = (walkFieldList s fields), trailingComma, close }),
          fieldListTwice s m keeps fields

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem fieldListTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Field):
    walkFieldList m (walkFieldList s input) = walkFieldList m input :=
  match input with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] =>
      rewrite attributesTwice s m keeps attributes,
          exprTwice s m keeps annotation,
          afterTwice s m keeps default,
          fieldListTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem constructorsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Constructor):
    walkConstructors m (walkConstructors s input) = walkConstructors m input :=
  match input with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] =>
      rewrite attributesTwice s m keeps attributes,
          partsTwice s m keeps fields,
          afterTwice s m keeps result,
          constructorsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem partsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List ConstructorPart):
    walkParts m (walkParts s input) = walkParts m input :=
  match input with
    | [] => byComputing
    | [PartGroup group, ..rest] => rewrite groupTwice s m keeps group, partsTwice s m keeps rest
    | [PartFields fields, ..rest] => rewrite fieldsTwice s m keeps fields, partsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem operationsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Operation):
    walkOperations m (walkOperations s input) = walkOperations m input :=
  match input with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] => rewrite exprTwice s m keeps annotation, operationsTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem attributesTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: List Attributes):
    walkAttributes m (walkAttributes s input) = walkAttributes m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite keeps.attributes first, attributesTwice s m keeps rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem optionalTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Option Expr):
    walkOptional m (walkOptional s input) = walkOptional m input :=
  match input with
    | Some value => rewrite exprTwice s m keeps value
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem afterTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Option (k, Expr)):
    walkAfter m (walkAfter s input) = walkAfter m input :=
  match input with
    | Some (word, value) => rewrite exprTwice s m keeps value
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem guardTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Option Guard):
    walkGuard m (walkGuard s input) = walkGuard m input :=
  match input with
    | Some { keyword, binder, condition } => rewrite exprTwice s m keeps condition
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem tailTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Option (Word, Pattern)):
    walkTail m (walkTail s input) = walkTail m input :=
  match input with
    | Some (dots, rest) => rewrite patternTwice s m keeps rest
    | None => byComputing

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem beforeTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (input: Option (Expr, k)):
    walkBefore m (walkBefore s input) = walkBefore m input :=
  match input with
    | Some (value, word) => rewrite exprTwice s m keeps value
    | None => byComputing

-- A file.

def walkDecls (p: Pure): List Decl → List Decl
  | [] => []
  | [decl, ..rest] => [decl.walk p, ..walkDecls p rest]

theorem applyDeclsWalk ∀ (on: Steps) (p: Pure)
    (agree: Agrees on p) (decls: List Decl):
    applyDecls on decls = walkDecls p decls :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] => rewrite declOk on p agree decl, applyDeclsWalk on p agree rest

--| Walking with `s` then `m` is walking with `m`. By induction: in each
--| arm, `Keeps` takes `s`'s step off the rebuilt node, then the
--| induction hypotheses take `s`'s walk off each child.
theorem walkDeclsTwice ∀ (s m: Pure)
    (keeps: Keeps s m) (decls: List Decl):
    walkDecls m (walkDecls s decls) = walkDecls m decls :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] => rewrite declTwice s m keeps decl, walkDeclsTwice s m keeps rest

--| A pass whose steps all finish is its pure copy's walk.
theorem applyWalk ∀ (file: SourceFile) (on: Steps) (p: Pure)
    (agree: Agrees on p):
    file.apply on = { file | decls = walkDecls p file.decls } :=
  rewrite applyDeclsWalk on p agree file.decls

--| The traversal lemma: a pass `on` whose steps finish as `s`'s do, and
--| `s`'s each keep what walking with `m` gives, keeps what applying `mean`
--| (whose steps finish as `m`'s) gives. The steps may rebuild the node's
--| descendants (`Keeps`).
theorem applyKeeps ∀ (file: SourceFile) (on mean: Steps) (s m: Pure)
    (agreeS: Agrees on s)
    (agreeM: Agrees mean m)
    (keeps: Keeps s m):
    (file.apply on).apply mean = file.apply mean :=
  rewrite applyWalk file on s agreeS,
      applyWalk { file | decls = walkDecls s file.decls } mean m agreeM,
      applyWalk file mean m agreeM,
      walkDeclsTwice s m keeps file.decls
