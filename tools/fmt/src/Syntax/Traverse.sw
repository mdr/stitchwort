--| The tree's traversal (tools/fmt-sketch/SKETCH.md §1, the traversal
--| item): one function per family that rebuilds a node from its traversed
--| children, left to right, then applies a step to it. `Steps` holds the
--| step for expressions, patterns, headers and declarations; a family
--| without a step is rebuilt as it was. The steps may `Fail`: the
--| lowering's checks do, and a tidy pass that rewrites never does.
--| (Generic in the steps' abilities, `{e}`, the mutually recursive
--| functions here are refused with E-NOT-A-FUNCTION at the first call from
--| one to another inside a `let`.)

namespace Syntax
import Std (Fail, List, Option)

--| What the traversal does to each node once its children are done: a
--| header's step is also applied to a local definition's.
type Steps = {
  expr: Expr → {Fail} Expr,
  pattern: Pattern → {Fail} Pattern,
  header: Header → {Fail} Header,
  decl: Decl → {Fail} Decl,
  fields: Fields → {Fail} Fields,
  attributes: Attributes → {Fail} Attributes,
  ruleSet: RuleSet → {Fail} RuleSet
}

--| The steps that change nothing.
def Steps.keep: Steps := {
  expr = (e => e),
  pattern = (p => p),
  header = (h => h),
  decl = (d => d),
  fields = (f => f),
  attributes = (a => a),
  ruleSet = (r => r)
}

def Expr.traverse (expr: Expr) (on: Steps): {Fail} Expr :=
  let rebuilt := match expr with
    | Atom kind word => Atom kind word
    | Paren open inner close => Paren open (inner.traverse on) close
    | Unit open close => Unit open close
    | Universe keyword level => Universe keyword level
    | Include keyword path => Include keyword path
    | Tuple open items trailingComma close => Tuple open (traverseExprs on items) trailingComma close
    | ListOf open items trailingComma close => ListOf open (traverseExprs on items) trailingComma close
    | Spread dots list => Spread dots (list.traverse on)
    | Record open base fields trailingComma close =>
      let based := traverseBefore on base
      Record open based (traverseExprs on fields) trailingComma close
    | RecordField name equals value => RecordField name equals (value.traverse on)
    | CtorFields ctor record =>
      let ctor' := ctor.traverse on
      CtorFields ctor' (record.traverse on)
    | App head arguments =>
      let head' := head.traverse on
      App head' (traverseExprs on arguments)
    | NamedArg open name colonEq value close => NamedArg open name colonEq (value.traverse on) close
    | FieldAccess target dot field =>
      let target' := traverseOptional on target
      FieldAccess target' dot field
    | Section body => Section (body.traverse on)
    | OperatorSection open left operator right close =>
      let left' := traverseOptional on left
      let right' := traverseOptional on right
      OperatorSection open left' operator right' close
    | Infix kind left operator right =>
      let left' := left.traverse on
      Infix kind left' operator (right.traverse on)
    | Chain first rest =>
      let first' := first.traverse on
      Chain first' (traverseLinks on rest)
    | Prefix operator operand => Prefix operator (operand.traverse on)
    | Binding kind keyword params arrow body =>
      let params' := traverseParams on params
      Binding kind keyword params' arrow (body.traverse on)
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      let condition' := condition.traverse on
      let whenTrue' := whenTrue.traverse on
      If keyword binder condition' thenKeyword whenTrue' elseKeyword (whenFalse.traverse on)
    | Annotation open value colon annotation close =>
      let value' := value.traverse on
      Annotation open value' colon (annotation.traverse on) close
    | Interpolated pieces => Interpolated (traversePieces on pieces)
    | Match keyword scrutinees withKeyword arms =>
      let scrutinees' := traverseScrutinees on scrutinees
      Match keyword scrutinees' withKeyword (traverseArms on arms)
    | ClauseLambda keyword word arms => ClauseLambda keyword word (traverseArms on arms)
    | Facts kind keyword facts => Facts kind keyword (facts.traverse on)
    | FunctionType binder arrow result =>
      let binder' := binder.traverse on
      FunctionType binder' arrow (result.traverse on)
    | Effect row result =>
      let row' := traverseRow on row
      Effect row' (result.traverse on)
    | Block first rest result =>
      let first' := traverseStatement on first
      let rest' := traverseStatements on rest
      Block first' rest' (result.traverse on)
    | LetIn binding semicolon body =>
      let binding' := traverseLet on binding
      LetIn binding' semicolon (body.traverse on)
    | Handle keyword computation withKeyword clauses =>
      let computation' := computation.traverse on
      Handle keyword computation' withKeyword (traverseClauses on clauses)
    | Reify keyword reify computation withKeyword clauses =>
      let computation' := computation.traverse on
      Reify keyword reify computation' withKeyword (traverseClauses on clauses)
    | Induct keyword induct call withKeyword arms =>
      let call' := call.traverse on
      Induct keyword induct call' withKeyword (traverseInductArms on arms)
    | Calc keyword first steps =>
      let first' := first.traverse on
      Calc keyword first' (traverseSteps on steps)
    | Rewrite keyword rules target body =>
      let rules' := traverseRules on rules
      let target' := traverseAfter on target
      Rewrite keyword rules' target' (traverseAfter on body)
    | Cases keyword thenKeyword body => Cases keyword thenKeyword (body.traverse on)
    | Walk keyword items body =>
      let items' := items.traverse on
      Walk keyword items' (traverseAfter on body)
  on.expr rebuilt

def traverseStatements (on: Steps) (input: List Statement): {Fail} List Statement := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := traverseStatement on first
    [first', ..traverseStatements on rest]

def traverseStatement (on: Steps) (input: Statement): {Fail} Statement := match input with
  | LetStatement binding => LetStatement (traverseLet on binding)
  | LocalDef attributes header body =>
    let attributes' := traverseAttributes on attributes
    let header' := traverseHeader on header
    LocalDef attributes' header' (traverseDefBody on body)
  | ExprStatement value => ExprStatement (value.traverse on)

def traverseLet (on: Steps) (input: Let): {Fail} Let := match input with
  | { keyword, pattern, annotation, colonEq, value } =>
    let pattern' := pattern.traverse on
    let annotation' := traverseAfter on annotation
    let value' := value.traverse on
    { keyword, pattern = pattern', annotation = annotation', colonEq, value = value' }

def traverseClauses (on: Steps) (input: List HandlerClause): {Fail} List HandlerClause := match input with
  | [] => []
  | [ReturnClause bar keyword name arrow body, ..rest] =>
    let body' := body.traverse on
    [ReturnClause bar keyword name arrow body', ..traverseClauses on rest]
  | [OperationClause bar operation argument comma continuation arrow body, ..rest] =>
    let argument' := argument.traverse on
    let body' := body.traverse on
    [OperationClause bar operation argument' comma continuation arrow body', ..traverseClauses on rest]

def traverseInductArms (on: Steps) (input: List InductArm): {Fail} List InductArm := match input with
  | [] => []
  | [{ bar, case, names, arrow, body }, ..rest] =>
    let body' := body.traverse on
    [{ bar, case, names, arrow, body = body' }, ..traverseInductArms on rest]

def traverseSteps (on: Steps) (input: List CalcStep): {Fail} List CalcStep := match input with
  | [] => []
  | [{ underscore, relation, operand, proof }, ..rest] =>
    let operand' := operand.traverse on
    let proof' := traverseAfter on proof
    [{ underscore, relation, operand = operand', proof = proof' }, ..traverseSteps on rest]

def traverseRules (on: Steps) (input: Rules): {Fail} Rules := match input with
  | RuleList rules => RuleList (traverseRuleList on rules)
  | Repeatedly word set => Repeatedly word (traverseRuleSet on set)

def traverseRuleSet (on: Steps) (input: RuleSet): {Fail} RuleSet := match input with
  | { open, rules, trailingComma, close } =>
    let rules' := traverseRuleList on rules
    on.ruleSet { open, rules = rules', trailingComma, close }

def traverseRuleList (on: Steps) (input: List RewriteRule): {Fail} List RewriteRule := match input with
  | [] => []
  | [{ reverse, rule }, ..rest] =>
    let rule' := rule.traverse on
    [{ reverse, rule = rule' }, ..traverseRuleList on rest]

def traverseRow (on: Steps) (input: Row): {Fail} Row := match input with
  | { open, abilities, variable, close } =>
    let abilities': List Expr := traverseExprs on abilities
    { open, abilities = abilities', variable, close }

def traverseExprs (on: Steps) (input: List Expr): {Fail} List Expr := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := first.traverse on
    [first', ..traverseExprs on rest]

def traverseLinks (on: Steps) (input: List (Word, Expr)): {Fail} List (Word, Expr) := match input with
  | [] => []
  | [(operator, operand), ..rest] =>
    let operand' := operand.traverse on
    [(operator, operand'), ..traverseLinks on rest]

def traversePieces (on: Steps) (input: List Piece): {Fail} List Piece := match input with
  | [] => []
  | [TextPiece word, ..rest] => [TextPiece word, ..traversePieces on rest]
  | [Interpolation open value close, ..rest] =>
    let value' := value.traverse on
    [Interpolation open value' close, ..traversePieces on rest]

def traverseScrutinees (on: Steps) (input: List Scrutinee): {Fail} List Scrutinee := match input with
  | [] => []
  | [{ name, value }, ..rest] =>
    let value' := value.traverse on
    [{ name, value = value' }, ..traverseScrutinees on rest]

def traverseArms (on: Steps) (input: List Arm): {Fail} List Arm := match input with
  | [] => []
  | [{ bar, patterns, guard, body }, ..rest] =>
    let patterns' := traversePatterns on patterns
    let guard' := traverseGuard on guard
    let body' := traverseAfter on body
    [{ bar, patterns = patterns', guard = guard', body = body' }, ..traverseArms on rest]

def traverseParams (on: Steps) (input: List Param): {Fail} List Param := match input with
  | [] => []
  | [NameParam word, ..rest] => [NameParam word, ..traverseParams on rest]
  | [PatternParam pattern, ..rest] =>
    let pattern' := pattern.traverse on
    [PatternParam pattern', ..traverseParams on rest]
  | [Grouped group, ..rest] =>
    let group' := group.traverse on
    [Grouped group', ..traverseParams on rest]
  | [TypedPattern open pattern colon annotation close, ..rest] =>
    let pattern' := pattern.traverse on
    let annotation' := annotation.traverse on
    [TypedPattern open pattern' colon annotation' close, ..traverseParams on rest]

def Group.traverse (group: Group) (on: Steps): {Fail} Group := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
    let attributes' := traverseAttributes on attributes
    let annotation' := traverseOptional on annotation
    let default' := traverseAfter on default
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

def Pattern.traverse (pattern: Pattern) (on: Steps): {Fail} Pattern :=
  let rebuilt := match pattern with
    | PatternWord kind word => PatternWord kind word
    | PatternCtor name arguments => PatternCtor name (traversePatterns on arguments)
    | PatternCtorFields name fields => PatternCtorFields name (traverseFields on fields)
    | PatternRecord fields => PatternRecord (traverseFields on fields)
    | PatternTuple open items trailingComma close => PatternTuple open (traversePatterns on items) trailingComma close
    | PatternList open items trailingComma tail close =>
      let items' := traversePatterns on items
      let tail' := traverseTail on tail
      PatternList open items' trailingComma tail' close
    | PatternNamed open name colonEq value close => PatternNamed open name colonEq (value.traverse on) close
    | PatternOr first rest =>
      let first' := first.traverse on
      PatternOr first' (traversePatternLinks on rest)
    | PatternParen open inner close => PatternParen open (inner.traverse on) close
    | PatternNegative minus number => PatternNegative minus number
    | PatternAbsurd open close => PatternAbsurd open close
    | PatternAppend start operator rest =>
      let start' := start.traverse on
      PatternAppend start' operator (rest.traverse on)
  on.pattern rebuilt

def traversePatterns (on: Steps) (input: List Pattern): {Fail} List Pattern := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := first.traverse on
    [first', ..traversePatterns on rest]

def traversePatternLinks (on: Steps) (input: List (Word, Pattern)): {Fail} List (Word, Pattern) := match input with
  | [] => []
  | [(bar, alternative), ..rest] =>
    let alternative' := alternative.traverse on
    [(bar, alternative'), ..traversePatternLinks on rest]

def traverseFields (on: Steps) (input: FieldsPattern): {Fail} FieldsPattern := match input with
  | { open, fields, trailingComma, rest, close } =>
    let fields' := traverseFieldPatterns on fields
    { open, fields = fields', trailingComma, rest, close }

def traverseFieldPatterns (on: Steps) (input: List FieldPattern): {Fail} List FieldPattern := match input with
  | [] => []
  | [{ name, value = Some (equals, pattern) }, ..rest] =>
    let pattern' := pattern.traverse on
    [{ name, value = Some (equals, pattern') }, ..traverseFieldPatterns on rest]
  | [{ name, value = None }, ..rest] => [{ name, value = None }, ..traverseFieldPatterns on rest]

--| A declaration with every expression and pattern in it traversed.
def Decl.traverse (decl: Decl) (on: Steps): {Fail} Decl :=
  let ex := (expr: Expr) => expr.traverse on
  let groups := (list: List Group) => traverseGroups on list
  let rebuilt := match decl with
    | Namespace keyword name => Namespace keyword name
    | Import keyword path open imported close => Import keyword path open imported close
    | Definition attributes header body =>
      let attributes' := traverseAttributes on attributes
      let header' := traverseHeader on header
      Definition attributes' header' (traverseDefBody on body)
    | Data attributes isInterface keyword name params indices body =>
      let attributes' := traverseAttributes on attributes
      let params' := groups params
      let indices' := match indices with
        | Some { colon, steps, last } =>
          let steps' := traverseIndices on steps
          Some { colon, steps = steps', last = ex last }
        | None => None
      let body' := match body with
        | Abstract => Abstract
        | Synonym equals annotation => Synonym equals (ex annotation)
        | RecordBody equals fields => RecordBody equals (fields.traverse on)
        | Sum equals constructors => Sum equals (traverseConstructors on constructors)
      Data attributes' isInterface keyword name params' indices' body'
    | Ability keyword name params whereKeyword operations =>
      let params' := groups params
      Ability keyword name params' whereKeyword (traverseOperations on operations)
    | Test keyword name colonEq body => Test keyword name colonEq (ex body)
    | RuleSetDecl keyword name colonEq set => RuleSetDecl keyword name colonEq (traverseRuleSet on set)
  on.decl rebuilt

def traverseHeader (on: Steps) (input: Header): {Fail} Header := match input with
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
    let params' := traverseGroups on params
    let result' := result.traverse on
    let decreasing' := traverseAfter on decreasingClause
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

def traverseDefBody (on: Steps) (input: DefBody): {Fail} DefBody := match input with
  | Primitive => Primitive
  | Assigned colonEq value =>
    let value' := value.traverse on
    Assigned colonEq value'
  | Arms arms => Arms (traverseArms on arms)

def traverseGroups (on: Steps) (input: List Group): {Fail} List Group := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := first.traverse on
    [first', ..traverseGroups on rest]

def traverseIndices (on: Steps) (input: List (Index, Word)): {Fail} List (Index, Word) := match input with
  | [] => []
  | [(IndexBinder binder, arrow), ..rest] =>
    let binder' := binder.traverse on
    [(IndexBinder binder', arrow), ..traverseIndices on rest]
  | [(IndexType annotation, arrow), ..rest] =>
    let annotation' := annotation.traverse on
    [(IndexType annotation', arrow), ..traverseIndices on rest]

def Fields.traverse (fields: Fields) (on: Steps): {Fail} Fields := match fields with
  | { open, fields, trailingComma, close } =>
    let fields' := traverseFieldList on fields
    on.fields { open, fields = fields', trailingComma, close }

def traverseFieldList (on: Steps) (input: List Field): {Fail} List Field := match input with
  | [] => []
  | [{ attributes, name, colon, annotation, default }, ..rest] =>
    let attributes' := traverseAttributes on attributes
    let annotation' := annotation.traverse on
    let default' := traverseAfter on default
    [
      { attributes = attributes', name, colon, annotation = annotation', default = default' },
      ..traverseFieldList on rest
    ]

def traverseConstructors (on: Steps) (input: List Constructor): {Fail} List Constructor := match input with
  | [] => []
  | [{ bar, attributes, name, fields, result }, ..rest] =>
    let attributes' := traverseAttributes on attributes
    let fields' := traverseParts on fields
    let result' := traverseAfter on result
    [{ bar, attributes = attributes', name, fields = fields', result = result' }, ..traverseConstructors on rest]

def traverseParts (on: Steps) (input: List ConstructorPart): {Fail} List ConstructorPart := match input with
  | [] => []
  | [PartGroup group, ..rest] =>
    let group' := group.traverse on
    [PartGroup group', ..traverseParts on rest]
  | [PartFields fields, ..rest] =>
    let fields' := fields.traverse on
    [PartFields fields', ..traverseParts on rest]

def traverseOperations (on: Steps) (input: List Operation): {Fail} List Operation := match input with
  | [] => []
  | [{ name, colon, annotation }, ..rest] =>
    let annotation' := annotation.traverse on
    [{ name, colon, annotation = annotation' }, ..traverseOperations on rest]

def traverseAttributes (on: Steps) (input: List Attributes): {Fail} List Attributes := match input with
  | [] => []
  | [first, ..rest] =>
    let first' := on.attributes first
    [first', ..traverseAttributes on rest]

-- Optional parts, each traversed by a function of its own: a `match` with
-- a step in it, as the value of a `let`, isn't accepted in a function
-- whose abilities are a row variable.

def traverseOptional (on: Steps) (input: Option Expr): {Fail} Option Expr := match input with
  | Some value =>
    let value' := value.traverse on
    Some value'
  | None => None

--| A part after a token: a default after `:=`, a body after `=>`.
def traverseAfter (on: Steps) (input: Option (k, Expr)): {Fail} Option (k, Expr) := match input with
  | Some (word, value) =>
    let value' := value.traverse on
    Some (word, value')
  | None => None

def traverseGuard (on: Steps) (input: Option Guard): {Fail} Option Guard := match input with
  | Some { keyword, binder, condition } =>
    let condition' := condition.traverse on
    Some { keyword, binder, condition = condition' }
  | None => None

def traverseTail (on: Steps) (input: Option (Word, Pattern)): {Fail} Option (Word, Pattern) := match input with
  | Some (dots, rest) =>
    let rest' := rest.traverse on
    Some (dots, rest')
  | None => None

--| A record update's base, before its `|`.
def traverseBefore (on: Steps) (input: Option (Expr, k)): {Fail} Option (Expr, k) := match input with
  | Some (value, word) =>
    let value' := value.traverse on
    Some (value', word)
  | None => None
