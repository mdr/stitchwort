--| The tree's traversal (tools/fmt-sketch/SKETCH.md §1, the traversal
--| item): one function per family that rebuilds a node from its traversed
--| children, left to right, then applies a step to it. `onExpr` is the
--| step for expressions and `onPattern` for patterns; every other family
--| is rebuilt as it was. The steps may `Fail`: the lowering's checks do,
--| and a pass that rewrites never does. (Generic in the steps' abilities,
--| `{e}`, the mutually recursive functions here are refused with
--| E-NOT-A-FUNCTION at the first call from one to another inside a `let`.)

namespace Syntax
import Std (Fail, List, Option)

def Expr.traverse (expr: Expr) (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern): {Fail} Expr :=
  let rebuilt := match expr with
    | Atom kind word => Atom kind word
    | Paren open inner close => Paren open (inner.traverse onExpr onPattern) close
    | Unit open close => Unit open close
    | Universe keyword level => Universe keyword level
    | Include keyword path => Include keyword path
    | Tuple open items trailingComma close => Tuple open (traverseExprs onExpr onPattern items) trailingComma close
    | ListOf open items trailingComma close => ListOf open (traverseExprs onExpr onPattern items) trailingComma close
    | Spread dots list => Spread dots (list.traverse onExpr onPattern)
    | Record open base fields trailingComma close =>
      let based := traverseBefore onExpr onPattern base
      Record open based (traverseExprs onExpr onPattern fields) trailingComma close
    | RecordField name equals value => RecordField name equals (value.traverse onExpr onPattern)
    | CtorFields ctor record =>
      let ctor' := ctor.traverse onExpr onPattern
      CtorFields ctor' (record.traverse onExpr onPattern)
    | App head arguments =>
      let head' := head.traverse onExpr onPattern
      App head' (traverseExprs onExpr onPattern arguments)
    | NamedArg open name colonEq value close => NamedArg open name colonEq (value.traverse onExpr onPattern) close
    | FieldAccess target dot field =>
      let target' := traverseOptional onExpr onPattern target
      FieldAccess target' dot field
    | Section body => Section (body.traverse onExpr onPattern)
    | OperatorSection open left operator right close =>
      let left' := traverseOptional onExpr onPattern left
      let right' := traverseOptional onExpr onPattern right
      OperatorSection open left' operator right' close
    | Infix kind left operator right =>
      let left' := left.traverse onExpr onPattern
      Infix kind left' operator (right.traverse onExpr onPattern)
    | Chain first rest =>
      let first' := first.traverse onExpr onPattern
      Chain first' (traverseLinks onExpr onPattern rest)
    | Prefix operator operand => Prefix operator (operand.traverse onExpr onPattern)
    | Binding kind keyword params arrow body =>
      let params' := traverseParams onExpr onPattern params
      Binding kind keyword params' arrow (body.traverse onExpr onPattern)
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      let condition' := condition.traverse onExpr onPattern
      let whenTrue' := whenTrue.traverse onExpr onPattern
      If keyword binder condition' thenKeyword whenTrue' elseKeyword (whenFalse.traverse onExpr onPattern)
    | Annotation open value colon annotation close =>
      let value' := value.traverse onExpr onPattern
      Annotation open value' colon (annotation.traverse onExpr onPattern) close
    | Interpolated pieces => Interpolated (traversePieces onExpr onPattern pieces)
    | Match keyword scrutinees withKeyword arms =>
      let scrutinees' := traverseScrutinees onExpr onPattern scrutinees
      Match keyword scrutinees' withKeyword (traverseArms onExpr onPattern arms)
    | ClauseLambda keyword word arms => ClauseLambda keyword word (traverseArms onExpr onPattern arms)
    | Facts kind keyword facts => Facts kind keyword (facts.traverse onExpr onPattern)
    | FunctionType binder arrow result =>
      let binder' := binder.traverse onExpr onPattern
      FunctionType binder' arrow (result.traverse onExpr onPattern)
    | Effect row result =>
      let row' := traverseRow onExpr onPattern row
      Effect row' (result.traverse onExpr onPattern)
  onExpr rebuilt

def traverseRow (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: Row): {Fail} Row :=
  match input with
    | { open, abilities, variable, close } =>
      let abilities': List Expr := traverseExprs onExpr onPattern abilities
      { open, abilities = abilities', variable, close }

def traverseExprs (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Expr):
    {Fail} List Expr :=
  match input with
    | [] => []
    | [first, ..rest] =>
      let first' := first.traverse onExpr onPattern
      [first', ..traverseExprs onExpr onPattern rest]

def traverseLinks (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List (Word, Expr)):
    {Fail} List (Word, Expr) :=
  match input with
    | [] => []
    | [(operator, operand), ..rest] =>
      let operand' := operand.traverse onExpr onPattern
      [(operator, operand'), ..traverseLinks onExpr onPattern rest]

def traversePieces (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Piece):
    {Fail} List Piece :=
  match input with
    | [] => []
    | [TextPiece word, ..rest] => [TextPiece word, ..traversePieces onExpr onPattern rest]
    | [Interpolation open value close, ..rest] =>
      let value' := value.traverse onExpr onPattern
      [Interpolation open value' close, ..traversePieces onExpr onPattern rest]

def traverseScrutinees (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Scrutinee):
    {Fail} List Scrutinee :=
  match input with
    | [] => []
    | [{ name, value }, ..rest] =>
      let value' := value.traverse onExpr onPattern
      [{ name, value = value' }, ..traverseScrutinees onExpr onPattern rest]

def traverseArms (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Arm):
    {Fail} List Arm :=
  match input with
    | [] => []
    | [{ bar, patterns, guard, body }, ..rest] =>
      let patterns' := traversePatterns onPattern patterns
      let guard' := traverseGuard onExpr onPattern guard
      let body' := traverseAfter onExpr onPattern body
      [{ bar, patterns = patterns', guard = guard', body = body' }, ..traverseArms onExpr onPattern rest]

def traverseParams (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Param):
    {Fail} List Param :=
  match input with
    | [] => []
    | [NameParam word, ..rest] => [NameParam word, ..traverseParams onExpr onPattern rest]
    | [PatternParam pattern, ..rest] =>
      let pattern' := pattern.traverse onPattern
      [PatternParam pattern', ..traverseParams onExpr onPattern rest]
    | [Grouped group, ..rest] =>
      let group' := group.traverse onExpr onPattern
      [Grouped group', ..traverseParams onExpr onPattern rest]
    | [TypedPattern open pattern colon annotation close, ..rest] =>
      let pattern' := pattern.traverse onPattern
      let annotation' := annotation.traverse onExpr onPattern
      [TypedPattern open pattern' colon annotation' close, ..traverseParams onExpr onPattern rest]

def Group.traverse (group: Group) (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern): {Fail} Group :=
  match group with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close } =>
      let annotation' := traverseOptional onExpr onPattern annotation
      let default' := traverseAfter onExpr onPattern default
      { kind, implicit, open, attributes, auto, names, colon, annotation = annotation', default = default', close }

def Pattern.traverse (pattern: Pattern) (onPattern: Pattern → {Fail} Pattern): {Fail} Pattern :=
  let rebuilt := match pattern with
    | PatternWord kind word => PatternWord kind word
    | PatternCtor name arguments => PatternCtor name (traversePatterns onPattern arguments)
    | PatternCtorFields name fields => PatternCtorFields name (traverseFields onPattern fields)
    | PatternRecord fields => PatternRecord (traverseFields onPattern fields)
    | PatternTuple open items trailingComma close =>
      PatternTuple open (traversePatterns onPattern items) trailingComma close
    | PatternList open items trailingComma tail close =>
      let items' := traversePatterns onPattern items
      let tail' := traverseTail onPattern tail
      PatternList open items' trailingComma tail' close
    | PatternNamed open name colonEq value close => PatternNamed open name colonEq (value.traverse onPattern) close
    | PatternOr first rest =>
      let first' := first.traverse onPattern
      PatternOr first' (traversePatternLinks onPattern rest)
    | PatternParen open inner close => PatternParen open (inner.traverse onPattern) close
    | PatternNegative minus number => PatternNegative minus number
    | PatternAbsurd open close => PatternAbsurd open close
    | PatternAppend start operator rest =>
      let start' := start.traverse onPattern
      PatternAppend start' operator (rest.traverse onPattern)
  onPattern rebuilt

def traversePatterns (onPattern: Pattern → {Fail} Pattern) (input: List Pattern): {Fail} List Pattern :=
  match input with
    | [] => []
    | [first, ..rest] =>
      let first' := first.traverse onPattern
      [first', ..traversePatterns onPattern rest]

def traversePatternLinks (onPattern: Pattern → {Fail} Pattern) (input: List (Word, Pattern)):
    {Fail} List (Word, Pattern) :=
  match input with
    | [] => []
    | [(bar, alternative), ..rest] =>
      let alternative' := alternative.traverse onPattern
      [(bar, alternative'), ..traversePatternLinks onPattern rest]

def traverseFields (onPattern: Pattern → {Fail} Pattern) (input: FieldsPattern): {Fail} FieldsPattern :=
  match input with
    | { open, fields, trailingComma, rest, close } =>
      let fields' := traverseFieldPatterns onPattern fields
      { open, fields = fields', trailingComma, rest, close }

def traverseFieldPatterns (onPattern: Pattern → {Fail} Pattern) (input: List FieldPattern): {Fail} List FieldPattern :=
  match input with
    | [] => []
    | [{ name, value = Some (equals, pattern) }, ..rest] =>
      let pattern' := pattern.traverse onPattern
      [{ name, value = Some (equals, pattern') }, ..traverseFieldPatterns onPattern rest]
    | [{ name, value = None }, ..rest] => [{ name, value = None }, ..traverseFieldPatterns onPattern rest]

--| A declaration with every expression and pattern in it traversed.
def Decl.traverse (decl: Decl) (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern): {Fail} Decl :=
  let ex := (expr: Expr) => expr.traverse onExpr onPattern
  let groups := (list: List Group) => traverseGroups onExpr onPattern list
  match decl with
    | Namespace keyword name => Namespace keyword name
    | Import keyword path open imported close => Import keyword path open imported close
    | Definition attributes header body =>
      let header' := match header with
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
          let params' := groups params
          let result' := ex result
          let decreasing' := traverseAfter onExpr onPattern decreasingClause
          {
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
      let body' := match body with
        | Primitive => Primitive
        | Assigned colonEq value => Assigned colonEq (ex value)
        | Arms arms => Arms (traverseArms onExpr onPattern arms)
      Definition attributes header' body'
    | Data attributes isInterface keyword name params indices body =>
      let params' := groups params
      let indices' := match indices with
        | Some { colon, steps, last } =>
          let steps' := traverseIndices onExpr onPattern steps
          Some { colon, steps = steps', last = ex last }
        | None => None
      let body' := match body with
        | Abstract => Abstract
        | Synonym equals annotation => Synonym equals (ex annotation)
        | RecordBody equals fields => RecordBody equals (fields.traverse onExpr onPattern)
        | Sum equals constructors => Sum equals (traverseConstructors onExpr onPattern constructors)
      Data attributes isInterface keyword name params' indices' body'
    | Ability keyword name params whereKeyword operations =>
      let params' := groups params
      Ability keyword name params' whereKeyword (traverseOperations onExpr onPattern operations)
    | Test keyword name colonEq body => Test keyword name colonEq (ex body)

def traverseGroups (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Group):
    {Fail} List Group :=
  match input with
    | [] => []
    | [first, ..rest] =>
      let first' := first.traverse onExpr onPattern
      [first', ..traverseGroups onExpr onPattern rest]

def traverseIndices (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List (Index, Word)):
    {Fail} List (Index, Word) :=
  match input with
    | [] => []
    | [(IndexBinder binder, arrow), ..rest] =>
      let binder' := binder.traverse onExpr onPattern
      [(IndexBinder binder', arrow), ..traverseIndices onExpr onPattern rest]
    | [(IndexType annotation, arrow), ..rest] =>
      let annotation' := annotation.traverse onExpr onPattern
      [(IndexType annotation', arrow), ..traverseIndices onExpr onPattern rest]

def Fields.traverse (fields: Fields) (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern):
    {Fail} Fields :=
  match fields with
    | { open, fields, trailingComma, close } =>
      let fields' := traverseFieldList onExpr onPattern fields
      { open, fields = fields', trailingComma, close }

def traverseFieldList (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Field):
    {Fail} List Field :=
  match input with
    | [] => []
    | [{ attributes, name, colon, annotation, default }, ..rest] =>
      let annotation' := annotation.traverse onExpr onPattern
      let default' := traverseAfter onExpr onPattern default
      [
        { attributes, name, colon, annotation = annotation', default = default' },
        ..traverseFieldList onExpr onPattern rest
      ]

def traverseConstructors (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Constructor):
    {Fail} List Constructor :=
  match input with
    | [] => []
    | [{ bar, attributes, name, fields, result }, ..rest] =>
      let fields' := traverseParts onExpr onPattern fields
      let result' := traverseAfter onExpr onPattern result
      [{ bar, attributes, name, fields = fields', result = result' }, ..traverseConstructors onExpr onPattern rest]

def traverseParts (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List ConstructorPart):
    {Fail} List ConstructorPart :=
  match input with
    | [] => []
    | [PartGroup group, ..rest] =>
      let group' := group.traverse onExpr onPattern
      [PartGroup group', ..traverseParts onExpr onPattern rest]
    | [PartFields fields, ..rest] =>
      let fields' := fields.traverse onExpr onPattern
      [PartFields fields', ..traverseParts onExpr onPattern rest]

def traverseOperations (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: List Operation):
    {Fail} List Operation :=
  match input with
    | [] => []
    | [{ name, colon, annotation }, ..rest] =>
      let annotation' := annotation.traverse onExpr onPattern
      [{ name, colon, annotation = annotation' }, ..traverseOperations onExpr onPattern rest]

-- Optional parts, each traversed by a function of its own: a `match` with
-- a step in it, as the value of a `let`, isn't accepted in a function
-- whose abilities are a row variable.

def traverseOptional (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: Option Expr):
    {Fail} Option Expr :=
  match input with
    | Some value =>
      let value' := value.traverse onExpr onPattern
      Some value'
    | None => None

--| A part after a token: a default after `:=`, a body after `=>`.
def traverseAfter (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: Option (k, Expr)):
    {Fail} Option (k, Expr) :=
  match input with
    | Some (word, value) =>
      let value' := value.traverse onExpr onPattern
      Some (word, value')
    | None => None

def traverseGuard (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: Option Guard):
    {Fail} Option Guard :=
  match input with
    | Some { keyword, binder, condition } =>
      let condition' := condition.traverse onExpr onPattern
      Some { keyword, binder, condition = condition' }
    | None => None

def traverseTail (onPattern: Pattern → {Fail} Pattern) (input: Option (Word, Pattern)): {Fail} Option (Word, Pattern) :=
  match input with
    | Some (dots, rest) =>
      let rest' := rest.traverse onPattern
      Some (dots, rest')
    | None => None

--| A record update's base, before its `|`.
def traverseBefore (onExpr: Expr → {Fail} Expr) (onPattern: Pattern → {Fail} Pattern) (input: Option (Expr, k)):
    {Fail} Option (Expr, k) :=
  match input with
    | Some (value, word) =>
      let value' := value.traverse onExpr onPattern
      Some (value', word)
    | None => None
