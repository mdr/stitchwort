--| A pure copy of the traversal (`Syntax/Traverse.sw`), with steps that
--| can't fail, and the facts that make it a stand-in for the real one.
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
    | Cases keyword thenKeyword body => Cases keyword thenKeyword (body.walk on)
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
    [
      { attributes = attributes', name, colon, annotation = annotation', default = default' },
      ..walkFieldList on rest
    ]

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
-- results and then a step: the shapes the traversal's arms elaborate to.

theorem seq1 ∀ (t1: () → {Fail} a1) (g: a1 → r) (v1: a1)
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => g (t1 ())) = Ok (g v1) :=
  rewrite Fail.toResultThen t1 (x => g x), h1

theorem seq1k ∀ (t1: () → {Fail} a1) (g: a1 → r) (k: r → {Fail} q) (v1: a1)
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => k (g (t1 ()))) = Fail.toResult (() => k (g v1)) :=
  rewrite Fail.toResultThen (() => g (t1 ())) k, seq1 t1 g v1 h1

theorem seq2 ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (g: a1 → a2 → r) (v1: a1) (v2: a2)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => g (t1 ()) (t2 ())) = Ok (g v1 v2) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ())), h1, seq1 t2 (g v1) v2 h2

theorem seq2k ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (g: a1 → a2 → r) (k: r → {Fail} q) (v1: a1) (v2: a2)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => k (g (t1 ()) (t2 ()))) = Fail.toResult (() => k (g v1 v2)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ())) k, seq2 t1 t2 g v1 v2 h1 h2

theorem seq3 ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (g: a1 → a2 → a3 → r) (v1: a1) (v2: a2) (v3: a3)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2) (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ())) = Ok (g v1 v2 v3) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ()) (t3 ())), h1, seq2 t2 t3 (g v1) v2 v3 h2 h3

theorem seq3k ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (g: a1 → a2 → a3 → r) (k: r → {Fail} q) (v1: a1) (v2: a2) (v3: a3)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2) (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()))) = Fail.toResult (() => k (g v1 v2 v3)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ())) k, seq3 t1 t2 t3 g v1 v2 v3 h1 h2 h3

theorem seq4 ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (t4: () → {Fail} a4) (g: a1 → a2 → a3 → a4 → r) (v1: a1) (v2: a2) (v3: a3) (v4: a4)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2) (h3: Fail.toResult t3 = Ok v3) (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) = Ok (g v1 v2 v3 v4) :=
  rewrite Fail.toResultThen t1 (x => g x (t2 ()) (t3 ()) (t4 ())), h1, seq3 t2 t3 t4 (g v1) v2 v3 v4 h2 h3 h4

theorem seq4k ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (t4: () → {Fail} a4) (g: a1 → a2 → a3 → a4 → r) (k: r → {Fail} q) (v1: a1) (v2: a2) (v3: a3) (v4: a4)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2) (h3: Fail.toResult t3 = Ok v3) (h4: Fail.toResult t4 = Ok v4):
    Fail.toResult (() => k (g (t1 ()) (t2 ()) (t3 ()) (t4 ()))) = Fail.toResult (() => k (g v1 v2 v3 v4)) :=
  rewrite Fail.toResultThen (() => g (t1 ()) (t2 ()) (t3 ()) (t4 ())) k, seq4 t1 t2 t3 t4 g v1 v2 v3 v4 h1 h2 h3 h4

theorem seq1j ∀ (t1: () → {Fail} a1) (g: a1 → r) (k: r → {Fail} q) (v1: a1)
    (h1: Fail.toResult t1 = Ok v1):
    Fail.toResult (() => (let x1 := t1 (); k (g x1))) = Fail.toResult (() => k (g v1)) :=
  rewrite Fail.toResultThen t1 (x => k (g x)), h1

theorem seq2j ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (g: a1 → a2 → r) (k: r → {Fail} q) (v1: a1) (v2: a2)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2):
    Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); k (g x1 x2))) = Fail.toResult (() => k (g v1 v2)) :=
  rewrite Fail.toResultThen t1 (x => (let x2 := t2 (); k (g x x2))), h1, seq1j t2 (g v1) k v2 h2

theorem seq3j ∀ (t1: () → {Fail} a1) (t2: () → {Fail} a2) (t3: () → {Fail} a3) (g: a1 → a2 → a3 → r) (k: r → {Fail} q) (v1: a1) (v2: a2) (v3: a3)
    (h1: Fail.toResult t1 = Ok v1) (h2: Fail.toResult t2 = Ok v2) (h3: Fail.toResult t3 = Ok v3):
    Fail.toResult (() => (let x1 := t1 (); let x2 := t2 (); let x3 := t3 (); k (g x1 x2 x3))) = Fail.toResult (() => k (g v1 v2 v3)) :=
  rewrite Fail.toResultThen t1 (x => (let x2 := t2 (); let x3 := t3 (); k (g x x2 x3))), h1, seq2j t2 t3 (g v1) k v2 v3 h2 h3

def runExpr (on: Steps) (input: Expr): Result (Expr) Text := Fail.toResult (() => input.traverse on)

def runStatements (on: Steps) (input: List Statement): Result (List Statement) Text := Fail.toResult (() => traverseStatements on input)

def runStatement (on: Steps) (input: Statement): Result (Statement) Text := Fail.toResult (() => traverseStatement on input)

def runLet (on: Steps) (input: Let): Result (Let) Text := Fail.toResult (() => traverseLet on input)

def runClauses (on: Steps) (input: List HandlerClause): Result (List HandlerClause) Text := Fail.toResult (() => traverseClauses on input)

def runInductArms (on: Steps) (input: List InductArm): Result (List InductArm) Text := Fail.toResult (() => traverseInductArms on input)

def runCalcSteps (on: Steps) (input: List CalcStep): Result (List CalcStep) Text := Fail.toResult (() => traverseSteps on input)

def runRules (on: Steps) (input: Rules): Result (Rules) Text := Fail.toResult (() => traverseRules on input)

def runRuleSet (on: Steps) (input: RuleSet): Result (RuleSet) Text := Fail.toResult (() => traverseRuleSet on input)

def runRuleList (on: Steps) (input: List RewriteRule): Result (List RewriteRule) Text := Fail.toResult (() => traverseRuleList on input)

def runRow (on: Steps) (input: Row): Result (Row) Text := Fail.toResult (() => traverseRow on input)

def runExprs (on: Steps) (input: List Expr): Result (List Expr) Text := Fail.toResult (() => traverseExprs on input)

def runLinks (on: Steps) (input: List (Word, Expr)): Result (List (Word, Expr)) Text := Fail.toResult (() => traverseLinks on input)

def runPieces (on: Steps) (input: List Piece): Result (List Piece) Text := Fail.toResult (() => traversePieces on input)

def runScrutinees (on: Steps) (input: List Scrutinee): Result (List Scrutinee) Text := Fail.toResult (() => traverseScrutinees on input)

def runArms (on: Steps) (input: List Arm): Result (List Arm) Text := Fail.toResult (() => traverseArms on input)

def runParams (on: Steps) (input: List Param): Result (List Param) Text := Fail.toResult (() => traverseParams on input)

def runGroup (on: Steps) (input: Group): Result (Group) Text := Fail.toResult (() => input.traverse on)

def runPattern (on: Steps) (input: Pattern): Result (Pattern) Text := Fail.toResult (() => input.traverse on)

def runPatterns (on: Steps) (input: List Pattern): Result (List Pattern) Text := Fail.toResult (() => traversePatterns on input)

def runPatternLinks (on: Steps) (input: List (Word, Pattern)): Result (List (Word, Pattern)) Text := Fail.toResult (() => traversePatternLinks on input)

def runFieldsPattern (on: Steps) (input: FieldsPattern): Result (FieldsPattern) Text := Fail.toResult (() => traverseFields on input)

def runFieldPatterns (on: Steps) (input: List FieldPattern): Result (List FieldPattern) Text := Fail.toResult (() => traverseFieldPatterns on input)

def runDecl (on: Steps) (input: Decl): Result (Decl) Text := Fail.toResult (() => input.traverse on)

def runHeader (on: Steps) (input: Header): Result (Header) Text := Fail.toResult (() => traverseHeader on input)

def runDefBody (on: Steps) (input: DefBody): Result (DefBody) Text := Fail.toResult (() => traverseDefBody on input)

def runGroups (on: Steps) (input: List Group): Result (List Group) Text := Fail.toResult (() => traverseGroups on input)

def runIndices (on: Steps) (input: List (Index, Word)): Result (List (Index, Word)) Text := Fail.toResult (() => traverseIndices on input)

def runFields (on: Steps) (input: Fields): Result (Fields) Text := Fail.toResult (() => input.traverse on)

def runFieldList (on: Steps) (input: List Field): Result (List Field) Text := Fail.toResult (() => traverseFieldList on input)

def runConstructors (on: Steps) (input: List Constructor): Result (List Constructor) Text := Fail.toResult (() => traverseConstructors on input)

def runParts (on: Steps) (input: List ConstructorPart): Result (List ConstructorPart) Text := Fail.toResult (() => traverseParts on input)

def runOperations (on: Steps) (input: List Operation): Result (List Operation) Text := Fail.toResult (() => traverseOperations on input)

def runAttributes (on: Steps) (input: List Attributes): Result (List Attributes) Text := Fail.toResult (() => traverseAttributes on input)

def runOptional (on: Steps) (input: Option Expr): Result (Option Expr) Text := Fail.toResult (() => traverseOptional on input)

def runAfter (on: Steps) (input: Option (k, Expr)): Result (Option (k, Expr)) Text := Fail.toResult (() => traverseAfter on input)

def runGuard (on: Steps) (input: Option Guard): Result (Option Guard) Text := Fail.toResult (() => traverseGuard on input)

def runTail (on: Steps) (input: Option (Word, Pattern)): Result (Option (Word, Pattern)) Text := Fail.toResult (() => traverseTail on input)

def runBefore (on: Steps) (input: Option (Expr, k)): Result (Option (Expr, k)) Text := Fail.toResult (() => traverseBefore on input)

theorem exprOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Expr):
    runExpr on input = Ok (input.walk p) :=
  match input with
    | Atom kind word => agree.expr (Atom kind word)
    | Paren open inner close => rewrite seq1k (() => inner.traverse on) (v1 => Paren open v1 close) on.expr (inner.walk p) (exprOk on p agree inner), agree.expr (Paren open (inner.walk p) close)
    | Unit open close => agree.expr (Unit open close)
    | Universe keyword level => agree.expr (Universe keyword level)
    | Include keyword path => agree.expr (Include keyword path)
    | Tuple open items trailingComma close => rewrite seq1k (() => traverseExprs on items) (v1 => Tuple open v1 trailingComma close) on.expr (walkExprs p items) (exprsOk on p agree items), agree.expr (Tuple open (walkExprs p items) trailingComma close)
    | ListOf open items trailingComma close => rewrite seq1k (() => traverseExprs on items) (v1 => ListOf open v1 trailingComma close) on.expr (walkExprs p items) (exprsOk on p agree items), agree.expr (ListOf open (walkExprs p items) trailingComma close)
    | Spread dots list => rewrite seq1k (() => list.traverse on) (v1 => Spread dots v1) on.expr (list.walk p) (exprOk on p agree list), agree.expr (Spread dots (list.walk p))
    | Record open base fields trailingComma close => rewrite seq2k (() => traverseBefore on base) (() => traverseExprs on fields) (v1 v2 => Record open v1 v2 trailingComma close) on.expr (walkBefore p base) (walkExprs p fields) (beforeOk on p agree base) (exprsOk on p agree fields), agree.expr (Record open (walkBefore p base) (walkExprs p fields) trailingComma close)
    | RecordField name equals value => rewrite seq1k (() => value.traverse on) (v1 => RecordField name equals v1) on.expr (value.walk p) (exprOk on p agree value), agree.expr (RecordField name equals (value.walk p))
    | CtorFields ctor record => rewrite seq2k (() => ctor.traverse on) (() => record.traverse on) (v1 v2 => CtorFields v1 v2) on.expr (ctor.walk p) (record.walk p) (exprOk on p agree ctor) (exprOk on p agree record), agree.expr (CtorFields (ctor.walk p) (record.walk p))
    | App head arguments => rewrite seq2k (() => head.traverse on) (() => traverseExprs on arguments) (v1 v2 => App v1 v2) on.expr (head.walk p) (walkExprs p arguments) (exprOk on p agree head) (exprsOk on p agree arguments), agree.expr (App (head.walk p) (walkExprs p arguments))
    | NamedArg open name colonEq value close => rewrite seq1k (() => value.traverse on) (v1 => NamedArg open name colonEq v1 close) on.expr (value.walk p) (exprOk on p agree value), agree.expr (NamedArg open name colonEq (value.walk p) close)
    | FieldAccess target dot field => rewrite seq1k (() => traverseOptional on target) (v1 => FieldAccess v1 dot field) on.expr (walkOptional p target) (optionalOk on p agree target), agree.expr (FieldAccess (walkOptional p target) dot field)
    | Section body => rewrite seq1k (() => body.traverse on) (v1 => Section v1) on.expr (body.walk p) (exprOk on p agree body), agree.expr (Section (body.walk p))
    | OperatorSection open left operator right close => rewrite seq2k (() => traverseOptional on left) (() => traverseOptional on right) (v1 v2 => OperatorSection open v1 operator v2 close) on.expr (walkOptional p left) (walkOptional p right) (optionalOk on p agree left) (optionalOk on p agree right), agree.expr (OperatorSection open (walkOptional p left) operator (walkOptional p right) close)
    | Infix kind left operator right => rewrite seq2k (() => left.traverse on) (() => right.traverse on) (v1 v2 => Infix kind v1 operator v2) on.expr (left.walk p) (right.walk p) (exprOk on p agree left) (exprOk on p agree right), agree.expr (Infix kind (left.walk p) operator (right.walk p))
    | Chain first rest => rewrite seq2k (() => first.traverse on) (() => traverseLinks on rest) (v1 v2 => Chain v1 v2) on.expr (first.walk p) (walkLinks p rest) (exprOk on p agree first) (linksOk on p agree rest), agree.expr (Chain (first.walk p) (walkLinks p rest))
    | Prefix operator operand => rewrite seq1k (() => operand.traverse on) (v1 => Prefix operator v1) on.expr (operand.walk p) (exprOk on p agree operand), agree.expr (Prefix operator (operand.walk p))
    | Binding kind keyword params arrow body => rewrite seq2k (() => traverseParams on params) (() => body.traverse on) (v1 v2 => Binding kind keyword v1 arrow v2) on.expr (walkParams p params) (body.walk p) (paramsOk on p agree params) (exprOk on p agree body), agree.expr (Binding kind keyword (walkParams p params) arrow (body.walk p))
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse => rewrite seq3k (() => condition.traverse on) (() => whenTrue.traverse on) (() => whenFalse.traverse on) (v1 v2 v3 => If keyword binder v1 thenKeyword v2 elseKeyword v3) on.expr (condition.walk p) (whenTrue.walk p) (whenFalse.walk p) (exprOk on p agree condition) (exprOk on p agree whenTrue) (exprOk on p agree whenFalse), agree.expr (If keyword binder (condition.walk p) thenKeyword (whenTrue.walk p) elseKeyword (whenFalse.walk p))
    | Annotation open value colon annotation close => rewrite seq2k (() => value.traverse on) (() => annotation.traverse on) (v1 v2 => Annotation open v1 colon v2 close) on.expr (value.walk p) (annotation.walk p) (exprOk on p agree value) (exprOk on p agree annotation), agree.expr (Annotation open (value.walk p) colon (annotation.walk p) close)
    | Interpolated pieces => rewrite seq1k (() => traversePieces on pieces) (v1 => Interpolated v1) on.expr (walkPieces p pieces) (piecesOk on p agree pieces), agree.expr (Interpolated (walkPieces p pieces))
    | Match keyword scrutinees withKeyword arms => rewrite seq2k (() => traverseScrutinees on scrutinees) (() => traverseArms on arms) (v1 v2 => Match keyword v1 withKeyword v2) on.expr (walkScrutinees p scrutinees) (walkArms p arms) (scrutineesOk on p agree scrutinees) (armsOk on p agree arms), agree.expr (Match keyword (walkScrutinees p scrutinees) withKeyword (walkArms p arms))
    | ClauseLambda keyword word arms => rewrite seq1k (() => traverseArms on arms) (v1 => ClauseLambda keyword word v1) on.expr (walkArms p arms) (armsOk on p agree arms), agree.expr (ClauseLambda keyword word (walkArms p arms))
    | Facts kind keyword facts => rewrite seq1k (() => facts.traverse on) (v1 => Facts kind keyword v1) on.expr (facts.walk p) (exprOk on p agree facts), agree.expr (Facts kind keyword (facts.walk p))
    | FunctionType binder arrow result => rewrite seq2k (() => binder.traverse on) (() => result.traverse on) (v1 v2 => FunctionType v1 arrow v2) on.expr (binder.walk p) (result.walk p) (groupOk on p agree binder) (exprOk on p agree result), agree.expr (FunctionType (binder.walk p) arrow (result.walk p))
    | Effect row result => rewrite seq2k (() => traverseRow on row) (() => result.traverse on) (v1 v2 => Effect v1 v2) on.expr (walkRow p row) (result.walk p) (rowOk on p agree row) (exprOk on p agree result), agree.expr (Effect (walkRow p row) (result.walk p))
    | Block first rest result => rewrite seq3k (() => traverseStatement on first) (() => traverseStatements on rest) (() => result.traverse on) (v1 v2 v3 => Block v1 v2 v3) on.expr (walkStatement p first) (walkStatements p rest) (result.walk p) (statementOk on p agree first) (statementsOk on p agree rest) (exprOk on p agree result), agree.expr (Block (walkStatement p first) (walkStatements p rest) (result.walk p))
    | LetIn binding semicolon body => rewrite seq2k (() => traverseLet on binding) (() => body.traverse on) (v1 v2 => LetIn v1 semicolon v2) on.expr (walkLet p binding) (body.walk p) (letOk on p agree binding) (exprOk on p agree body), agree.expr (LetIn (walkLet p binding) semicolon (body.walk p))
    | Handle keyword computation withKeyword clauses => rewrite seq2k (() => computation.traverse on) (() => traverseClauses on clauses) (v1 v2 => Handle keyword v1 withKeyword v2) on.expr (computation.walk p) (walkClauses p clauses) (exprOk on p agree computation) (clausesOk on p agree clauses), agree.expr (Handle keyword (computation.walk p) withKeyword (walkClauses p clauses))
    | Reify keyword reifyWord computation withKeyword clauses => rewrite seq2k (() => computation.traverse on) (() => traverseClauses on clauses) (v1 v2 => Reify keyword reifyWord v1 withKeyword v2) on.expr (computation.walk p) (walkClauses p clauses) (exprOk on p agree computation) (clausesOk on p agree clauses), agree.expr (Reify keyword reifyWord (computation.walk p) withKeyword (walkClauses p clauses))
    | Induct keyword inductWord call withKeyword arms => rewrite seq2k (() => call.traverse on) (() => traverseInductArms on arms) (v1 v2 => Induct keyword inductWord v1 withKeyword v2) on.expr (call.walk p) (walkInductArms p arms) (exprOk on p agree call) (inductArmsOk on p agree arms), agree.expr (Induct keyword inductWord (call.walk p) withKeyword (walkInductArms p arms))
    | Calc keyword first steps => rewrite seq2k (() => first.traverse on) (() => traverseSteps on steps) (v1 v2 => Calc keyword v1 v2) on.expr (first.walk p) (walkSteps p steps) (exprOk on p agree first) (calcStepsOk on p agree steps), agree.expr (Calc keyword (first.walk p) (walkSteps p steps))
    | Rewrite keyword rules target body => rewrite seq3k (() => traverseRules on rules) (() => traverseAfter on target) (() => traverseAfter on body) (v1 v2 v3 => Rewrite keyword v1 v2 v3) on.expr (walkRules p rules) (walkAfter p target) (walkAfter p body) (rulesOk on p agree rules) (afterOk on p agree target) (afterOk on p agree body), agree.expr (Rewrite keyword (walkRules p rules) (walkAfter p target) (walkAfter p body))
    | Cases keyword thenKeyword body => rewrite seq1k (() => body.traverse on) (v1 => Cases keyword thenKeyword v1) on.expr (body.walk p) (exprOk on p agree body), agree.expr (Cases keyword thenKeyword (body.walk p))

theorem statementsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Statement):
    runStatements on input = Ok (walkStatements p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => seq2 (() => traverseStatement on first) (() => traverseStatements on rest) (v1 v2 => [v1, ..v2]) (walkStatement p first) (walkStatements p rest) (statementOk on p agree first) (statementsOk on p agree rest)

theorem statementOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Statement):
    runStatement on input = Ok (walkStatement p input) :=
  match input with
    | LetStatement binding => seq1 (() => traverseLet on binding) (v1 => LetStatement v1) (walkLet p binding) (letOk on p agree binding)
    | LocalDef attributes header body => seq3 (() => traverseAttributes on attributes) (() => traverseHeader on header) (() => traverseDefBody on body) (v1 v2 v3 => LocalDef v1 v2 v3) (walkAttributes p attributes) (walkHeader p header) (walkDefBody p body) (attributesOk on p agree attributes) (headerOk on p agree header) (defBodyOk on p agree body)
    | ExprStatement value => seq1 (() => value.traverse on) (v1 => ExprStatement v1) (value.walk p) (exprOk on p agree value)

theorem letOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Let):
    runLet on input = Ok (walkLet p input) :=
  match input with
    | { keyword, pattern, annotation, colonEq, value } => seq3 (() => pattern.traverse on) (() => traverseAfter on annotation) (() => value.traverse on) (v1 v2 v3 => { keyword, pattern = v1, annotation = v2, colonEq, value = v3 }) (pattern.walk p) (walkAfter p annotation) (value.walk p) (patternOk on p agree pattern) (afterOk on p agree annotation) (exprOk on p agree value)

theorem clausesOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List HandlerClause):
    runClauses on input = Ok (walkClauses p input) :=
  match input with
    | [] => byComputing
    | [ReturnClause bar keyword name arrow body, ..rest] => seq2 (() => body.traverse on) (() => traverseClauses on rest) (v1 v2 => [ReturnClause bar keyword name arrow v1, ..v2]) (body.walk p) (walkClauses p rest) (exprOk on p agree body) (clausesOk on p agree rest)
    | [OperationClause bar operation argument comma continuation arrow body, ..rest] => seq3 (() => argument.traverse on) (() => body.traverse on) (() => traverseClauses on rest) (v1 v2 v3 => [OperationClause bar operation v1 comma continuation arrow v2, ..v3]) (argument.walk p) (body.walk p) (walkClauses p rest) (patternOk on p agree argument) (exprOk on p agree body) (clausesOk on p agree rest)

theorem inductArmsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List InductArm):
    runInductArms on input = Ok (walkInductArms p input) :=
  match input with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] => seq2 (() => body.traverse on) (() => traverseInductArms on rest) (v1 v2 => [{ bar, case, names, arrow, body = v1 }, ..v2]) (body.walk p) (walkInductArms p rest) (exprOk on p agree body) (inductArmsOk on p agree rest)

theorem calcStepsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List CalcStep):
    runCalcSteps on input = Ok (walkSteps p input) :=
  match input with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] => seq3 (() => operand.traverse on) (() => traverseAfter on proof) (() => traverseSteps on rest) (v1 v2 v3 => [{ underscore, relation, operand = v1, proof = v2 }, ..v3]) (operand.walk p) (walkAfter p proof) (walkSteps p rest) (exprOk on p agree operand) (afterOk on p agree proof) (calcStepsOk on p agree rest)

theorem rulesOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Rules):
    runRules on input = Ok (walkRules p input) :=
  match input with
    | RuleList rules => seq1 (() => traverseRuleList on rules) (v1 => RuleList v1) (walkRuleList p rules) (ruleListOk on p agree rules)
    | Repeatedly word set => seq1 (() => traverseRuleSet on set) (v1 => Repeatedly word v1) (walkRuleSet p set) (ruleSetOk on p agree set)

theorem ruleSetOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: RuleSet):
    runRuleSet on input = Ok (walkRuleSet p input) :=
  match input with
    | { open, rules, trailingComma, close } => rewrite seq1j (() => traverseRuleList on rules) (v1 => { open, rules = v1, trailingComma, close }) on.ruleSet (walkRuleList p rules) (ruleListOk on p agree rules), agree.ruleSet ({ open, rules = (walkRuleList p rules), trailingComma, close })

theorem ruleListOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List RewriteRule):
    runRuleList on input = Ok (walkRuleList p input) :=
  match input with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] => seq2 (() => rule.traverse on) (() => traverseRuleList on rest) (v1 v2 => [{ reverse, rule = v1 }, ..v2]) (rule.walk p) (walkRuleList p rest) (exprOk on p agree rule) (ruleListOk on p agree rest)

theorem rowOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Row):
    runRow on input = Ok (walkRow p input) :=
  match input with
    | { open, abilities, variable, close } => seq1 (() => traverseExprs on abilities) (v1 => { open, abilities = v1, variable, close }) (walkExprs p abilities) (exprsOk on p agree abilities)

theorem exprsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Expr):
    runExprs on input = Ok (walkExprs p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => seq2 (() => first.traverse on) (() => traverseExprs on rest) (v1 v2 => [v1, ..v2]) (first.walk p) (walkExprs p rest) (exprOk on p agree first) (exprsOk on p agree rest)

theorem linksOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List (Word, Expr)):
    runLinks on input = Ok (walkLinks p input) :=
  match input with
    | [] => byComputing
    | [(operator, operand), ..rest] => seq2 (() => operand.traverse on) (() => traverseLinks on rest) (v1 v2 => [(operator, v1), ..v2]) (operand.walk p) (walkLinks p rest) (exprOk on p agree operand) (linksOk on p agree rest)

theorem piecesOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Piece):
    runPieces on input = Ok (walkPieces p input) :=
  match input with
    | [] => byComputing
    | [TextPiece word, ..rest] => seq1 (() => traversePieces on rest) (v1 => [TextPiece word, ..v1]) (walkPieces p rest) (piecesOk on p agree rest)
    | [Interpolation open value close, ..rest] => seq2 (() => value.traverse on) (() => traversePieces on rest) (v1 v2 => [Interpolation open v1 close, ..v2]) (value.walk p) (walkPieces p rest) (exprOk on p agree value) (piecesOk on p agree rest)

theorem scrutineesOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Scrutinee):
    runScrutinees on input = Ok (walkScrutinees p input) :=
  match input with
    | [] => byComputing
    | [{ name, value }, ..rest] => seq2 (() => value.traverse on) (() => traverseScrutinees on rest) (v1 v2 => [{ name, value = v1 }, ..v2]) (value.walk p) (walkScrutinees p rest) (exprOk on p agree value) (scrutineesOk on p agree rest)

theorem armsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Arm):
    runArms on input = Ok (walkArms p input) :=
  match input with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] => seq4 (() => traversePatterns on patterns) (() => traverseGuard on guard) (() => traverseAfter on body) (() => traverseArms on rest) (v1 v2 v3 v4 => [{ bar, patterns = v1, guard = v2, body = v3 }, ..v4]) (walkPatterns p patterns) (walkGuard p guard) (walkAfter p body) (walkArms p rest) (patternsOk on p agree patterns) (guardOk on p agree guard) (afterOk on p agree body) (armsOk on p agree rest)

theorem paramsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Param):
    runParams on input = Ok (walkParams p input) :=
  match input with
    | [] => byComputing
    | [NameParam word, ..rest] => seq1 (() => traverseParams on rest) (v1 => [NameParam word, ..v1]) (walkParams p rest) (paramsOk on p agree rest)
    | [PatternParam pattern, ..rest] => seq2 (() => pattern.traverse on) (() => traverseParams on rest) (v1 v2 => [PatternParam v1, ..v2]) (pattern.walk p) (walkParams p rest) (patternOk on p agree pattern) (paramsOk on p agree rest)
    | [Grouped group, ..rest] => seq2 (() => group.traverse on) (() => traverseParams on rest) (v1 v2 => [Grouped v1, ..v2]) (group.walk p) (walkParams p rest) (groupOk on p agree group) (paramsOk on p agree rest)
    | [TypedPattern open pattern colon annotation close, ..rest] => seq3 (() => pattern.traverse on) (() => annotation.traverse on) (() => traverseParams on rest) (v1 v2 v3 => [TypedPattern open v1 colon v2 close, ..v3]) (pattern.walk p) (annotation.walk p) (walkParams p rest) (patternOk on p agree pattern) (exprOk on p agree annotation) (paramsOk on p agree rest)

theorem groupOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Group):
    runGroup on input = Ok (input.walk p) :=
  match input with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => seq3 (() => traverseAttributes on attributes) (() => traverseOptional on annotation) (() => traverseAfter on default) (v1 v2 v3 => { kind, implicit, open, attributes = v1, auto, names, colon, annotation = v2, default = v3, close, bare }) (walkAttributes p attributes) (walkOptional p annotation) (walkAfter p default) (attributesOk on p agree attributes) (optionalOk on p agree annotation) (afterOk on p agree default)

theorem patternOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Pattern):
    runPattern on input = Ok (input.walk p) :=
  match input with
    | PatternWord kind word => agree.pattern (PatternWord kind word)
    | PatternCtor name arguments => rewrite seq1k (() => traversePatterns on arguments) (v1 => PatternCtor name v1) on.pattern (walkPatterns p arguments) (patternsOk on p agree arguments), agree.pattern (PatternCtor name (walkPatterns p arguments))
    | PatternCtorFields name fields => rewrite seq1k (() => traverseFields on fields) (v1 => PatternCtorFields name v1) on.pattern (walkFields p fields) (fieldsPatternOk on p agree fields), agree.pattern (PatternCtorFields name (walkFields p fields))
    | PatternRecord fields => rewrite seq1k (() => traverseFields on fields) (v1 => PatternRecord v1) on.pattern (walkFields p fields) (fieldsPatternOk on p agree fields), agree.pattern (PatternRecord (walkFields p fields))
    | PatternTuple open items trailingComma close => rewrite seq1k (() => traversePatterns on items) (v1 => PatternTuple open v1 trailingComma close) on.pattern (walkPatterns p items) (patternsOk on p agree items), agree.pattern (PatternTuple open (walkPatterns p items) trailingComma close)
    | PatternList open items trailingComma tail close => rewrite seq2k (() => traversePatterns on items) (() => traverseTail on tail) (v1 v2 => PatternList open v1 trailingComma v2 close) on.pattern (walkPatterns p items) (walkTail p tail) (patternsOk on p agree items) (tailOk on p agree tail), agree.pattern (PatternList open (walkPatterns p items) trailingComma (walkTail p tail) close)
    | PatternNamed open name colonEq value close => rewrite seq1k (() => value.traverse on) (v1 => PatternNamed open name colonEq v1 close) on.pattern (value.walk p) (patternOk on p agree value), agree.pattern (PatternNamed open name colonEq (value.walk p) close)
    | PatternOr first rest => rewrite seq2k (() => first.traverse on) (() => traversePatternLinks on rest) (v1 v2 => PatternOr v1 v2) on.pattern (first.walk p) (walkPatternLinks p rest) (patternOk on p agree first) (patternLinksOk on p agree rest), agree.pattern (PatternOr (first.walk p) (walkPatternLinks p rest))
    | PatternParen open inner close => rewrite seq1k (() => inner.traverse on) (v1 => PatternParen open v1 close) on.pattern (inner.walk p) (patternOk on p agree inner), agree.pattern (PatternParen open (inner.walk p) close)
    | PatternNegative minus number => agree.pattern (PatternNegative minus number)
    | PatternAbsurd open close => agree.pattern (PatternAbsurd open close)
    | PatternAppend start operator rest => rewrite seq2k (() => start.traverse on) (() => rest.traverse on) (v1 v2 => PatternAppend v1 operator v2) on.pattern (start.walk p) (rest.walk p) (patternOk on p agree start) (patternOk on p agree rest), agree.pattern (PatternAppend (start.walk p) operator (rest.walk p))

theorem patternsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Pattern):
    runPatterns on input = Ok (walkPatterns p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => seq2 (() => first.traverse on) (() => traversePatterns on rest) (v1 v2 => [v1, ..v2]) (first.walk p) (walkPatterns p rest) (patternOk on p agree first) (patternsOk on p agree rest)

theorem patternLinksOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List (Word, Pattern)):
    runPatternLinks on input = Ok (walkPatternLinks p input) :=
  match input with
    | [] => byComputing
    | [(bar, alternative), ..rest] => seq2 (() => alternative.traverse on) (() => traversePatternLinks on rest) (v1 v2 => [(bar, v1), ..v2]) (alternative.walk p) (walkPatternLinks p rest) (patternOk on p agree alternative) (patternLinksOk on p agree rest)

theorem fieldsPatternOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: FieldsPattern):
    runFieldsPattern on input = Ok (walkFields p input) :=
  match input with
    | { open, fields, trailingComma, rest, close } => seq1 (() => traverseFieldPatterns on fields) (v1 => { open, fields = v1, trailingComma, rest, close }) (walkFieldPatterns p fields) (fieldPatternsOk on p agree fields)

theorem fieldPatternsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List FieldPattern):
    runFieldPatterns on input = Ok (walkFieldPatterns p input) :=
  match input with
    | [] => byComputing
    | [{ name, value = Some (equals, pattern) }, ..rest] => seq2 (() => pattern.traverse on) (() => traverseFieldPatterns on rest) (v1 v2 => [{ name, value = Some (equals, v1) }, ..v2]) (pattern.walk p) (walkFieldPatterns p rest) (patternOk on p agree pattern) (fieldPatternsOk on p agree rest)
    | [{ name, value = None }, ..rest] => seq1 (() => traverseFieldPatterns on rest) (v1 => [{ name, value = None }, ..v1]) (walkFieldPatterns p rest) (fieldPatternsOk on p agree rest)

theorem declOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Decl):
    runDecl on input = Ok (input.walk p) :=
  match input with
    | Namespace keyword name => agree.decl (Namespace keyword name)
    | Import keyword path open imported close => agree.decl (Import keyword path open imported close)
    | Definition attributes header body => rewrite seq3k (() => traverseAttributes on attributes) (() => traverseHeader on header) (() => traverseDefBody on body) (v1 v2 v3 => Definition v1 v2 v3) on.decl (walkAttributes p attributes) (walkHeader p header) (walkDefBody p body) (attributesOk on p agree attributes) (headerOk on p agree header) (defBodyOk on p agree body), agree.decl (Definition (walkAttributes p attributes) (walkHeader p header) (walkDefBody p body))
    | Data attributes isInterface keyword name params indices body =>
      match indices with
        | Some { colon, steps, last } =>
          match body with
            | Abstract => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => Some { colon, steps = (traverseIndices on steps), last = (last.traverse on) }) (() => Abstract) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (Abstract) (attributesOk on p agree attributes) (groupsOk on p agree params) (seq2 (() => traverseIndices on steps) (() => last.traverse on) (w1 w2 => Some { colon, steps = w1, last = w2 }) (walkIndices p steps) (last.walk p) (indicesOk on p agree steps) (exprOk on p agree last)) (Fail.toResultPure (Abstract)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (Abstract))
            | Synonym equals annotation => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => Some { colon, steps = (traverseIndices on steps), last = (last.traverse on) }) (() => Synonym equals (annotation.traverse on)) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (Synonym equals (annotation.walk p)) (attributesOk on p agree attributes) (groupsOk on p agree params) (seq2 (() => traverseIndices on steps) (() => last.traverse on) (w1 w2 => Some { colon, steps = w1, last = w2 }) (walkIndices p steps) (last.walk p) (indicesOk on p agree steps) (exprOk on p agree last)) (seq1 (() => annotation.traverse on) (w1 => Synonym equals w1) (annotation.walk p) (exprOk on p agree annotation)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (Synonym equals (annotation.walk p)))
            | RecordBody equals fields => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => Some { colon, steps = (traverseIndices on steps), last = (last.traverse on) }) (() => RecordBody equals (fields.traverse on)) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (RecordBody equals (fields.walk p)) (attributesOk on p agree attributes) (groupsOk on p agree params) (seq2 (() => traverseIndices on steps) (() => last.traverse on) (w1 w2 => Some { colon, steps = w1, last = w2 }) (walkIndices p steps) (last.walk p) (indicesOk on p agree steps) (exprOk on p agree last)) (seq1 (() => fields.traverse on) (w1 => RecordBody equals w1) (fields.walk p) (fieldsOk on p agree fields)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (RecordBody equals (fields.walk p)))
            | Sum equals constructors => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => Some { colon, steps = (traverseIndices on steps), last = (last.traverse on) }) (() => Sum equals (traverseConstructors on constructors)) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (Sum equals (walkConstructors p constructors)) (attributesOk on p agree attributes) (groupsOk on p agree params) (seq2 (() => traverseIndices on steps) (() => last.traverse on) (w1 w2 => Some { colon, steps = w1, last = w2 }) (walkIndices p steps) (last.walk p) (indicesOk on p agree steps) (exprOk on p agree last)) (seq1 (() => traverseConstructors on constructors) (w1 => Sum equals w1) (walkConstructors p constructors) (constructorsOk on p agree constructors)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (Some { colon, steps = (walkIndices p steps), last = (last.walk p) }) (Sum equals (walkConstructors p constructors)))
        | None =>
          match body with
            | Abstract => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => None) (() => Abstract) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (None) (Abstract) (attributesOk on p agree attributes) (groupsOk on p agree params) (Fail.toResultPure (None)) (Fail.toResultPure (Abstract)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (None) (Abstract))
            | Synonym equals annotation => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => None) (() => Synonym equals (annotation.traverse on)) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (None) (Synonym equals (annotation.walk p)) (attributesOk on p agree attributes) (groupsOk on p agree params) (Fail.toResultPure (None)) (seq1 (() => annotation.traverse on) (w1 => Synonym equals w1) (annotation.walk p) (exprOk on p agree annotation)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (None) (Synonym equals (annotation.walk p)))
            | RecordBody equals fields => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => None) (() => RecordBody equals (fields.traverse on)) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (None) (RecordBody equals (fields.walk p)) (attributesOk on p agree attributes) (groupsOk on p agree params) (Fail.toResultPure (None)) (seq1 (() => fields.traverse on) (w1 => RecordBody equals w1) (fields.walk p) (fieldsOk on p agree fields)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (None) (RecordBody equals (fields.walk p)))
            | Sum equals constructors => rewrite seq4k (() => traverseAttributes on attributes) (() => traverseGroups on params) (() => None) (() => Sum equals (traverseConstructors on constructors)) (v1 v2 v3 v4 => Data v1 isInterface keyword name v2 v3 v4) on.decl (walkAttributes p attributes) (walkGroups p params) (None) (Sum equals (walkConstructors p constructors)) (attributesOk on p agree attributes) (groupsOk on p agree params) (Fail.toResultPure (None)) (seq1 (() => traverseConstructors on constructors) (w1 => Sum equals w1) (walkConstructors p constructors) (constructorsOk on p agree constructors)), agree.decl (Data (walkAttributes p attributes) isInterface keyword name (walkGroups p params) (None) (Sum equals (walkConstructors p constructors)))
    | Ability keyword name params whereKeyword operations => rewrite seq2k (() => traverseGroups on params) (() => traverseOperations on operations) (v1 v2 => Ability keyword name v1 whereKeyword v2) on.decl (walkGroups p params) (walkOperations p operations) (groupsOk on p agree params) (operationsOk on p agree operations), agree.decl (Ability keyword name (walkGroups p params) whereKeyword (walkOperations p operations))
    | Test keyword name colonEq body => rewrite seq1k (() => body.traverse on) (v1 => Test keyword name colonEq v1) on.decl (body.walk p) (exprOk on p agree body), agree.decl (Test keyword name colonEq (body.walk p))
    | RuleSetDecl keyword name colonEq set => rewrite seq1k (() => traverseRuleSet on set) (v1 => RuleSetDecl keyword name colonEq v1) on.decl (walkRuleSet p set) (ruleSetOk on p agree set), agree.decl (RuleSetDecl keyword name colonEq (walkRuleSet p set))

theorem headerOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Header):
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
      } => rewrite seq3j (() => traverseGroups on params) (() => result.traverse on) (() => traverseAfter on decreasingClause) (v1 v2 v3 => { exportKeyword, opaqueKeyword, kind, keyword, name, forallKeyword, params = v1, colon, result = v2, decreasingClause = v3, unfoldingClause }) on.header (walkGroups p params) (result.walk p) (walkAfter p decreasingClause) (groupsOk on p agree params) (exprOk on p agree result) (afterOk on p agree decreasingClause), agree.header ({ exportKeyword, opaqueKeyword, kind, keyword, name, forallKeyword, params = (walkGroups p params), colon, result = (result.walk p), decreasingClause = (walkAfter p decreasingClause), unfoldingClause })

theorem defBodyOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: DefBody):
    runDefBody on input = Ok (walkDefBody p input) :=
  match input with
    | Primitive => byComputing
    | Assigned colonEq value => seq1 (() => value.traverse on) (v1 => Assigned colonEq v1) (value.walk p) (exprOk on p agree value)
    | Arms arms => seq1 (() => traverseArms on arms) (v1 => Arms v1) (walkArms p arms) (armsOk on p agree arms)

theorem groupsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Group):
    runGroups on input = Ok (walkGroups p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => seq2 (() => first.traverse on) (() => traverseGroups on rest) (v1 v2 => [v1, ..v2]) (first.walk p) (walkGroups p rest) (groupOk on p agree first) (groupsOk on p agree rest)

theorem indicesOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List (Index, Word)):
    runIndices on input = Ok (walkIndices p input) :=
  match input with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] => seq2 (() => binder.traverse on) (() => traverseIndices on rest) (v1 v2 => [(IndexBinder v1, arrow), ..v2]) (binder.walk p) (walkIndices p rest) (groupOk on p agree binder) (indicesOk on p agree rest)
    | [(IndexType annotation, arrow), ..rest] => seq2 (() => annotation.traverse on) (() => traverseIndices on rest) (v1 v2 => [(IndexType v1, arrow), ..v2]) (annotation.walk p) (walkIndices p rest) (exprOk on p agree annotation) (indicesOk on p agree rest)

theorem fieldsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Fields):
    runFields on input = Ok (input.walk p) :=
  match input with
    | { open, fields, trailingComma, close } => rewrite seq1j (() => traverseFieldList on fields) (v1 => { open, fields = v1, trailingComma, close }) on.fields (walkFieldList p fields) (fieldListOk on p agree fields), agree.fields ({ open, fields = (walkFieldList p fields), trailingComma, close })

theorem fieldListOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Field):
    runFieldList on input = Ok (walkFieldList p input) :=
  match input with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] => seq4 (() => traverseAttributes on attributes) (() => annotation.traverse on) (() => traverseAfter on default) (() => traverseFieldList on rest) (v1 v2 v3 v4 => [{ attributes = v1, name, colon, annotation = v2, default = v3 }, ..v4]) (walkAttributes p attributes) (annotation.walk p) (walkAfter p default) (walkFieldList p rest) (attributesOk on p agree attributes) (exprOk on p agree annotation) (afterOk on p agree default) (fieldListOk on p agree rest)

theorem constructorsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Constructor):
    runConstructors on input = Ok (walkConstructors p input) :=
  match input with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] => seq4 (() => traverseAttributes on attributes) (() => traverseParts on fields) (() => traverseAfter on result) (() => traverseConstructors on rest) (v1 v2 v3 v4 => [{ bar, attributes = v1, name, fields = v2, result = v3 }, ..v4]) (walkAttributes p attributes) (walkParts p fields) (walkAfter p result) (walkConstructors p rest) (attributesOk on p agree attributes) (partsOk on p agree fields) (afterOk on p agree result) (constructorsOk on p agree rest)

theorem partsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List ConstructorPart):
    runParts on input = Ok (walkParts p input) :=
  match input with
    | [] => byComputing
    | [PartGroup group, ..rest] => seq2 (() => group.traverse on) (() => traverseParts on rest) (v1 v2 => [PartGroup v1, ..v2]) (group.walk p) (walkParts p rest) (groupOk on p agree group) (partsOk on p agree rest)
    | [PartFields fields, ..rest] => seq2 (() => fields.traverse on) (() => traverseParts on rest) (v1 v2 => [PartFields v1, ..v2]) (fields.walk p) (walkParts p rest) (fieldsOk on p agree fields) (partsOk on p agree rest)

theorem operationsOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Operation):
    runOperations on input = Ok (walkOperations p input) :=
  match input with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] => seq2 (() => annotation.traverse on) (() => traverseOperations on rest) (v1 v2 => [{ name, colon, annotation = v1 }, ..v2]) (annotation.walk p) (walkOperations p rest) (exprOk on p agree annotation) (operationsOk on p agree rest)

theorem attributesOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: List Attributes):
    runAttributes on input = Ok (walkAttributes p input) :=
  match input with
    | [] => byComputing
    | [first, ..rest] => seq2 (() => on.attributes first) (() => traverseAttributes on rest) (v1 v2 => [v1, ..v2]) (p.attributes first) (walkAttributes p rest) (agree.attributes first) (attributesOk on p agree rest)

theorem optionalOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Option Expr):
    runOptional on input = Ok (walkOptional p input) :=
  match input with
    | Some value => seq1 (() => value.traverse on) (v1 => Some v1) (value.walk p) (exprOk on p agree value)
    | None => byComputing

theorem afterOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Option (k, Expr)):
    runAfter on input = Ok (walkAfter p input) :=
  match input with
    | Some (word, value) => seq1 (() => value.traverse on) (v1 => Some (word, v1)) (value.walk p) (exprOk on p agree value)
    | None => byComputing

theorem guardOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Option Guard):
    runGuard on input = Ok (walkGuard p input) :=
  match input with
    | Some { keyword, binder, condition } => seq1 (() => condition.traverse on) (v1 => Some { keyword, binder, condition = v1 }) (condition.walk p) (exprOk on p agree condition)
    | None => byComputing

theorem tailOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Option (Word, Pattern)):
    runTail on input = Ok (walkTail p input) :=
  match input with
    | Some (dots, rest) => seq1 (() => rest.traverse on) (v1 => Some (dots, v1)) (rest.walk p) (patternOk on p agree rest)
    | None => byComputing

theorem beforeOk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (input: Option (Expr, k)):
    runBefore on input = Ok (walkBefore p input) :=
  match input with
    | Some (value, word) => seq1 (() => value.traverse on) (v1 => Some (v1, word)) (value.walk p) (exprOk on p agree value)
    | None => byComputing

theorem exprTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Expr):
    (input.walk s).walk m = input.walk m :=
  match input with
    | Atom kind word => rewrite keeps.expr (Atom kind word)
    | Paren open inner close => rewrite keeps.expr (Paren open (inner.walk s) close), exprTwice s m keeps inner
    | Unit open close => rewrite keeps.expr (Unit open close)
    | Universe keyword level => rewrite keeps.expr (Universe keyword level)
    | Include keyword path => rewrite keeps.expr (Include keyword path)
    | Tuple open items trailingComma close => rewrite keeps.expr (Tuple open (walkExprs s items) trailingComma close), exprsTwice s m keeps items
    | ListOf open items trailingComma close => rewrite keeps.expr (ListOf open (walkExprs s items) trailingComma close), exprsTwice s m keeps items
    | Spread dots list => rewrite keeps.expr (Spread dots (list.walk s)), exprTwice s m keeps list
    | Record open base fields trailingComma close => rewrite keeps.expr (Record open (walkBefore s base) (walkExprs s fields) trailingComma close), beforeTwice s m keeps base, exprsTwice s m keeps fields
    | RecordField name equals value => rewrite keeps.expr (RecordField name equals (value.walk s)), exprTwice s m keeps value
    | CtorFields ctor record => rewrite keeps.expr (CtorFields (ctor.walk s) (record.walk s)), exprTwice s m keeps ctor, exprTwice s m keeps record
    | App head arguments => rewrite keeps.expr (App (head.walk s) (walkExprs s arguments)), exprTwice s m keeps head, exprsTwice s m keeps arguments
    | NamedArg open name colonEq value close => rewrite keeps.expr (NamedArg open name colonEq (value.walk s) close), exprTwice s m keeps value
    | FieldAccess target dot field => rewrite keeps.expr (FieldAccess (walkOptional s target) dot field), optionalTwice s m keeps target
    | Section body => rewrite keeps.expr (Section (body.walk s)), exprTwice s m keeps body
    | OperatorSection open left operator right close => rewrite keeps.expr (OperatorSection open (walkOptional s left) operator (walkOptional s right) close), optionalTwice s m keeps left, optionalTwice s m keeps right
    | Infix kind left operator right => rewrite keeps.expr (Infix kind (left.walk s) operator (right.walk s)), exprTwice s m keeps left, exprTwice s m keeps right
    | Chain first rest => rewrite keeps.expr (Chain (first.walk s) (walkLinks s rest)), exprTwice s m keeps first, linksTwice s m keeps rest
    | Prefix operator operand => rewrite keeps.expr (Prefix operator (operand.walk s)), exprTwice s m keeps operand
    | Binding kind keyword params arrow body => rewrite keeps.expr (Binding kind keyword (walkParams s params) arrow (body.walk s)), paramsTwice s m keeps params, exprTwice s m keeps body
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse => rewrite keeps.expr (If keyword binder (condition.walk s) thenKeyword (whenTrue.walk s) elseKeyword (whenFalse.walk s)), exprTwice s m keeps condition, exprTwice s m keeps whenTrue, exprTwice s m keeps whenFalse
    | Annotation open value colon annotation close => rewrite keeps.expr (Annotation open (value.walk s) colon (annotation.walk s) close), exprTwice s m keeps value, exprTwice s m keeps annotation
    | Interpolated pieces => rewrite keeps.expr (Interpolated (walkPieces s pieces)), piecesTwice s m keeps pieces
    | Match keyword scrutinees withKeyword arms => rewrite keeps.expr (Match keyword (walkScrutinees s scrutinees) withKeyword (walkArms s arms)), scrutineesTwice s m keeps scrutinees, armsTwice s m keeps arms
    | ClauseLambda keyword word arms => rewrite keeps.expr (ClauseLambda keyword word (walkArms s arms)), armsTwice s m keeps arms
    | Facts kind keyword facts => rewrite keeps.expr (Facts kind keyword (facts.walk s)), exprTwice s m keeps facts
    | FunctionType binder arrow result => rewrite keeps.expr (FunctionType (binder.walk s) arrow (result.walk s)), groupTwice s m keeps binder, exprTwice s m keeps result
    | Effect row result => rewrite keeps.expr (Effect (walkRow s row) (result.walk s)), rowTwice s m keeps row, exprTwice s m keeps result
    | Block first rest result => rewrite keeps.expr (Block (walkStatement s first) (walkStatements s rest) (result.walk s)), statementTwice s m keeps first, statementsTwice s m keeps rest, exprTwice s m keeps result
    | LetIn binding semicolon body => rewrite keeps.expr (LetIn (walkLet s binding) semicolon (body.walk s)), letTwice s m keeps binding, exprTwice s m keeps body
    | Handle keyword computation withKeyword clauses => rewrite keeps.expr (Handle keyword (computation.walk s) withKeyword (walkClauses s clauses)), exprTwice s m keeps computation, clausesTwice s m keeps clauses
    | Reify keyword reifyWord computation withKeyword clauses => rewrite keeps.expr (Reify keyword reifyWord (computation.walk s) withKeyword (walkClauses s clauses)), exprTwice s m keeps computation, clausesTwice s m keeps clauses
    | Induct keyword inductWord call withKeyword arms => rewrite keeps.expr (Induct keyword inductWord (call.walk s) withKeyword (walkInductArms s arms)), exprTwice s m keeps call, inductArmsTwice s m keeps arms
    | Calc keyword first steps => rewrite keeps.expr (Calc keyword (first.walk s) (walkSteps s steps)), exprTwice s m keeps first, calcStepsTwice s m keeps steps
    | Rewrite keyword rules target body => rewrite keeps.expr (Rewrite keyword (walkRules s rules) (walkAfter s target) (walkAfter s body)), rulesTwice s m keeps rules, afterTwice s m keeps target, afterTwice s m keeps body
    | Cases keyword thenKeyword body => rewrite keeps.expr (Cases keyword thenKeyword (body.walk s)), exprTwice s m keeps body

theorem statementsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Statement):
    walkStatements m (walkStatements s input) = walkStatements m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite statementTwice s m keeps first, statementsTwice s m keeps rest

theorem statementTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Statement):
    walkStatement m (walkStatement s input) = walkStatement m input :=
  match input with
    | LetStatement binding => rewrite letTwice s m keeps binding
    | LocalDef attributes header body => rewrite attributesTwice s m keeps attributes, headerTwice s m keeps header, defBodyTwice s m keeps body
    | ExprStatement value => rewrite exprTwice s m keeps value

theorem letTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Let):
    walkLet m (walkLet s input) = walkLet m input :=
  match input with
    | { keyword, pattern, annotation, colonEq, value } => rewrite patternTwice s m keeps pattern, afterTwice s m keeps annotation, exprTwice s m keeps value

theorem clausesTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List HandlerClause):
    walkClauses m (walkClauses s input) = walkClauses m input :=
  match input with
    | [] => byComputing
    | [ReturnClause bar keyword name arrow body, ..rest] => rewrite exprTwice s m keeps body, clausesTwice s m keeps rest
    | [OperationClause bar operation argument comma continuation arrow body, ..rest] => rewrite patternTwice s m keeps argument, exprTwice s m keeps body, clausesTwice s m keeps rest

theorem inductArmsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List InductArm):
    walkInductArms m (walkInductArms s input) = walkInductArms m input :=
  match input with
    | [] => byComputing
    | [{ bar, case, names, arrow, body }, ..rest] => rewrite exprTwice s m keeps body, inductArmsTwice s m keeps rest

theorem calcStepsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List CalcStep):
    walkSteps m (walkSteps s input) = walkSteps m input :=
  match input with
    | [] => byComputing
    | [{ underscore, relation, operand, proof }, ..rest] => rewrite exprTwice s m keeps operand, afterTwice s m keeps proof, calcStepsTwice s m keeps rest

theorem rulesTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Rules):
    walkRules m (walkRules s input) = walkRules m input :=
  match input with
    | RuleList rules => rewrite ruleListTwice s m keeps rules
    | Repeatedly word set => rewrite ruleSetTwice s m keeps set

theorem ruleSetTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: RuleSet):
    walkRuleSet m (walkRuleSet s input) = walkRuleSet m input :=
  match input with
    | { open, rules, trailingComma, close } => rewrite keeps.ruleSet ({ open, rules = (walkRuleList s rules), trailingComma, close }), ruleListTwice s m keeps rules

theorem ruleListTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List RewriteRule):
    walkRuleList m (walkRuleList s input) = walkRuleList m input :=
  match input with
    | [] => byComputing
    | [{ reverse, rule }, ..rest] => rewrite exprTwice s m keeps rule, ruleListTwice s m keeps rest

theorem rowTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Row):
    walkRow m (walkRow s input) = walkRow m input :=
  match input with
    | { open, abilities, variable, close } => rewrite exprsTwice s m keeps abilities

theorem exprsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Expr):
    walkExprs m (walkExprs s input) = walkExprs m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite exprTwice s m keeps first, exprsTwice s m keeps rest

theorem linksTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List (Word, Expr)):
    walkLinks m (walkLinks s input) = walkLinks m input :=
  match input with
    | [] => byComputing
    | [(operator, operand), ..rest] => rewrite exprTwice s m keeps operand, linksTwice s m keeps rest

theorem piecesTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Piece):
    walkPieces m (walkPieces s input) = walkPieces m input :=
  match input with
    | [] => byComputing
    | [TextPiece word, ..rest] => rewrite piecesTwice s m keeps rest
    | [Interpolation open value close, ..rest] => rewrite exprTwice s m keeps value, piecesTwice s m keeps rest

theorem scrutineesTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Scrutinee):
    walkScrutinees m (walkScrutinees s input) = walkScrutinees m input :=
  match input with
    | [] => byComputing
    | [{ name, value }, ..rest] => rewrite exprTwice s m keeps value, scrutineesTwice s m keeps rest

theorem armsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Arm):
    walkArms m (walkArms s input) = walkArms m input :=
  match input with
    | [] => byComputing
    | [{ bar, patterns, guard, body }, ..rest] => rewrite patternsTwice s m keeps patterns, guardTwice s m keeps guard, afterTwice s m keeps body, armsTwice s m keeps rest

theorem paramsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Param):
    walkParams m (walkParams s input) = walkParams m input :=
  match input with
    | [] => byComputing
    | [NameParam word, ..rest] => rewrite paramsTwice s m keeps rest
    | [PatternParam pattern, ..rest] => rewrite patternTwice s m keeps pattern, paramsTwice s m keeps rest
    | [Grouped group, ..rest] => rewrite groupTwice s m keeps group, paramsTwice s m keeps rest
    | [TypedPattern open pattern colon annotation close, ..rest] => rewrite patternTwice s m keeps pattern, exprTwice s m keeps annotation, paramsTwice s m keeps rest

theorem groupTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Group):
    (input.walk s).walk m = input.walk m :=
  match input with
    | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } => rewrite attributesTwice s m keeps attributes, optionalTwice s m keeps annotation, afterTwice s m keeps default

theorem patternTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Pattern):
    (input.walk s).walk m = input.walk m :=
  match input with
    | PatternWord kind word => rewrite keeps.pattern (PatternWord kind word)
    | PatternCtor name arguments => rewrite keeps.pattern (PatternCtor name (walkPatterns s arguments)), patternsTwice s m keeps arguments
    | PatternCtorFields name fields => rewrite keeps.pattern (PatternCtorFields name (walkFields s fields)), fieldsPatternTwice s m keeps fields
    | PatternRecord fields => rewrite keeps.pattern (PatternRecord (walkFields s fields)), fieldsPatternTwice s m keeps fields
    | PatternTuple open items trailingComma close => rewrite keeps.pattern (PatternTuple open (walkPatterns s items) trailingComma close), patternsTwice s m keeps items
    | PatternList open items trailingComma tail close => rewrite keeps.pattern (PatternList open (walkPatterns s items) trailingComma (walkTail s tail) close), patternsTwice s m keeps items, tailTwice s m keeps tail
    | PatternNamed open name colonEq value close => rewrite keeps.pattern (PatternNamed open name colonEq (value.walk s) close), patternTwice s m keeps value
    | PatternOr first rest => rewrite keeps.pattern (PatternOr (first.walk s) (walkPatternLinks s rest)), patternTwice s m keeps first, patternLinksTwice s m keeps rest
    | PatternParen open inner close => rewrite keeps.pattern (PatternParen open (inner.walk s) close), patternTwice s m keeps inner
    | PatternNegative minus number => rewrite keeps.pattern (PatternNegative minus number)
    | PatternAbsurd open close => rewrite keeps.pattern (PatternAbsurd open close)
    | PatternAppend start operator rest => rewrite keeps.pattern (PatternAppend (start.walk s) operator (rest.walk s)), patternTwice s m keeps start, patternTwice s m keeps rest

theorem patternsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Pattern):
    walkPatterns m (walkPatterns s input) = walkPatterns m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite patternTwice s m keeps first, patternsTwice s m keeps rest

theorem patternLinksTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List (Word, Pattern)):
    walkPatternLinks m (walkPatternLinks s input) = walkPatternLinks m input :=
  match input with
    | [] => byComputing
    | [(bar, alternative), ..rest] => rewrite patternTwice s m keeps alternative, patternLinksTwice s m keeps rest

theorem fieldsPatternTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: FieldsPattern):
    walkFields m (walkFields s input) = walkFields m input :=
  match input with
    | { open, fields, trailingComma, rest, close } => rewrite fieldPatternsTwice s m keeps fields

theorem fieldPatternsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List FieldPattern):
    walkFieldPatterns m (walkFieldPatterns s input) = walkFieldPatterns m input :=
  match input with
    | [] => byComputing
    | [{ name, value = Some (equals, pattern) }, ..rest] => rewrite patternTwice s m keeps pattern, fieldPatternsTwice s m keeps rest
    | [{ name, value = None }, ..rest] => rewrite fieldPatternsTwice s m keeps rest

theorem declTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Decl):
    (input.walk s).walk m = input.walk m :=
  match input with
    | Namespace keyword name => rewrite keeps.decl (Namespace keyword name)
    | Import keyword path open imported close => rewrite keeps.decl (Import keyword path open imported close)
    | Definition attributes header body => rewrite keeps.decl (Definition (walkAttributes s attributes) (walkHeader s header) (walkDefBody s body)), attributesTwice s m keeps attributes, headerTwice s m keeps header, defBodyTwice s m keeps body
    | Data attributes isInterface keyword name params indices body =>
      match indices with
        | Some { colon, steps, last } =>
          match body with
            | Abstract => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (Some { colon, steps = (walkIndices s steps), last = (last.walk s) }) (Abstract)), attributesTwice s m keeps attributes, groupsTwice s m keeps params, indicesTwice s m keeps steps, exprTwice s m keeps last
            | Synonym equals annotation => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (Some { colon, steps = (walkIndices s steps), last = (last.walk s) }) (Synonym equals (annotation.walk s))), attributesTwice s m keeps attributes, groupsTwice s m keeps params, indicesTwice s m keeps steps, exprTwice s m keeps last, exprTwice s m keeps annotation
            | RecordBody equals fields => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (Some { colon, steps = (walkIndices s steps), last = (last.walk s) }) (RecordBody equals (fields.walk s))), attributesTwice s m keeps attributes, groupsTwice s m keeps params, indicesTwice s m keeps steps, exprTwice s m keeps last, fieldsTwice s m keeps fields
            | Sum equals constructors => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (Some { colon, steps = (walkIndices s steps), last = (last.walk s) }) (Sum equals (walkConstructors s constructors))), attributesTwice s m keeps attributes, groupsTwice s m keeps params, indicesTwice s m keeps steps, exprTwice s m keeps last, constructorsTwice s m keeps constructors
        | None =>
          match body with
            | Abstract => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (None) (Abstract)), attributesTwice s m keeps attributes, groupsTwice s m keeps params
            | Synonym equals annotation => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (None) (Synonym equals (annotation.walk s))), attributesTwice s m keeps attributes, groupsTwice s m keeps params, exprTwice s m keeps annotation
            | RecordBody equals fields => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (None) (RecordBody equals (fields.walk s))), attributesTwice s m keeps attributes, groupsTwice s m keeps params, fieldsTwice s m keeps fields
            | Sum equals constructors => rewrite keeps.decl (Data (walkAttributes s attributes) isInterface keyword name (walkGroups s params) (None) (Sum equals (walkConstructors s constructors))), attributesTwice s m keeps attributes, groupsTwice s m keeps params, constructorsTwice s m keeps constructors
    | Ability keyword name params whereKeyword operations => rewrite keeps.decl (Ability keyword name (walkGroups s params) whereKeyword (walkOperations s operations)), groupsTwice s m keeps params, operationsTwice s m keeps operations
    | Test keyword name colonEq body => rewrite keeps.decl (Test keyword name colonEq (body.walk s)), exprTwice s m keeps body
    | RuleSetDecl keyword name colonEq set => rewrite keeps.decl (RuleSetDecl keyword name colonEq (walkRuleSet s set)), ruleSetTwice s m keeps set

theorem headerTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Header):
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
      } => rewrite keeps.header ({ exportKeyword, opaqueKeyword, kind, keyword, name, forallKeyword, params = (walkGroups s params), colon, result = (result.walk s), decreasingClause = (walkAfter s decreasingClause), unfoldingClause }), groupsTwice s m keeps params, exprTwice s m keeps result, afterTwice s m keeps decreasingClause

theorem defBodyTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: DefBody):
    walkDefBody m (walkDefBody s input) = walkDefBody m input :=
  match input with
    | Primitive => byComputing
    | Assigned colonEq value => rewrite exprTwice s m keeps value
    | Arms arms => rewrite armsTwice s m keeps arms

theorem groupsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Group):
    walkGroups m (walkGroups s input) = walkGroups m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite groupTwice s m keeps first, groupsTwice s m keeps rest

theorem indicesTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List (Index, Word)):
    walkIndices m (walkIndices s input) = walkIndices m input :=
  match input with
    | [] => byComputing
    | [(IndexBinder binder, arrow), ..rest] => rewrite groupTwice s m keeps binder, indicesTwice s m keeps rest
    | [(IndexType annotation, arrow), ..rest] => rewrite exprTwice s m keeps annotation, indicesTwice s m keeps rest

theorem fieldsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Fields):
    (input.walk s).walk m = input.walk m :=
  match input with
    | { open, fields, trailingComma, close } => rewrite keeps.fields ({ open, fields = (walkFieldList s fields), trailingComma, close }), fieldListTwice s m keeps fields

theorem fieldListTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Field):
    walkFieldList m (walkFieldList s input) = walkFieldList m input :=
  match input with
    | [] => byComputing
    | [{ attributes, name, colon, annotation, default }, ..rest] => rewrite attributesTwice s m keeps attributes, exprTwice s m keeps annotation, afterTwice s m keeps default, fieldListTwice s m keeps rest

theorem constructorsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Constructor):
    walkConstructors m (walkConstructors s input) = walkConstructors m input :=
  match input with
    | [] => byComputing
    | [{ bar, attributes, name, fields, result }, ..rest] => rewrite attributesTwice s m keeps attributes, partsTwice s m keeps fields, afterTwice s m keeps result, constructorsTwice s m keeps rest

theorem partsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List ConstructorPart):
    walkParts m (walkParts s input) = walkParts m input :=
  match input with
    | [] => byComputing
    | [PartGroup group, ..rest] => rewrite groupTwice s m keeps group, partsTwice s m keeps rest
    | [PartFields fields, ..rest] => rewrite fieldsTwice s m keeps fields, partsTwice s m keeps rest

theorem operationsTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Operation):
    walkOperations m (walkOperations s input) = walkOperations m input :=
  match input with
    | [] => byComputing
    | [{ name, colon, annotation }, ..rest] => rewrite exprTwice s m keeps annotation, operationsTwice s m keeps rest

theorem attributesTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: List Attributes):
    walkAttributes m (walkAttributes s input) = walkAttributes m input :=
  match input with
    | [] => byComputing
    | [first, ..rest] => rewrite keeps.attributes first, attributesTwice s m keeps rest

theorem optionalTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Option Expr):
    walkOptional m (walkOptional s input) = walkOptional m input :=
  match input with
    | Some value => rewrite exprTwice s m keeps value
    | None => byComputing

theorem afterTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Option (k, Expr)):
    walkAfter m (walkAfter s input) = walkAfter m input :=
  match input with
    | Some (word, value) => rewrite exprTwice s m keeps value
    | None => byComputing

theorem guardTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Option Guard):
    walkGuard m (walkGuard s input) = walkGuard m input :=
  match input with
    | Some { keyword, binder, condition } => rewrite exprTwice s m keeps condition
    | None => byComputing

theorem tailTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Option (Word, Pattern)):
    walkTail m (walkTail s input) = walkTail m input :=
  match input with
    | Some (dots, rest) => rewrite patternTwice s m keeps rest
    | None => byComputing

theorem beforeTwice ∀ (s m: Pure) (keeps: Keeps s m) (input: Option (Expr, k)):
    walkBefore m (walkBefore s input) = walkBefore m input :=
  match input with
    | Some (value, word) => rewrite exprTwice s m keeps value
    | None => byComputing

-- A file.

def walkDecls (p: Pure): List Decl → List Decl
  | [] => []
  | [decl, ..rest] => [decl.walk p, ..walkDecls p rest]

theorem applyDeclsWalk ∀ (on: Steps) (p: Pure) (agree: Agrees on p) (decls: List Decl):
    applyDecls on decls = walkDecls p decls :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] => rewrite declOk on p agree decl, applyDeclsWalk on p agree rest

theorem walkDeclsTwice ∀ (s m: Pure) (keeps: Keeps s m) (decls: List Decl):
    walkDecls m (walkDecls s decls) = walkDecls m decls :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] => rewrite declTwice s m keeps decl, walkDeclsTwice s m keeps rest

--| A pass whose steps all finish is its pure copy's walk.
theorem applyWalk ∀ (file: SourceFile) (on: Steps) (p: Pure) (agree: Agrees on p):
    file.apply on = { file | decls = walkDecls p file.decls } :=
  rewrite applyDeclsWalk on p agree file.decls

--| The traversal lemma: a pass `on` whose steps finish as `s`'s do, and
--| `s`'s each keep what walking with `m` gives, keeps what applying `mean`
--| (whose steps finish as `m`'s) gives. The steps may rebuild the node's
--| descendants (`Keeps`).
theorem applyKeeps ∀ (file: SourceFile) (on mean: Steps) (s m: Pure)
    (agreeS: Agrees on s) (agreeM: Agrees mean m) (keeps: Keeps s m):
    (file.apply on).apply mean = file.apply mean :=
  rewrite applyWalk file on s agreeS,
    applyWalk { file | decls = walkDecls s file.decls } mean m agreeM,
    applyWalk file mean m agreeM,
    walkDeclsTwice s m keeps file.decls
