--| Blanking comments (SW-3884): `meaning` reads a tree with every comment
--| gone (docs/proposals/self-hosted-fmt-engine-plan.md §4, option (b)).
--|
--| Each function here blanks the comments a node holds itself: its own
--| tokens, and the tokens of the records inside it that the traversal
--| doesn't give a step of their own (a group, a row, a `let`, an arm, a
--| clause). The parts the traversal reaches with a step (an expression,
--| a pattern, a header, attribute or field list, a rule set) are left to
--| that step. So the traversal with these steps (`blankSteps`) blanks a
--| whole file, and `meaning`'s steps blank a node before they read it.
--|
--| Trusted with `meaning`: a token this misses keeps its comments in
--| `meaning`, which makes "the same program" stricter, never looser.
--| `Group.bare` summarises a group's comments and is set to `True`.

namespace Fmt
import Std (Bool, List, Option)
import Syntax (..)

def Comments.none: Comments := { above = [], after = None, blankBefore = False }

def Word.blank (word: Word): Word := { word | comments = Comments.none }

--| A part after a token held as its comments: a default after `:=`, a
--| proof after `:=`, a `let`'s type after `:`.
def blankAfter (input: Option (Comments, x)): Option (Comments, x) := match input with
  | Some (_, value) => Some (Comments.none, value)
  | None => None

--| A part after a token held as a word: an arm's body after `=>`.
def blankAfterWord (input: Option (Word, x)): Option (Word, x) := match input with
  | Some (word, value) => Some (word.blank, value)
  | None => None

def blankPair (input: Option (Word, Word)): Option (Word, Word) := match input with
  | Some (first, second) => Some (first.blank, second.blank)
  | None => None

def blankComments (input: Option Comments): Option Comments := match input with
  | Some _ => Some Comments.none
  | None => None

def blankLinks (input: List (Word, x)): List (Word, x) := match input with
  | [] => []
  | [(word, value), ..rest] => [(word.blank, value), ..blankLinks rest]

def blankWords (input: List Word): List Word := match input with
  | [] => []
  | [word, ..rest] => [word.blank, ..blankWords rest]

-- Expressions.

def blankExpr: Expr → Expr
  | Atom kind word => Atom kind word.blank
  | Paren open inner close => Paren open.blank inner close.blank
  | Unit open close => Unit open.blank close.blank
  | Universe keyword level => Universe keyword.blank level.blank
  | Include keyword path => Include keyword.blank path.blank
  | Tuple open items comma close => Tuple open.blank items comma close.blank
  | ListOf open items comma close => ListOf open.blank items comma close.blank
  | Spread dots list => Spread dots.blank list
  | Record open base fields comma close => Record open.blank (blankBase base) fields comma close.blank
  | RecordField name equals value => RecordField name.blank equals.blank value
  | NamedArg open name colonEq value close => NamedArg open.blank name.blank colonEq.blank value close.blank
  | FieldAccess target dot field => FieldAccess target dot.blank field.blank
  | OperatorSection open left operator right close => OperatorSection open.blank left operator.blank right close.blank
  | Infix kind left operator right => Infix kind left operator.blank right
  | Chain first rest => Chain first (blankLinks rest)
  | Prefix operator operand => Prefix operator.blank operand
  | Binding kind keyword params arrow body =>
    Binding kind (keyword.map Word.blank) (blankParams params) arrow.blank body
  | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    If keyword.blank (blankPair binder) condition thenKeyword.blank whenTrue elseKeyword.blank whenFalse
  | Annotation open value colon annotation close => Annotation open.blank value colon.blank annotation close.blank
  | Interpolated pieces => Interpolated (blankPieces pieces)
  | Match keyword scrutinees withKeyword arms =>
    Match keyword.blank (blankScrutinees scrutinees) withKeyword.blank (blankArms arms)
  | ClauseLambda keyword word arms => ClauseLambda keyword.blank (word.map Word.blank) (blankArms arms)
  | Facts kind keyword facts => Facts kind keyword.blank facts
  | FunctionType binder arrow result => FunctionType binder.blank arrow.blank result
  | Effect row result => Effect row.blank result
  | Block first rest result => Block first.blank (blankStatements rest) result
  | LetIn binding semicolon body => LetIn binding.blank Comments.none body
  | Handle _ computation _ clauses => Handle Comments.none computation Comments.none (blankClauses clauses)
  | Reify _ _ computation _ clauses =>
    Reify Comments.none Comments.none computation Comments.none (blankClauses clauses)
  | Induct _ _ call _ arms => Induct Comments.none Comments.none call Comments.none (blankInductArms arms)
  | Calc _ first steps => Calc Comments.none first (blankCalcSteps steps)
  | Rewrite _ rules target body => Rewrite Comments.none rules.blank (blankAfter target) (blankAfter body)
  | Cases _ _ body => Cases Comments.none Comments.none body
  | Walk _ items body => Walk Comments.none items (blankAfter body)
  | other => other

def blankBase (input: Option (Expr, Word)): Option (Expr, Word) := match input with
  | Some (value, bar) => Some (value, bar.blank)
  | None => None

def Row.blank (row: Row): Row :=
  { row | open = Comments.none, variable = blankCommentsWord row.variable, close = Comments.none }

--| A word after a token held as its comments: a row variable after its
--| `|`, an import's alias after `as`.
def blankCommentsWord (input: Option (Comments, Word)): Option (Comments, Word) := match input with
  | Some (_, word) => Some (Comments.none, word.blank)
  | None => None

def Group.blank (group: Group): Group := { group |
  open = Comments.none,
  auto = blankComments group.auto,
  names = blankWords group.names,
  colon = blankComments group.colon,
  default = blankAfter group.default,
  close = Comments.none,
  bare = True
}

def Param.blank: Param → Param
  | NameParam word => NameParam word.blank
  | PatternParam pattern => PatternParam pattern
  | Grouped group => Grouped group.blank
  | TypedPattern open pattern colon annotation close =>
    TypedPattern open.blank pattern colon.blank annotation close.blank

def blankParams: List Param → List Param
  | [] => []
  | [first, ..rest] => [first.blank, ..blankParams rest]

def blankGroups: List Group → List Group
  | [] => []
  | [first, ..rest] => [first.blank, ..blankGroups rest]

def blankPieces: List Piece → List Piece
  | [] => []
  | [TextPiece word, ..rest] => [TextPiece word.blank, ..blankPieces rest]
  | [Interpolation open value close, ..rest] => [Interpolation open.blank value close.blank, ..blankPieces rest]

def blankScrutinees: List Scrutinee → List Scrutinee
  | [] => []
  | [{ name, value }, ..rest] => [{ name = blankPair name, value }, ..blankScrutinees rest]

def Guard.blank (guard: Guard): Guard := { guard | keyword = guard.keyword.blank, binder = blankPair guard.binder }

def Arm.blank (arm: Arm): Arm :=
  { arm | bar = arm.bar.blank, guard = arm.guard.map Guard.blank, body = blankAfterWord arm.body }

def blankArms: List Arm → List Arm
  | [] => []
  | [first, ..rest] => [first.blank, ..blankArms rest]

def Let.blank (binding: Let): Let :=
  { binding | keyword = Comments.none, annotation = blankAfter binding.annotation, colonEq = Comments.none }

--| A local definition's header and attributes have steps of their own;
--| its body doesn't.
def Statement.blank: Statement → Statement
  | LetStatement binding => LetStatement binding.blank
  | LocalDef attributes header body => LocalDef attributes header body.blank
  | ExprStatement value => ExprStatement value

def blankStatements: List Statement → List Statement
  | [] => []
  | [first, ..rest] => [first.blank, ..blankStatements rest]

def HandlerClause.blank: HandlerClause → HandlerClause
  | ReturnClause _ _ name _ body => ReturnClause Comments.none Comments.none name.blank Comments.none body
  | OperationClause _ operation argument _ continuation _ body =>
    OperationClause Comments.none operation.blank argument Comments.none continuation.blank Comments.none body

def blankClauses: List HandlerClause → List HandlerClause
  | [] => []
  | [first, ..rest] => [first.blank, ..blankClauses rest]

def blankInductArms: List InductArm → List InductArm
  | [] => []
  | [{ bar, case, names, arrow, body }, ..rest] => [
    { bar = Comments.none, case = case.blank, names = blankWords names, arrow = Comments.none, body },
    ..blankInductArms rest
  ]

def blankCalcSteps: List CalcStep → List CalcStep
  | [] => []
  | [{ underscore, relation, operand, proof }, ..rest] => [
    { underscore = Comments.none, relation = relation.blank, operand, proof = blankAfter proof },
    ..blankCalcSteps rest
  ]

def blankReverse (input: Option (Comments, Comments)): Option (Comments, Comments) := match input with
  | Some _ => Some (Comments.none, Comments.none)
  | None => None

def blankRuleList: List RewriteRule → List RewriteRule
  | [] => []
  | [{ reverse, rule }, ..rest] => [{ reverse = blankReverse reverse, rule }, ..blankRuleList rest]

--| A rule set has a step of its own.
def Rules.blank: Rules → Rules
  | RuleList rules => RuleList (blankRuleList rules)
  | Repeatedly _ set => Repeatedly Comments.none set

def DefBody.blank: DefBody → DefBody
  | Primitive => Primitive
  | Assigned _ value => Assigned Comments.none value
  | Arms arms => Arms (blankArms arms)

-- Patterns.

def blankPattern: Pattern → Pattern
  | PatternWord kind word => PatternWord kind word.blank
  | PatternCtor name arguments => PatternCtor name.blank arguments
  | PatternCtorFields name fields => PatternCtorFields name.blank fields.blank
  | PatternRecord fields => PatternRecord fields.blank
  | PatternTuple open items comma close => PatternTuple open.blank items comma close.blank
  | PatternList open items comma tail close => PatternList open.blank items comma (blankAfterWord tail) close.blank
  | PatternNamed open name colonEq value close => PatternNamed open.blank name.blank colonEq.blank value close.blank
  | PatternOr first rest => PatternOr first (blankLinks rest)
  | PatternParen open inner close => PatternParen open.blank inner close.blank
  | PatternNegative minus number => PatternNegative minus.blank number.blank
  | PatternAbsurd open close => PatternAbsurd open.blank close.blank
  | PatternAppend start operator rest => PatternAppend start operator.blank rest

def FieldsPattern.blank (fields: FieldsPattern): FieldsPattern := { fields |
  open = fields.open.blank,
  fields = blankFieldPatterns fields.fields,
  rest = fields.rest.map Word.blank,
  close = fields.close.blank
}

def blankFieldPatterns: List FieldPattern → List FieldPattern
  | [] => []
  | [{ name, value }, ..rest] => [{ name = name.blank, value = blankAfterWord value }, ..blankFieldPatterns rest]

-- Headers and declarations.

def blankHeader (header: Header): Header := { header |
  exportKeyword = blankComments header.exportKeyword,
  opaqueKeyword = blankComments header.opaqueKeyword,
  keyword = Comments.none,
  name = header.name.blank,
  forallKeyword = header.forallKeyword.map Word.blank,
  params = blankGroups header.params,
  colon = Comments.none,
  decreasingClause = blankAfter header.decreasingClause,
  unfoldingClause = blankUnfolding header.unfoldingClause
}

def blankUnfolding (input: Option (Comments, List Word)): Option (Comments, List Word) := match input with
  | Some (_, names) => Some (Comments.none, blankWords names)
  | None => None

def blankDecl: Decl → Decl
  | Namespace _ name => Namespace Comments.none name.blank
  | Import _ path _ imported _ => Import Comments.none path.blank Comments.none imported.blank Comments.none
  | Definition attributes header body => Definition attributes header body.blank
  | Data attributes isInterface _ name params indices body =>
    Data attributes isInterface Comments.none name.blank (blankGroups params) (indices.map Indices.blank) body.blank
  | Ability _ name params _ operations =>
    Ability Comments.none name.blank (blankGroups params) Comments.none (blankOperations operations)
  | Test _ name _ body => Test Comments.none name.blank Comments.none body
  | RuleSetDecl _ name _ set => RuleSetDecl Comments.none name.blank Comments.none set

def Imported.blank: Imported → Imported
  | ImportAll _ => ImportAll Comments.none
  | ImportItems items => ImportItems (blankImportItems items)

def blankImportItems: List ImportItem → List ImportItem
  | [] => []
  | [{ name, alias }, ..rest] => [{ name = name.blank, alias = blankCommentsWord alias }, ..blankImportItems rest]

def Indices.blank (indices: Indices): Indices :=
  { indices | colon = Comments.none, steps = blankIndexSteps indices.steps }

def blankIndexSteps: List (Index, Word) → List (Index, Word)
  | [] => []
  | [(IndexBinder binder, arrow), ..rest] => [(IndexBinder binder.blank, arrow.blank), ..blankIndexSteps rest]
  | [(IndexType annotation, arrow), ..rest] => [(IndexType annotation, arrow.blank), ..blankIndexSteps rest]

def DataBody.blank: DataBody → DataBody
  | Abstract => Abstract
  | Synonym _ annotation => Synonym Comments.none annotation
  | RecordBody _ fields => RecordBody Comments.none fields
  | Sum _ constructors => Sum Comments.none (blankConstructors constructors)

def blankConstructors: List Constructor → List Constructor
  | [] => []
  | [{ bar, attributes, name, fields, result }, ..rest] => [
    { bar = Comments.none, attributes, name = name.blank, fields = blankParts fields, result = blankAfter result },
    ..blankConstructors rest
  ]

--| A part's fields have a step of their own.
def blankParts: List ConstructorPart → List ConstructorPart
  | [] => []
  | [PartGroup group, ..rest] => [PartGroup group.blank, ..blankParts rest]
  | [PartFields fields, ..rest] => [PartFields fields, ..blankParts rest]

def blankOperations: List Operation → List Operation
  | [] => []
  | [{ name, colon, annotation }, ..rest] =>
    [{ name = name.blank, colon = Comments.none, annotation }, ..blankOperations rest]

-- The lists with steps of their own.

def blankFields (fields: Fields): Fields :=
  { fields | open = Comments.none, fields = blankFieldList fields.fields, close = Comments.none }

def blankFieldList: List Field → List Field
  | [] => []
  | [{ attributes, name, colon, annotation, default }, ..rest] => [
    { attributes, name = name.blank, colon = Comments.none, annotation, default = blankAfter default },
    ..blankFieldList rest
  ]

def blankAttributes (attributes: Attributes): Attributes := { attributes |
  at = Comments.none,
  open = Comments.none,
  items = blankAttributeItems attributes.items,
  close = Comments.none
}

def blankAttributeItems: List Attribute → List Attribute
  | [] => []
  | [{ name, parts, argument }, ..rest] => [
    { name = name.blank, parts = blankDottedParts parts, argument = argument.map Word.blank },
    ..blankAttributeItems rest
  ]

--| A dotted name's parts, each after its `.`.
def blankDottedParts: List (Comments, Word) → List (Comments, Word)
  | [] => []
  | [(_, word), ..rest] => [(Comments.none, word.blank), ..blankDottedParts rest]

def blankRuleSet (set: RuleSet): RuleSet :=
  { set | open = Comments.none, rules = blankRuleList set.rules, close = Comments.none }

--| The traversal's steps that blank a whole file.
def blankSteps: Steps := {
  expr = blankExpr,
  pattern = blankPattern,
  header = blankHeader,
  decl = blankDecl,
  fields = blankFields,
  attributes = blankAttributes,
  ruleSet = blankRuleSet
}

--| The file with every comment blanked.
def SourceFile.withoutComments (file: SourceFile): SourceFile :=
  { decls = (file.apply blankSteps).decls, end = Comments.none }
