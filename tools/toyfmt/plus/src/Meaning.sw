--| What formatting must keep (toy-plus-plus.md §2, D3635, D3643): a
--| file's tree in plain form, with each freedom the formatter has set to
--| one fixed spelling. Two files are the same program when their
--| meanings are equal.
--|
--| Nothing proves this definition right: the pass theorems are stated
--| against it. It is meant to be read case by case.

namespace Toy.Plus
import Toy.Syntax (Comment, Comments, Operator, Spaced)
import Std (Bool, List, NonEmptyList, Option, Text)

--| A plain tree is wrapped so that it can't be printed by mistake: it
--| need not have the parser's shape (its grouping is in the tree, not in
--| brackets).
type Meaning = { plain: SourceFile }

def SourceFile.meaning (file: SourceFile): Meaning := { plain = { declarations = plainDeclarations file.declarations } }

def holdsNone (comments: Comments): Bool := comments.above.isEmpty && comments.after.isNone

def Expr.plain: Expr → Expr
  -- A pair that holds no comment is forgotten: the tree's shape says how
  -- the expression groups. A pair that holds one is kept, with it.
  | Bracketed open inner close =>
    if holdsNone open && holdsNone close then inner.plain else Bracketed open inner.plain close
  | ListLiteral open items _ close => ListLiteral open (plainItems items) False close
  | Call callee open arguments _ close => Call callee.plain open (plainItems arguments) False close
  | Field target dot name nameComments => Field target.plain dot name nameComments
  | Negate minus operand => Negate minus operand.plain
  | Binary operator sign left right => Binary operator sign left.plain right.plain
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If ifComments condition.plain thenComments whenTrue.plain elseComments whenFalse.plain
  | leaf => leaf

def plainItems: List Expr → List Expr
  | [] => []
  | [first, ..rest] => [first.plain, ..plainItems rest]

def Body.plain: Body → Body
  | { statements } => { statements = plainLines statements }

def plainLines: List (Spaced Statement) → List (Spaced Statement)
  | [] => []
  | [{ blankBefore, line }, ..rest] => [{ blankBefore, line = line.plain }, ..plainLines rest]

def Statement.plain: Statement → Statement
  | Let letComments name nameComments equals body => Let letComments name nameComments equals body.plain
  | Bare value => Bare value.plain
  | note => note

def TypeExpr.plain: TypeExpr → TypeExpr
  | TypeBracketed open inner close =>
    if holdsNone open && holdsNone close then inner.plain else TypeBracketed open inner.plain close
  | name => name

--| The type's name alone: no brackets, no comments.
def TypeExpr.bare: TypeExpr → TypeExpr
  | TypeBracketed _ inner _ => inner.bare
  | TypeName name _ => TypeName name Comments.none

--| One group for each name. The group's own `:` and type, with their
--| comments, stay with its last name; the names before it get the bare
--| type.
def ParameterGroup.plain: ParameterGroup → List ParameterGroup
  | Untyped parameter => [Untyped parameter]
  | Typed names colon annotation => splitGroup names.head names.tail colon annotation.plain

def splitGroup (first: Named) (others: List Named) (colon: Comments) (annotation: TypeExpr): List ParameterGroup :=
  match others with
    | [] => [Typed (NonEmptyList.singleton first) colon annotation]
    | [next, ..rest] =>
      [Typed (NonEmptyList.singleton first) Comments.none annotation.bare, ..splitGroup next rest colon annotation]

def plainGroups: List ParameterGroup → List ParameterGroup
  | [] => []
  | [group, ..rest] => group.plain ++ plainGroups rest

def Declaration.plain: Declaration → Declaration
  | Function fnComments name nameComments takes open groups _ close equals body =>
    Function fnComments name nameComments
      (Some (takes.getOrElse Comments.none))
      open
      (plainGroups groups)
      False
      close
      equals
      body.plain
  | Value letComments name nameComments equals body => Value letComments name nameComments equals body.plain
  | note => note

def plainDeclarations: List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] => [{ blankBefore, line = line.plain }, ..plainDeclarations rest]
