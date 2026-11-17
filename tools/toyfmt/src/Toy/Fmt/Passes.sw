--| The passes `format` runs between parsing and printing
--| (toy-plus-plus.md §3.2), in order: P1 `withTakes`, P2
--| `withoutTrailingCommas`, then P3 `withoutSpareBrackets`. Each is a
--| function on trees, right on every tree, and a tree is tidy for a pass
--| when the pass leaves it alone. P4 (merged parameter groups) comes at
--| stage T6.

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Bool, List, Option, Text)

-- P1: `takes`, written on every function that has parameters.

--| The `takes` a function with `parameters` is printed with: one with no
--| comments where none was written, if there are parameters.
def takesFor (takes: Option Comments) (parameters: List ParameterGroup): Option Comments := match parameters with
  | [] => takes
  | [_, .._] => Some (takes.getOrElse Comments.none)

def Declaration.withTakes: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Function fnComments name nameComments (takesFor takes parameters) open parameters trailingComma close equals body
  | other => other

def declarationsWithTakes: List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] => [{ blankBefore, line = line.withTakes }, ..declarationsWithTakes rest]

def SourceFile.withTakes (file: SourceFile): SourceFile := { declarations = declarationsWithTakes file.declarations }

-- P2: no trailing commas. Rule N has left no comment on a comma, so
-- dropping one loses nothing.

def Expr.withoutTrailingCommas: Expr → Expr
  | Bracketed open inner close => Bracketed open inner.withoutTrailingCommas close
  | ListLiteral open items _ close => ListLiteral open (itemsWithoutTrailingCommas items) False close
  | Call callee open arguments _ close =>
    Call callee.withoutTrailingCommas open (itemsWithoutTrailingCommas arguments) False close
  | Field target dot name nameComments => Field target.withoutTrailingCommas dot name nameComments
  | Negate minus operand => Negate minus operand.withoutTrailingCommas
  | Binary operator sign left right => Binary operator sign left.withoutTrailingCommas right.withoutTrailingCommas
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If ifComments condition.withoutTrailingCommas thenComments whenTrue.withoutTrailingCommas elseComments
        whenFalse.withoutTrailingCommas
  | leaf => leaf

def itemsWithoutTrailingCommas: List Expr → List Expr
  | [] => []
  | [value, ..rest] => [value.withoutTrailingCommas, ..itemsWithoutTrailingCommas rest]

def Body.withoutTrailingCommas: Body → Body
  | { statements } => { statements = linesWithoutTrailingCommas statements }

def linesWithoutTrailingCommas: List (Spaced Statement) → List (Spaced Statement)
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [{ blankBefore, line = line.withoutTrailingCommas }, ..linesWithoutTrailingCommas rest]

def Statement.withoutTrailingCommas: Statement → Statement
  | Let letComments name nameComments equals body => Let letComments name nameComments equals body.withoutTrailingCommas
  | Bare value => Bare value.withoutTrailingCommas
  | StatementNote comment => StatementNote comment

def Declaration.withoutTrailingCommas: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters _ close equals body =>
    Function fnComments name nameComments takes open parameters False close equals body.withoutTrailingCommas
  | Value letComments name nameComments equals body =>
    Value letComments name nameComments equals body.withoutTrailingCommas
  | DeclarationNote comment => DeclarationNote comment

def declarationsWithoutTrailingCommas: List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [{ blankBefore, line = line.withoutTrailingCommas }, ..declarationsWithoutTrailingCommas rest]

def SourceFile.withoutTrailingCommas (file: SourceFile): SourceFile :=
  { declarations = declarationsWithoutTrailingCommas file.declarations }

-- P3: no spare brackets.

--| Whether the expression, read inside brackets, reads the same outside
--| them: there an own-line comment above the first token of a statement
--| in an `if`'s branch would start a block.
def Expr.standsOutside: Expr → Bool
  | Call callee _ _ _ _ => callee.standsOutside
  | Field target _ _ _ => target.standsOutside
  | Negate _ operand => operand.standsOutside
  | Binary _ _ left right => left.standsOutside && right.standsOutside
  | If _ condition _ whenTrue _ whenFalse =>
    condition.standsOutside && whenTrue.standsOutside && whenFalse.standsOutside
  | _ => True

def Body.standsOutside: Body → Bool
  | { statements } => linesStandOutside statements

def linesStandOutside: List (Spaced Statement) → Bool
  | [] => True
  | [{ line, .. }, ..rest] => line.standsOutside && linesStandOutside rest

def Statement.standsOutside: Statement → Bool
  | Bare value => value.firstAbove.isEmpty && value.standsOutside
  | _ => True

--| Whether the pair `( inner )` can go at `position`: neither bracket
--| holds a comment, no own-line comment is above the content's first
--| token, the content is read as it stands in the pair's place
--| (precedence), and outside brackets it reads the same (`standsOutside`).
def spare (position: Position) (open: Comments) (inner: Expr) (close: Comments): Bool :=
  open.isNone
    && close.isNone
    && inner.firstAbove.isEmpty
    && inner.fits position.slot
    && (position.bracketed || inner.standsOutside)

--| P3's step: a spare pair is replaced by its content.
def dropPair (position: Position) (expr: Expr): Expr := match expr with
  | Bracketed open inner close => if spare position open inner close then inner else Bracketed open inner close
  | other => other

--| A type's brackets with no comments go: a type is a name wherever it
--| stands.
def TypeExpr.withoutSpareBrackets: TypeExpr → TypeExpr
  | TypeBracketed open inner close =>
    if open.isNone && close.isNone then inner.withoutSpareBrackets
    else TypeBracketed open inner.withoutSpareBrackets close
  | name => name

def ParameterGroup.withoutSpareBrackets: ParameterGroup → ParameterGroup
  | Typed names colon annotation => Typed names colon annotation.withoutSpareBrackets
  | untyped => untyped

def groupsWithoutSpareBrackets: List ParameterGroup → List ParameterGroup
  | [] => []
  | [group, ..rest] => [group.withoutSpareBrackets, ..groupsWithoutSpareBrackets rest]

def Declaration.withoutSpareTypeBrackets: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Function fnComments name nameComments takes open
      (groupsWithoutSpareBrackets parameters)
      trailingComma
      close
      equals
      body
  | other => other

--| P3: no bracket pair that could go is left. Pairs nested in each other
--| go in one run: the traversal drops the inner pair before it looks at
--| the outer.
def SourceFile.withoutSpareBrackets (file: SourceFile): SourceFile :=
  file.traverse dropPair (line => line.withoutSpareTypeBrackets)

--| The passes, in order.
def SourceFile.tidy (file: SourceFile): SourceFile := file.withTakes.withoutTrailingCommas.withoutSpareBrackets
