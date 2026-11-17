--| The passes `format` runs between parsing and printing
--| (toy-plus-plus.md §3.2), in order: P1 `withTakes`, then P2
--| `withoutTrailingCommas`. Each is a function on trees, right on every
--| tree, and a tree is tidy for a pass when the pass leaves it alone.
--| P3 (spare brackets) and P4 (merged parameter groups) come at stages
--| T5 and T6.

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

--| The passes, in order.
def SourceFile.tidy (file: SourceFile): SourceFile := file.withTakes.withoutTrailingCommas
