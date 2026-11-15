--| How many comments a tree holds: the parser compares a declaration's
--| with the comments among its tokens, to find one it couldn't place.

namespace Toy.Syntax
import Std (List, Option, Text)

def Declaration.comments: Declaration → Nat
  | Function _ _ body => body.comments
  | Value _ body => body.comments
  | DeclarationNote _ => 1
  | AsWritten _ => 0

def Body.comments: Body → Nat
  | { statements } => statementComments statements

def statementComments: List (Spaced Statement) → Nat
  | [] => 0
  | [{ line, .. }, ..rest] => line.comments + statementComments rest

def Statement.comments: Statement → Nat
  | Let _ body => body.comments
  | Bare value trailing => value.comments + trailingCount trailing
  | StatementNote _ => 1

def trailingCount: Option Comment → Nat
  | None => 0
  | Some _ => 1

def Expr.comments: Expr → Nat
  | Bracketed inner => inner.comments
  | ListLiteral items => itemComments items
  | Call callee arguments => callee.comments + itemComments arguments
  | Field target _ => target.comments
  | Negate operand => operand.comments
  | Binary _ left right => left.comments + right.comments
  | If condition whenTrue whenFalse => condition.comments + whenTrue.comments + whenFalse.comments
  | _ => 0

def itemComments: List Item → Nat
  | [] => 0
  | [{ comments, value, trailing }, ..rest] =>
    comments.length + value.comments + trailingCount trailing + itemComments rest
