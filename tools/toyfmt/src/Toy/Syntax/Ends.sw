--| Where a construct's last token's trailing comment is, and what rule N
--| (`Settle.sw`) leaves on a closing bracket.
--|
--| Rule N moves a comment written after a closing bracket back to the
--| token before it, unless the bracket has own-line comments above it or
--| that token has a trailing comment already. So in a tree read from
--| settled tokens a closing bracket holds a trailing comment only in
--| those two cases (`settledCloser`). The parser builds every closing
--| bracket's comments through `Comments.closing`, which makes that a fact
--| about each tree it gives, with no account of which token was read
--| last.

namespace Toy.Syntax
import Std (Bool, List, NonEmptyList, Option)

--| Whether the expression's last token has a trailing comment.
def Expr.endsWithComment: Expr → Bool
  | Var _ comments => comments.after.isSome
  | NumberLiteral _ comments => comments.after.isSome
  | StringLiteral _ comments => comments.after.isSome
  | Bracketed _ _ close => close.after.isSome
  | ListLiteral _ _ close => close.after.isSome
  | Call _ _ _ close => close.after.isSome
  | Field _ _ _ nameComments => nameComments.after.isSome
  | Negate _ operand => operand.endsWithComment
  | Binary _ _ _ right => right.endsWithComment
  | If _ _ _ _ _ whenFalse => whenFalse.endsWithComment

def Body.endsWithComment: Body → Bool
  | { statements } => statementsEndWithComment statements

--| Whether the last of the statements ends in a trailing comment.
def statementsEndWithComment: List (Spaced Statement) → Bool
  | [] => False
  | [{ line, .. }] => line.endsWithComment
  | [_, ..rest] => statementsEndWithComment rest

def Statement.endsWithComment: Statement → Bool
  | Bare value => value.endsWithComment
  | Let _ _ _ _ body => body.endsWithComment
  | StatementNote _ => False

--| Whether the token before a list's or a call's closing bracket has a
--| trailing comment: the last item's last token, or the opening bracket
--| with no items.
def itemsEndWithComment (open: Comments): List Expr → Bool
  | [] => open.after.isSome
  | [last] => last.endsWithComment
  | [_, ..rest] => itemsEndWithComment open rest

def TypeExpr.endsWithComment: TypeExpr → Bool
  | TypeName _ comments => comments.after.isSome
  | TypeBracketed _ _ close => close.after.isSome

def ParameterGroup.endsWithComment: ParameterGroup → Bool
  | Untyped parameter => parameter.comments.after.isSome
  | Typed _ _ annotation => annotation.endsWithComment

--| Whether the token before a parameter list's `)` has a trailing
--| comment: the last group's last token, or the `(` with no parameters.
def groupsEndWithComment (open: Comments): List ParameterGroup → Bool
  | [] => open.after.isSome
  | [last] => last.endsWithComment
  | [_, ..rest] => groupsEndWithComment open rest

--| Whether a closing bracket may hold the trailing comment it has, where
--| `before` says the token before it has one: rule N leaves a comment on
--| a closing bracket only below own-line comments of the bracket's, or
--| after a token with a trailing comment of its own.
def settledCloser (before: Bool) (close: Comments): Bool := close.after.isNone || not close.above.isEmpty || before

--| A closing bracket's comments as the tree keeps them, where `before`
--| says the token before it has a trailing comment. A trailing comment
--| rule N would have moved goes above the bracket, where it stays. On
--| settled tokens there is none, so this changes nothing the parser
--| reads; it makes `settledCloser` a fact about the tree.
def Comments.closing (close: Comments) (before: Bool): Comments := match close.after with
  | Some comment if not (settledCloser before close) => { above = [comment], after = None }
  | _ => close
