--| What the passes and the parser ask of an expression's shape, as
--| functions: which forms may stand where (P3 drops a bracket pair only
--| where its content may stand without it), where an expression's first
--| and last tokens' comments are, and route (A) for `Settled`
--| (toy-plus-plus.md §3.1): the parser builds each closer through
--| `closed`, so that every tree it gives is `Settled` by construction.
--|
--| `isPostfix`, `isOperand`, `isChain` and `chainLevel` are the toy's
--| (`Syntax/ExpressionProofs.sw`), for this tree: P3 makes them program
--| code.

namespace Toy.Plus
import Toy.Syntax (Comment, Comments, Operator, Spaced)
import Std (Bool, List, NonEmptyList, Option, Text)

def Expr.isPostfix: Expr → Bool
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ _ _ => True
  | ListLiteral _ _ _ _ => True
  | Call _ _ _ _ _ => True
  | Field _ _ _ _ => True
  | _ => False

def Expr.isOperand: Expr → Bool
  | Negate _ _ => True
  | expr => expr.isPostfix

--| Any expression but an `if`, which stands only as a whole expression.
def Expr.isChain: Expr → Bool
  | Binary _ _ _ _ => True
  | expr => expr.isOperand

--| The level of a chain's outermost operator; 7, past every level, for an
--| operand.
def Expr.chainLevel: Expr → Nat
  | Binary operator _ _ _ => operator.level
  | _ => 7

--| The own-line comments above the expression's leftmost token.
def Expr.firstAbove: Expr → List Comment
  | Var _ comments => comments.above
  | NumberLiteral _ comments => comments.above
  | StringLiteral _ comments => comments.above
  | Bracketed open _ _ => open.above
  | ListLiteral open _ _ _ => open.above
  | Call callee _ _ _ _ => callee.firstAbove
  | Field target _ _ _ => target.firstAbove
  | Negate minus _ => minus.above
  | Binary _ _ left _ => left.firstAbove
  | If ifComments _ _ _ _ _ => ifComments.above

--| Whether the token before a list's or a call's closer has a trailing
--| comment: the last item's last token, or the opening bracket's with no
--| items.
def lastEndsWithComment (open: Comments): List Expr → Bool
  | [] => open.after.isSome
  | [last] => last.endsWithComment
  | [_, ..rest] => lastEndsWithComment open rest

--| Whether the expression's last token has a trailing comment.
def Expr.endsWithComment: Expr → Bool
  | Var _ comments => comments.after.isSome
  | NumberLiteral _ comments => comments.after.isSome
  | StringLiteral _ comments => comments.after.isSome
  | Bracketed _ _ close => close.after.isSome
  | ListLiteral _ _ _ close => close.after.isSome
  | Call _ _ _ _ close => close.after.isSome
  | Field _ _ _ nameComments => nameComments.after.isSome
  | Negate _ operand => operand.endsWithComment
  | Binary _ _ _ right => right.endsWithComment
  | If _ _ _ _ _ whenFalse => whenFalse.endsWithComment

def Body.endsWithComment: Body → Bool
  | { statements } => linesEndWithComment statements

def linesEndWithComment: List (Spaced Statement) → Bool
  | [] => False
  | [{ line, .. }] => line.endsWithComment
  | [_, ..rest] => linesEndWithComment rest

def Statement.endsWithComment: Statement → Bool
  | Bare value => value.endsWithComment
  | Let _ _ _ _ body => body.endsWithComment
  | StatementNote _ => False

def TypeExpr.endsWithComment: TypeExpr → Bool
  | TypeName _ comments => comments.after.isSome
  | TypeBracketed _ _ close => close.after.isSome

--| Whether the token before a parameter list's `)` has a trailing
--| comment.
def groupsEndWithComment (open: Comments): List ParameterGroup → Bool
  | [] => open.after.isSome
  | [Untyped parameter] => parameter.comments.after.isSome
  | [Typed _ _ annotation] => annotation.endsWithComment
  | [_, ..rest] => groupsEndWithComment open rest

--| Whether a closer may hold the trailing comment it has: rule N leaves
--| one on a closer only below own-line comments of the closer's, or
--| where the token before the closer has a trailing comment already
--| (`before`). In both cases the closer is printed on a line of its own.
def settledCloser (before: Bool) (close: Comments): Bool := close.after.isNone || not close.above.isEmpty || before

-- Route (A). Rule N again, on the tree: `receive` puts a comment written
-- after an expression on the token rule N gives it to, through the
-- expression's closers. On trees read from settled tokens `closed` and
-- its like change nothing (not proved: the goldens and the disturber are
-- the evidence, as for `Layout.headed`); what is proved is that their
-- results are `Settled`.

--| The expression with `comment` after it, on the token rule N gives it
--| to. For an expression that doesn't end with a comment.
def Expr.receive (expr: Expr) (comment: Comment): Expr := match expr with
  | Var name comments => Var name { comments | after = Some comment }
  | NumberLiteral digits comments => NumberLiteral digits { comments | after = Some comment }
  | StringLiteral written comments => StringLiteral written { comments | after = Some comment }
  | Bracketed open inner close =>
    if close.above.isEmpty && not inner.endsWithComment then Bracketed open (inner.receive comment) close
    else Bracketed open inner { close | after = Some comment }
  | ListLiteral open items trailingComma close =>
    let (settledOpen, settledItems, settledClose) := receiveList comment open items close
    ListLiteral settledOpen settledItems trailingComma settledClose
  | Call callee open arguments trailingComma close =>
    let (settledOpen, settledArguments, settledClose) := receiveList comment open arguments close
    Call callee settledOpen settledArguments trailingComma settledClose
  | Field target dot name nameComments => Field target dot name { nameComments | after = Some comment }
  | Negate minus operand => Negate minus (operand.receive comment)
  | Binary operator sign left right => Binary operator sign left (right.receive comment)
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If ifComments condition thenComments whenTrue elseComments (whenFalse.receive comment)

--| A list's or a call's brackets and items with `comment` after the
--| closer, where rule N puts it: on the closer below its own-line
--| comments, else on the token before it, else (that token has a comment)
--| on the closer.
def receiveList (comment: Comment) (open: Comments) (items: List Expr) (close: Comments):
    (Comments, List Expr, Comments) :=
  if not close.above.isEmpty || lastEndsWithComment open items then (open, items, { close | after = Some comment })
  else
    match items with
      | [] => ({ open | after = Some comment }, [], close)
      | [first, ..rest] => (open, receiveLast comment first rest, close)

def receiveLast (comment: Comment) (first: Expr) (rest: List Expr): List Expr := match rest with
  | [] => [first.receive comment]
  | [next, ..others] => [first, ..receiveLast comment next others]

def Body.receive (body: Body) (comment: Comment): Body := match body with
  | { statements } => { statements = receiveLines comment statements }

def receiveLines (comment: Comment): List (Spaced Statement) → List (Spaced Statement)
  | [] => []
  | [{ blankBefore, line }] => [{ blankBefore, line = line.receive comment }]
  | [first, ..rest] => [first, ..receiveLines comment rest]

def Statement.receive (line: Statement) (comment: Comment): Statement := match line with
  | Bare value => Bare (value.receive comment)
  | Let letComments name nameComments equals body => Let letComments name nameComments equals (body.receive comment)
  | note => note

--| `Bracketed open inner close` as the parser builds it: a comment after
--| the `)` that rule N would have moved is moved.
def closed (open: Comments) (inner: Expr) (close: Comments): Expr := match close.after with
  | Some comment if not (settledCloser inner.endsWithComment close) =>
    Bracketed open (inner.receive comment) { close | after = None }
  | _ => Bracketed open inner close

--| A list's or a call's brackets and items as the parser builds them,
--| given whether a comma came after the last item: as `closed`. After a
--| trailing comma, a comment that can't move back goes above the closer,
--| as rule N puts a comma's.
def closedList (open: Comments) (items: List Expr) (trailingComma: Bool) (close: Comments):
    (Comments, List Expr, Comments) :=
  match close.after with
    | Some comment if not (settledCloser (not trailingComma && lastEndsWithComment open items) close) =>
      if lastEndsWithComment open items then (open, items, { above = [comment], after = None })
      else receiveList comment open items { close | after = None }
    | _ => (open, items, close)
