--| One traversal for the passes that rewrite expressions
--| (toy-plus-plus.md §3.4): `Expr.traverse step position` rewrites
--| bottom-up, each expression directly inside first, then `step` at the
--| node itself, told where the node stands. A pass is a `step`, and
--| `Fmt/TraverseProofs.sw` proves once for every `step` that a fact the
--| step keeps at one node, the traversal keeps for the whole tree.

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Bool, List, Nat)

--| What an expression's place asks of its form: nothing (`Whole`: a
--| body's expression, an item, a condition, a bracket pair's content), a
--| postfix expression (a callee, a field's target), an operand (after
--| `-`), or a side of an operator of `level`.
type Slot =
  | Whole
  | PostfixSlot
  | OperandSlot
  | LeftOf (level: Nat)
  | RightOf (level: Nat)

--| Where an expression stands: its slot, and whether a bracket pair is
--| open around it (inside one, own-line comments above a statement's
--| first token don't make blocks).
type Position = { bracketed: Bool, slot: Slot }

--| Whether the parser reads `expr` in `slot` as it stands: the forms
--| `Shaped` allows there.
def Expr.fits (expr: Expr) (slot: Slot): Bool := match slot with
  | Whole => True
  | PostfixSlot => expr.isPostfix
  | OperandSlot => expr.isOperand
  | LeftOf level => expr.isChain && level <= expr.chainLevel
  | RightOf level => expr.isChain && level < expr.chainLevel

--| `expr` rewritten bottom-up: each expression inside it first, then
--| `step` at `expr` itself, told where it stands.
def Expr.traverse (expr: Expr) (step: Position → Expr → Expr) (position: Position): Expr :=
  step position (expr.traverseInside step position.bracketed)

--| `expr` with each expression directly inside it traversed, each told
--| where it stands.
def Expr.traverseInside (expr: Expr) (step: Position → Expr → Expr) (bracketed: Bool): Expr := match expr with
  | Bracketed open inner close => Bracketed open (inner.traverse step { bracketed = True, slot = Whole }) close
  | ListLiteral open items trailingComma close => ListLiteral open (traverseItems step items) trailingComma close
  | Call callee open arguments trailingComma close =>
    Call (callee.traverse step { bracketed, slot = PostfixSlot }) open (traverseItems step arguments) trailingComma close
  | Field target dot name nameComments =>
    Field (target.traverse step { bracketed, slot = PostfixSlot }) dot name nameComments
  | Negate minus operand => Negate minus (operand.traverse step { bracketed, slot = OperandSlot })
  | Binary operator sign left right =>
    Binary operator sign
      (left.traverse step { bracketed, slot = LeftOf operator.level })
      (right.traverse step { bracketed, slot = RightOf operator.level })
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If ifComments
      (condition.traverse step { bracketed, slot = Whole })
      thenComments
      (whenTrue.traverse step bracketed)
      elseComments
      (whenFalse.traverse step bracketed)
  | leaf => leaf

def traverseItems (step: Position → Expr → Expr): List Expr → List Expr
  | [] => []
  | [first, ..rest] => [first.traverse step { bracketed = True, slot = Whole }, ..traverseItems step rest]

def Body.traverse (body: Body) (step: Position → Expr → Expr) (bracketed: Bool): Body := match body with
  | { statements } => { statements = traverseLines step bracketed statements }

def traverseLines (step: Position → Expr → Expr) (bracketed: Bool):
    List (Spaced Statement) → List (Spaced Statement)
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [{ blankBefore, line = line.traverse step bracketed }, ..traverseLines step bracketed rest]

def Statement.traverse (line: Statement) (step: Position → Expr → Expr) (bracketed: Bool): Statement :=
  match line with
    | Let letComments name nameComments equals body => Let letComments name nameComments equals (body.traverse step False)
    | Bare value => Bare (value.traverse step { bracketed, slot = Whole })
    | note => note

--| The declaration with its body traversed.
def Declaration.traverseBody (line: Declaration) (step: Position → Expr → Expr): Declaration := match line with
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Function fnComments name nameComments takes open parameters trailingComma close equals (body.traverse step False)
  | Value letComments name nameComments equals body =>
    Value letComments name nameComments equals (body.traverse step False)
  | note => note

def traverseDeclarations (step: Position → Expr → Expr) (declare: Declaration → Declaration):
    List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [{ blankBefore, line = declare (line.traverseBody step) }, ..traverseDeclarations step declare rest]

--| Every expression of the file traversed with `step`, and then every
--| declaration rewritten by `declare` (which sees its body traversed).
def SourceFile.traverse (file: SourceFile) (step: Position → Expr → Expr) (declare: Declaration → Declaration):
    SourceFile :=
  { declarations = traverseDeclarations step declare file.declarations }
