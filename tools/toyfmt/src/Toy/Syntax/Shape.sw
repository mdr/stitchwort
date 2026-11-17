--| Which forms of expression may stand where: the parser reads a postfix
--| expression as a callee or a field's target, an operand after `-`,
--| and a chain of operators no looser than an operator's level on its
--| sides. `Shaped` (`ExpressionProofs.sw`) is stated with these, and P3
--| (`Fmt/Passes.sw`) drops a bracket pair only where they allow its
--| content.

namespace Toy.Syntax
import Std (Bool, Nat)

--| An expression that `atom` and `suffixesFrom` read: an atom with its
--| calls and fields.
def Expr.isPostfix: Expr → Bool
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ _ _ => True
  | ListLiteral _ _ _ _ => True
  | Call _ _ _ _ _ => True
  | Field _ _ _ _ => True
  | _ => False

--| An operand of an operator chain: a postfix expression, or `-` before
--| an operand.
def Expr.isOperand: Expr → Bool
  | Negate _ _ => True
  | expr => expr.isPostfix

--| An operator chain or an operand: any expression but an `if`, which
--| stands only as a whole expression.
def Expr.isChain: Expr → Bool
  | Binary _ _ _ _ => True
  | expr => expr.isOperand

--| The level of a chain's outermost operator; 7, past every level, for an
--| operand.
def Expr.chainLevel: Expr → Nat
  | Binary operator _ _ _ => operator.level
  | _ => 7
