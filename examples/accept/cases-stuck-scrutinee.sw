-- A goal stuck on a value that both it and a hypothesis wait for, the
-- hypothesis inside a conjunction: `cases` splits the slot, then the
-- expression the pass rewrote, and every case computes (SW-3739, from the
-- toy formatter's shared traversal, where a lemma bridged them).
import Std (List)

type Op = | Plus | Times

type Expr =
  | Var (name: Text)
  | Num (digits: Text)
  | Str (written: Text)
  | Bracketed (open: Bool) (inner: Expr) (close: Bool)
  | ListLit (items: List Expr) (trailingComma: Bool)
  | Call (callee: Expr) (arguments: List Expr) (trailingComma: Bool)
  | Field (target: Expr) (name: Text)
  | Negate (operand: Expr)
  | Binary (operator: Op) (left: Expr) (right: Expr)
  | If (condition: Expr) (whenTrue: Expr) (whenFalse: Expr)

def Expr.isPostfix: Expr → Bool
  | Var _ => True
  | Num _ => True
  | Str _ => True
  | Bracketed _ _ _ => True
  | ListLit _ _ => True
  | Call _ _ _ => True
  | Field _ _ => True
  | _ => False

def Expr.isOperand: Expr → Bool
  | Negate _ => True
  | expr => expr.isPostfix

def Expr.isChain: Expr → Bool
  | Binary _ _ _ => True
  | expr => expr.isOperand

def Op.level: Op → Nat
  | Plus => 4
  | Times => 5

def Expr.chainLevel: Expr → Nat
  | Binary operator _ _ => operator.level
  | _ => 7

type Slot =
  | Whole
  | PostfixSlot
  | OperandSlot
  | LeftOf (level: Nat)
  | RightOf (level: Nat)

def Expr.fits (expr: Expr) (slot: Slot): Bool := match slot with
  | Whole => True
  | PostfixSlot => expr.isPostfix
  | OperandSlot => expr.isOperand
  | LeftOf level => expr.isChain && level <= expr.chainLevel
  | RightOf level => expr.isChain && level < expr.chainLevel

def Expr.withoutTrailingCommas: Expr → Expr
  | Bracketed o inner c => Bracketed o inner.withoutTrailingCommas c
  | ListLit items _ => ListLit (itemsWithout items) False
  | Call callee arguments _ => Call callee.withoutTrailingCommas (itemsWithout arguments) False
  | Field target name => Field target.withoutTrailingCommas name
  | Negate operand => Negate operand.withoutTrailingCommas
  | Binary op left right => Binary op left.withoutTrailingCommas right.withoutTrailingCommas
  | If c t f => If c.withoutTrailingCommas t.withoutTrailingCommas f.withoutTrailingCommas
  | other => other

def itemsWithout: List Expr → List Expr
  | [] => []
  | [x, ..xs] => [x.withoutTrailingCommas, ..itemsWithout xs]

def ShapedAt (slot: Slot) (expr: Expr): Prop := expr.isChain = True ∧ expr.fits slot = True

theorem commasFit ∀ (expr: Expr) (slot: Slot)
    (shaped: ShapedAt slot expr):
    expr.withoutTrailingCommas.fits slot = True :=
  cases

-- Both sides wait for `slot`: equal in every case, though neither computes.
theorem bracketedFits ∀ (o c: Bool) (i i': Expr) (slot: Slot):
    (Bracketed o i' c).fits slot = (Bracketed o i c).fits slot :=
  cases
