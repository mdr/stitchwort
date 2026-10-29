-- `+` computes on both sides (docs/core.md, "Natural numbers"; SW-787): its
-- definition counts down its first argument, and the kernel also counts down
-- the second when the first is unknown. So `x + 1` is `Succ x`, `x + 0` is
-- `x`, and a number on either side moves out: `x + 3` is `3 + x`. Only
-- commutativity and associativity of unknowns stay theorems
-- (reject/plus-comm-by-rfl.sw).

-- The four equations of `+`, by computation.
theorem zeroPlus (x: Nat): 0 + x = x := rfl
theorem plusZero (x: Nat): x + 0 = x := rfl
theorem succPlus (m: Nat) (n: Nat): Succ m + n = Succ (m + n) := rfl
theorem plusSucc (m: Nat) (n: Nat): m + Succ n = Succ (m + n) := rfl

-- What follows from them.
theorem plusOne (x: Nat): x + 1 = Succ x := rfl
theorem numberMoves (x: Nat): x + 3 = 3 + x := rfl
theorem numbersMoveOut (x: Nat) (y: Nat): x + (y + 2) = (x + y) + 2 := rfl
theorem bothSides (x: Nat) (y: Nat): (2 + x) + (y + 3) = 5 + (x + y) := rfl

-- An index written `n + 1` is `Succ n`, so it can be declared and matched
-- like one.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (n + 1)

-- No `VNil` arm: `0` can't be `n + 1`.
def head: Vec a (n + 1) → a
  | VCons x _ => x

def tail: Vec a (Succ n) → Vec a n
  | VCons _ xs => xs

-- Append with either order of lengths.
def append: Vec a n → Vec a m → Vec a (n + m)
  | VNil, ys => ys
  | VCons x xs, ys => VCons x (append xs ys)

def appendSwapped: Vec a n → Vec a m → Vec a (m + n)
  | VNil, ys => ys
  | VCons x xs, ys => VCons x (appendSwapped xs ys)

-- Snoc: the new length is `n + 1` either way round.
def snoc: Vec a n → a → Vec a (n + 1)
  | VNil, y => VCons y VNil
  | VCons x xs, y => VCons x (snoc xs y)

test "head of a snoc" := head (snoc (VCons 1 VNil) 2) == 1
