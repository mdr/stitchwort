-- Numbers are stored compactly, and arithmetic on them is native, so large
-- numbers are cheap. They still mean `Succ (Succ … Zero)`: matching on one
-- takes the `Zero` or `Succ` branch, and `3` is the same as `Succ 2`.

import Std (Nat)

-- Checked by computing both sides, natively.
theorem bigSum: 1000000 + 1000000 = 2000000 := rfl

theorem bigProduct: 123456789 * 987654321 = 121932631112635269 := rfl

theorem literalIsSucc: 1000000 = Succ 999999 := rfl

-- Matching on a literal takes the `Succ` branch without counting down.
def isZero: Nat → Bool
  | Zero => True
  | Succ n => False

test "a big number isn't zero" := not (isZero 1000000000000)

-- Unification works through literals: `Succ k` matches `5000` with `k = 4999`.
def predOf: (n: Nat) → Nat
  | Succ k => k
  | Zero => 0

test "pred" := Nat.equal (predOf 5000) 4999
test "division" := Nat.equal (1000000 / 7) 142857
test "remainder" := Nat.equal (1000000 % 7) 1
test "subtraction stops at zero" := Nat.equal (3 - 5) 0
test "comparison" := Nat.leq 99999999999 100000000000

-- `auto` decides propositions about big numbers natively too.
def under (n: Nat): [auto ok: n < 100000000000] → Nat := n

test "auto" := Nat.equal (under 99999999999) 99999999999
test "equal" := Nat.equal (if h: 123456789 = 123456789 then 1 else 0) 1
test "not equal" := Nat.equal (if h: 123456789 = 123456788 then 1 else 0) 0

-- Literals can be any size, not just 64 bits.
theorem hugeLiteral: 18446744073709551616 * 18446744073709551616 = 340282366920938463463374607431768211456 := rfl

test "huge subtraction" := Nat.equal (340282366920938463463374607431768211456 - 18446744073709551616) 340282366920938463444927863358058659840

-- A big number plus an unknown stays compact (this used to expand into a
-- million `Succ`s and crash the checker).
def shifted (x: Nat): List Nat := [1000000 + x]

theorem shiftSucc (x: Nat): 1000000 + Succ x = Succ (1000000 + x) := rfl

-- `-`, `<=` and `Nat.equal` take off shared `Succ`s in one step.
theorem subShared (x: Nat): (500000 + x) - 500000 = x := rfl

theorem leqShared (x: Nat): Nat.leq (1000000 + x) (1000000 + Succ x) = Nat.leq x (Succ x) := rfl

def headOr0: List Nat → Nat
  | Nil => 0
  | Cons x _ => x

test "shifted" := headOr0 (shifted 5) == 1000005
