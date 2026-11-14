-- P4. A `decreasing` definition: branch equations through `f.unfold`.
-- P5. Its functional induction, written as the generator would state it,
-- and one theorem proved with it and without it.
import Std (Bool, Eq, List, Nat, Option, Void)

def gcd (a b: Nat): Nat
    decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

-- `gcd.eq.ifTrue` and `gcd.eq.ifFalse`.
theorem gcdEqIfTrue ∀ (a b: Nat) (h: b = 0): gcd a b = a := rewrite gcd.unfold a b in cases

theorem gcdEqIfFalse ∀ (a b: Nat) (h: b ≠ 0): gcd a b = gcd b (a % b) := rewrite gcd.unfold a b in cases

-- `gcd.induct`: one case per branch, the recursive call's motive as a hypothesis.
theorem gcdInduct ∀ (motive: Nat → Nat → Prop) (case1: (a: Nat) → (b: Nat) → b = 0 → motive a b)
    (case2: (a: Nat) → (b: Nat) → b ≠ 0 → motive b (a % b) → motive a b) (a b: Nat):
    motive a b
    decreasing b
:=
  if h: b = 0 then case1 a b h
  else case2 a b h (gcdInduct motive case1 case2 b (a % b) [decreasing := Nat.modLess a b h])

-- With it.
theorem gcdZero ∀ (a b: Nat): gcd a b = 0 → a = 0 :=
  gcdInduct
    (a b => gcd a b = 0 → a = 0)
    (a b z g => rewrite gcdEqIfTrue a b z at g in g)
    (a b nz ih g => Void.exfalso (nz (ih (rewrite gcdEqIfFalse a b nz at g in g))))
    a
    b

-- Without it: the theorem recurses on the same measure.
theorem gcdZeroDirect ∀ (a b: Nat) (g: gcd a b = 0): a = 0
    decreasing b
:=
  if h: b = 0 then rewrite gcdEqIfTrue a b h at g in g
  else
    Void.exfalso (h (gcdZeroDirect b (a % b) (rewrite gcdEqIfFalse a b h at g in g) [decreasing := Nat.modLess a b h]))
