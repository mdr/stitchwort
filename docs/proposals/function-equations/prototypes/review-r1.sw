-- Review R1: an overlap hypothesis on an indexed family. Arm 1 fixes the
-- index, so `v = VNil` relates two different types.
import Std (Nat, Void, Eq)

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def short: Vec Nat n → Nat
  | VNil => 0
  | VCons x VNil => 1
  | v => 2

-- Lean's form, as the note states it for arms: ill-typed here.
theorem shortEq3 ∀ (n: Nat) (v: Vec Nat n) (notArm1: v = VNil → Void): short v = 2 :=
  cases
