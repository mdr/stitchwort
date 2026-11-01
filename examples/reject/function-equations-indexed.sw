-- expect-error: E-NO-EQUATION
-- Arm 1 fixes the index (`Vec Nat 0`), so arm 3's overlap hypothesis `v =
-- VNil → Void` would compare a `Vec Nat n` with a `Vec Nat 0`: `short.eq3`
-- isn't generated (D2185). `short.eq1` and `short.eq2` are.
import Std (Nat)

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def short: Vec Nat n → Nat
  | VNil => 0
  | VCons x VNil => 1
  | v => 2

theorem shortEmpty: short VNil = 0 := short.eq1

theorem shortOther [n: Nat] (v: Vec Nat n): short v = 2 := short.eq3 v
