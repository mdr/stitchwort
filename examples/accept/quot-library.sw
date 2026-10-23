-- The library's quotient lemmas (docs/proposals/map-equality.md §8.6-§8.8,
-- test A2), from `std/Quot/Quot.sw`, which loads when a program uses one:
--
-- - `Quot.funext`: functions whose results are data, and that agree at every
--   input, are equal;
-- - `Quot.funextProp`: the same for functions whose results are proofs, by
--   storing each proof in a `ProofBox`;
-- - `Quot.exactDec`: when a `Bool` function decides an equivalence,
--   `Quot.mk x = Quot.mk y` gives back that `x` and `y` are related.
import Std (Bool, DecEq, Decidable, Eq, Iff, ProofBox, Quot)

def double (n: Nat): Nat := n + n
def twice (n: Nat): Nat := 2 * n

theorem doubleIsTwice: double = twice :=
  Quot.funext Nat (n => Nat) double twice (n => omega)

-- Two proofs of the same `(n: Nat) -> n + 0 = n`, equal as functions.
theorem plusZero (f: (n: Nat) -> n + 0 = n) (g: (n: Nat) -> n + 0 = n): f = g :=
  Quot.funextProp Nat (n => n + 0 = n) f g (n => DecEq.uniqueEq (f n) (g n))

-- A proof, stored as data.
def boxed: ProofBox (1 + 1 = 2) := { proof = rfl }

-- `Bool` equality, decided by `==`.
def BoolEq (x: Bool) (y: Bool): Prop := x = y

def boolDecides (x: Bool) (y: Bool): Iff ((x == y) = True) (BoolEq x y) := {
  forward = DecEq.sound x y,
  backward = e => rewrite e in Decidable.toBoolOf (DecEq.decide y y) rfl
}

-- In the quotient of `Bool` by its own equality, `True` and `False` stay apart.
theorem trueNotFalse (same: (Quot.mk True: Quot Bool BoolEq) = Quot.mk False): Void :=
  Bool.trueNotFalse
    (Quot.exactDec Bool BoolEq (x y => x == y) boolDecides
      (x => rfl)
      (x y e => Eq.sym e)
      (x y z p q => Eq.trans p q)
      True False same)
