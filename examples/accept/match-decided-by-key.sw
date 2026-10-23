-- D1073: `match e: c < x with` on a type whose order is by a key (`Fin`, by
-- `Ord.byKey Fin.toNat`) decides the same comparison an `if c < x` holds
-- once unfolded, `Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x)`, so each branch
-- sees its `if` decided and `omega` reads `e`. `Nat`'s own `<` works as before.
import Std (Nat, Fin, Bool, Void)

def larger (c: Fin 10) (x: Fin 10): Fin 10 := if c < x then x else c

theorem largerGe (c: Fin 10) (x: Fin 10): Fin.toNat c <= Fin.toNat (larger c x) :=
  match e: c < x with
    | True => omega
    | False => omega

theorem largerGeRight (c: Fin 10) (x: Fin 10): Fin.toNat x <= Fin.toNat (larger c x) :=
  match e: c < x with
    | True => omega
    | False => omega

-- A `Bool` comparison in the goal is decided by the same `match`.
def below (c: Fin 10) (x: Fin 10): Bool := c < x

theorem belowLess (c: Fin 10) (x: Fin 10) (h: below c x = True): Fin.toNat c < Fin.toNat x :=
  match e: c < x with
    | True => omega
    | False => Void.exfalso (Bool.falseNotTrue h)

def largerNat (c: Nat) (x: Nat): Nat := if c < x then x else c

theorem largerNatGe (c: Nat) (x: Nat): c <= largerNat c x :=
  match e: c < x with
    | True => omega
    | False => omega
