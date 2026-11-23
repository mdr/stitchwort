-- expect-error: E-REFL
-- Rule S reads a proof's indices from its type at the match: here the outer
-- match refines `x` to `0`, but `y` is unknown, so `Same Nat 0 y` may have
-- no proof and the inner match stays stuck.
import Std (Nat)

type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x

def carry2 (x y: Nat) (h: Same Nat x y) (n: Nat): Nat := match x with
  | Zero =>
    (match h with
      | MkSame => n)
  | Succ k => n

theorem mustRefuse ∀ (y: Nat) (h: Same Nat 0 y): carry2 0 y h 4 = 4 := byComputing
