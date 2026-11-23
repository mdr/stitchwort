-- expect-error: E-REFL
-- Rule K compares a cast's ends while evaluating, where nothing counts the
-- variables in scope. Its fresh variables come from a range no context
-- reaches (docs/proposals/full-proof-irrelevance-audit.md, finding A): with
-- `v` the sixth variable, comparing `z => z` with `z => v` at level 5 would
-- name `z` as `v` and call them equal. They differ, so the cast is stuck.
import Std (Nat, Eq)

def castFn (f g: Nat → Nat) (h: f = g) (n: Nat): Nat := J (y e => Nat) n h

theorem fresh ∀ (a b c d e v: Nat) (h: ((z: Nat) => z) = ((z: Nat) => v)): castFn (z => z) (z => v) h 7 = 7 :=
  byComputing
