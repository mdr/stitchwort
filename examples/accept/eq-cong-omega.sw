-- `Eq.cong f (arithmetic)` against `f a = f b`: the goal fixes what `arithmetic`
-- proves, `a = b`, before `arithmetic` is run.
import Std (Nat, Option, Eq)

theorem someShifted ∀ (n: Nat): Some (n + 0 + 1) = Some (1 + n) := Eq.cong Some (arithmetic)

theorem succShifted ∀ (m n: Nat) (h: m <= n): Nat.Succ (n - m + m) = Nat.Succ n := Eq.cong Nat.Succ (arithmetic)

def applyTo [a: Type] [b: Prop] (continue: a -> b) (x: a): b := continue x

theorem moved ∀ (n: Nat): Some (n + 0 + 1) = Some (n + 1) :=
  applyTo (x => rewrite Nat.addZero n then Eq.cong Some (arithmetic)) n
