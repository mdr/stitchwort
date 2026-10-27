-- `Eq.cong f (omega)` against `f a = f b`: the goal fixes what `omega`
-- proves, `a = b`, before `omega` is run.
import Std (Nat, Option, Eq)

theorem someShifted (n: Nat): Some (n + 0 + 1) = Some (1 + n) :=
  Eq.cong Some (omega)

theorem succShifted (m: Nat) (n: Nat) (h: m <= n): Nat.Succ (n - m + m) = Nat.Succ n :=
  Eq.cong Nat.Succ (omega)

def applyTo [a: Type] [b: Prop] (continue: a -> b) (x: a): b := continue x

theorem moved (n: Nat): Some (n + 0 + 1) = Some (n + 1) :=
  applyTo (x =>
    rewrite Nat.addZero n in
    Eq.cong Some (omega)) n
