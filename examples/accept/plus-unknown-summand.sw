-- An unknown summand is inferred by peeling `Succ`s (SW-896). `+` computes
-- on both sides (accept/plus-both-sides.sw), so `x + 1` is `Succ x` and
-- `x + 3` is `3 + x`. A sum stuck on an unknown, `x + ?d`, can then only
-- equal `Succ s` if `?d` is a `Succ` too, and the unifier solves it that
-- way: `x + ?d` against `3 + x` gives `?d := 3`, and against `Succ (x + t)`
-- gives `?d := Succ t`.
import Std (List)

-- `d` is inferred from the proof's type.
def extra (x: Nat) (d: Nat) (p: x + d = Succ (x + 3)): Nat := d

theorem extraIsFour ∀ (x: Nat): extra x _ rfl = 4 := rfl

-- A computed `Succ (x + t)` against `x + ?d`, as in the roguelike's
-- `actAllDamage` (games/rogue).
def peel (x: Nat) (t: Nat) (f: (d: Nat) → x + d = Succ (x + t) → Nat): Nat := f _ rfl

-- The unknown on the left: `?d + x` against `Succ (t + x)`.
def peelLeft (x: Nat) (t: Nat) (f: (d: Nat) → d + x = Succ (t + x) → Nat): Nat := f _ rfl

-- Inside a `Succ`: `Succ (x + ?d)` against `Succ (Succ (Succ x))`.
def inside (x: Nat) (f: (d: Nat) → Succ (x + d) = x + 3 → Nat): Nat := f _ rfl

-- `(List.memRange _ _ (_ + 1)).forward h` with `h: x ∈ List.range 2 (n + 1)` and nothing else
-- to go on (a `match`'s scrutinee): the numbers are inferred from `h`'s type.
-- `List.range ?lo (?hi + 1)` is `List.rangeFrom (Succ ?hi - ?lo) ?lo`, stuck on
-- `?lo`, against `List.rangeFrom (n - 1) 2`; the first arguments are compared
-- again once the second have solved `?lo`.
theorem atLeastTwo ∀ (x: Nat) (n: Nat) (h: x ∈ List.range 2 (n + 1)): 2 ≤ x :=
  match (List.memRange _ _ (_ + 1)).forward h with
    | Both low _ => low

theorem atMostN ∀ (x: Nat) (n: Nat) (h: x ∈ List.range 1 (n + 1)): x ≤ n :=
  match (List.memRange _ _ (_ + 1)).forward h with
    | Both _ high => omega
