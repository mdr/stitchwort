-- `rewrite f.unfold in …` with the argument left open (SW-917). Matching
-- `lcg seed` solves the rule's unknown argument with `seed`; the goal after
-- the rewrite holds `seed` itself, not the solved unknown, so the body's type
-- is found the same as the goal at once. With the solved unknown left in,
-- the comparison unfolded `% 2147483648` in full on both sides, a
-- `Nat.divFuel` step per `Succ` of the `+ 12345`, and took 24 s.
import Std (Nat)

opaque def lcg (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648

theorem lcgBelow (seed: Nat): lcg seed < 2147483648 :=
  rewrite lcg.unfold in Nat.modLt (seed * 1103515245 + 12345) 2147483648

-- The argument given, as before.
theorem lcgBelowGiven (seed: Nat): lcg seed < 2147483648 :=
  rewrite lcg.unfold seed in Nat.modLt (seed * 1103515245 + 12345) 2147483648

-- Two occurrences with different arguments: each match solves its own copy.
theorem twoBelow (a: Nat) (b: Nat): lcg a < 2147483648 ∧ lcg b < 2147483648 :=
  rewrite lcg.unfold in
  rewrite lcg.unfold in
  Both (Nat.modLt (a * 1103515245 + 12345) 2147483648) (Nat.modLt (b * 1103515245 + 12345) 2147483648)
