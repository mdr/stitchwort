-- Probe for docs/proposals/bool-and-prop.md §2.2 and §5: what a `≤` defined
-- by its test gives for free. Checks.
import Std (Bool, List, Nat, Set, Void)

theorem small: 3 ≤ 5 := rfl
theorem big: 123456789012345678901234567890 ≤ 123456789012345678901234567891 := rfl

-- With unknowns: the test computes as far as the numbers are known.
theorem open1 ∀ (n: Nat): 2 ≤ n + 5 := rfl
theorem open2 ∀ (a b: Nat) (h: Succ a ≤ Succ b): a ≤ b := h
theorem open3 ∀ (a b: Nat) (h: a + 3 ≤ b + 3): a ≤ b := h

-- A premise that computes to `False = True` needs no arm.
theorem leZero: ∀ (m: Nat) => m ≤ 0 → m = 0
  | Zero, h => rfl
  | Succ m, ()

-- The hypothesis is the program's test, so it rewrites the program.
def pick (s: Set Nat) (k: Nat): Nat := if s.contains k && k ≤ 10 then 1 else 2
theorem pickIn ∀ (s: Set Nat) (k: Nat) (has: k ∈ s) (small: k ≤ 10): pick s k = 1 := rewrite has, small in rfl
