-- An `∨` hypothesis named is split into its sides, each a fact, and an `∨`
-- inside a side too: `h` makes three cases, and in each the fact puts the
-- number in place of `n`.
import Std (Nat)

theorem smallSum ∀ (n: Nat) (h: n = 1 ∨ n = 2 ∨ n = 4): n + n ≤ 8 := cases h then arithmetic
