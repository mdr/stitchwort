-- expect-error: E-NO-READING
-- A `let Both` on a test fact with no reading is an error whatever the goal:
-- here the goal is a membership, so the pattern binds projections, and the
-- fact is read before they can be projected
-- (docs/proposals/bool-as-proposition.md §6.1, §6.7).
import Std (Bool, List, Nat)

opaque def mystery (n: Nat): Bool := n < 10

theorem noParts ∀ (n: Nat) (xs: List Nat) (h: mystery n) (member: n ∈ xs): n ∈ xs :=
  let Both left _ := h
  member
