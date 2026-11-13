-- `cases` closes a case by a part of a hypothesis
-- (docs/proposals/bool-as-proposition.md §9): a side of a conjunction, or
-- what a test fact reads as, taken apart in turn. Before, each of these
-- split the tests and still couldn't close the case.
import Std (Bool, List, Nat)

type Point = { x: Nat, y: Nat }

theorem inRight (x: Nat) (xs: List Nat) (b: Bool) (h: (b && xs.contains x) = True): x ∈ xs := cases

theorem notSame (p: Point) (q: Point) (b: Bool) (h: (b || p == q) = False): p ≠ q := cases

theorem noneBig (xs: List Nat) (wanted: Bool) (h: (wanted && not (xs.any (x => x > 2))) = True):
    ∀ (x: Nat) => x ∈ xs → (x > 2) = False :=
  cases

theorem fromConjunction (x: Nat) (xs: List Nat) (ys: List Nat) (h: x ∈ xs ∧ x ∈ ys): x ∈ ys := cases
