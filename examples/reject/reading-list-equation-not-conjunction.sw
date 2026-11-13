-- expect-error: E-NO-READING
-- `==` on two lists reads as the equation of the lists, not as the
-- conjunction of their heads and tails it computes to, so `Both` can't take
-- it apart (docs/proposals/bool-as-proposition.md §5.4, step 2b).
import Std (Nat)

theorem heads (x y: Nat) (xs ys: List Nat) (h: ([x, ..xs] == [y, ..ys]) = True): x = y :=
  match h with
    | Both heads tails => heads.read
