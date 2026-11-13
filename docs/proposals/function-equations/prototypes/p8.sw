-- P8. An effect-polymorphic definition's arm, at the empty row, by `rfl`.
import Std (List)

theorem filterEq2 ∀ (x: Nat) (xs: List Nat) (p: Nat → Bool):
    List.filter (Cons x xs) p = List.filterStep x (List.filter xs p) (p x) :=
  rfl
