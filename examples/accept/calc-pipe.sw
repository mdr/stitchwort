-- A `calc` step's expression may use `|>`, which binds tighter than the
-- step's relation: `_ = xs |> List.sum` is `_ = (xs |> List.sum)`.
import Std (Eq, List, Nat)

theorem sumIsThree (xs: List Nat) (h: List.sum xs = 3): 3 = (xs |> List.sum) :=
  calc 3
    _ = xs |> List.sum := Eq.sym h

-- In the first expression too, and on a line of its own.
theorem doubled (xs: List Nat) (h: List.sum xs = 3): (xs |> List.sum) + 3 = 6 :=
  calc xs |> List.sum |> (n => n + 3)
    _ = 3 + 3 := Eq.cong (n => n + 3) h
    _ = 6
