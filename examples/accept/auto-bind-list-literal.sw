-- Variables bound only by a constructor's result type are auto-bound through
-- list literals as through `Cons`: `[x]`, `[x, ..xs]` and `[x, y, ..rest]`.

type Swapped: List Nat → List Nat → Prop =
  | Empty: Swapped [] []
  | One: Swapped [x] [x]
  | Step (tail: Swapped xs ys): Swapped [x, ..xs] [x, ..ys]
  | Flip (tail: Swapped rest rest2): Swapped [x, y, ..rest] [y, x, ..rest2]

theorem oneExample: Swapped [3] [3] := One

theorem stepExample: Swapped [1, 2] [1, 2] := Step One

theorem flipExample: Swapped [1, 2, 3] [2, 1, 3] := Flip One
