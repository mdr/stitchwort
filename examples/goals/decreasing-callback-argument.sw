-- A recursive call inside a callback (`sumBy`'s), whose argument has a
-- lambda in it: the `decreasing` goal states the argument itself, as it
-- does outside a callback, and a `let` before the call shows its value
-- (SW-981). It was `List.length x < List.length xs`, about an unknown `x`:
-- the callback's row isn't known while its body is checked, so the
-- argument, a `filter` that might perform, was run with `bind` into a
-- variable that hid what it was.
import Std (List)

def g (xs: List Nat) (k: Nat): Nat
    decreasing xs.length
:=
  [1, 2] |> .sumBy (other => if k == 0 then 0 else g (xs.filter (c => c == other)) k [decreasing := ?])

def withLet (xs: List Nat) (k: Nat): Nat
    decreasing xs.length
:=
  [1, 2]
    |> .sumBy (other =>
      let left := xs.filter (c => c == other)
      if k == 0 then 0 else withLet left k [decreasing := ?])
