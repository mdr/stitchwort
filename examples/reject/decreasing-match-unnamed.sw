-- expect-error: E-DECREASING
-- A `match`'s equation reaches the recursive call unnamed, but `omega`
-- can't read `set.popMin = Some (least, rest)`: the message lists it and
-- says to name it, to pass it to a lemma (`Set.sizePopMin`).
import Std (Nat, Option, Set)

def total (set: Set Nat): Nat
    decreasing set.size
:=
  match set.popMin with
    | None => 0
    | Some (least, rest) => least + total rest
