-- Deciding `List.Mem` (`x in xs` on a list, D1201) from a decision for
-- equality, so `x in xs` is decided where a `Bool` is expected (`if x in
-- seen`, `xs.filter (x => x !in seen)`) and `if h: x in xs` names the proof.
-- `List.Mem` and its facts are in Toolkit.sw.

-- `x in xs`, decided one element at a time from the front.
instance List.decMem [auto eq: DecEq a] (x: a): (xs: List a) -> Decidable (List.Mem x xs)
  | Nil => No (none => none)
  | Cons y ys => Decidable.or (eq.decide y x) (List.decMem x ys)

test "List.decMem" := 2 in [1, 2, 3] && 4 !in [1, 2, 3] && 'a' !in []

test "List.decMem on a variable" := List.all [3, 1] (x => x in [1, 2, 3])
