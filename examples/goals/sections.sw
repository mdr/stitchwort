-- Operator sections and bare operators are shown as written: `(== id)`,
-- `(id ==)`, `(+ 1)`, `(< n)`, `(+)`. A method section that takes a whole
-- expression is a lambda, with its parameter named.
type Item : Type = { name: Text, id: Nat }

def summary (xs: List Nat) (items: List Item) (id: Nat) (n: Nat): Nat :=
  let matching := xs.count (== id)
  let flipped := xs.count (id ==)
  let others := xs.count (!= id)
  let next := xs.map (+ 1)
  let doubled := xs.map (n * 2 +)
  let small := xs.filter (< n)
  let large := xs.filter (> n)
  let total := Std.List.foldLeft xs 0 (+)
  let found := items.filter (.id == id)
  ?

theorem countBelow (xs: List Nat) (n: Nat): xs.count (< n) ≤ xs.length := ?
