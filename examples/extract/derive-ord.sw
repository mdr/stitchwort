-- Derived `Ord` in generated JS (docs/proposals/interfaces.md §5.11): the
-- same order as the interpreter gives, for an enumeration, a record and a
-- recursive data type, sorted with the generic `List.sort`.
--
-- run: suits 2
-- run: items 3
-- run: shapes 1
-- run: shapes 4

type Suit = | Clubs | Diamonds | Hearts | Spades

type Item = { name: Text, price: Nat, positive: price = price }

type Shape = | Dot | Circle (radius: Nat) | Group (first: Shape) (rest: Shape)

export def suits (n: Nat): Text :=
  let hand: List Suit := if n == 0 then [Hearts] else [Spades, Clubs, Hearts, Diamonds, Clubs]
  "${List.sort hand}"

export def items (n: Nat): Text :=
  let xs: List Item := [{ name = "tea", price = n, positive = rfl }, { name = "jam", price = 4, positive = rfl }, { name = "jam", price = n, positive = rfl }]
  "${List.sort xs}"

export def shapes (n: Nat): Text := "${List.sort [Group Dot (Circle n), Circle 2, Group Dot Dot, Dot]}"
