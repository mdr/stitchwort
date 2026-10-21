-- `Show` and interpolation in generated JS (docs/proposals/interfaces.md
-- §5.14): the same text as the interpreter gives, for lists of texts,
-- derived data and records.
--
-- run: describe 3
-- run: describe 0
-- run: names ["a", "b\"c"]
-- run: shapes 2
-- run: shapes 0

type Shape = | Circle (radius: Nat) | Rect (w: Nat) (h: Nat) | Dot

type Item = { name: Text, price: Nat, positive: price = price }

export def describe (n: Nat): Text :=
  let item: Item := { name = "tea", price = n, positive = rfl }
  "${item} costs ${n}"

export def names (xs: List Text): Text := "${xs} / ${xs.length}"

export def shapes (n: Nat): Text :=
  if n == 0 then "${[Dot]}" else "${[Circle n, Rect n n]}"
