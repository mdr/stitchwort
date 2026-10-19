-- expect-error: E-REFL
-- A false `rfl` about a definition that computes a long way: the message
-- shows the two sides as written, and the computed form is short, with its
-- inner parts elided (SW-115).
type Range = { lo: Nat, hi: Nat }

def Range.repeated (r: Range) (k: Nat) (n: Nat): Nat :=
  let m := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))
  if m != 0 then
    let lo := Nat.max (Nat.pow 10 (k - 1)) ((r.lo + m - 1) / m)
    let hi := Nat.min (Nat.pow 10 k - 1) (r.hi / m)
    if lo <= hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

theorem wrongRepeated (r: Range) (k: Nat) (n: Nat): r.repeated k n = 0 := rfl
