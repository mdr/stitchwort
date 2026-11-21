-- A `match` on a function, with a goal whose opened call holds a function
-- of another type. Looking for `q`'s value, `x y => p x y`, inside `Both p`
-- (opened because its arguments mention `p`), the search meets `(c: Bool) =>
-- False`: a function too, so a candidate by its head, but not of `q`'s
-- type. Comparing the two by computation would apply `False` to an
-- argument; the candidate's type is compared first, and it is no
-- occurrence. (The shape of the toy formatter's `operatorToken`, which
-- matches on `stands`, a `let` of a proof that is a function;
-- docs/proposals/partial-unfold.md.)
def Both (p: Nat → Nat → Bool): Prop := ((c: Bool) => False) = ((c: Bool) => False) ∧ p 0 0 = p 0 0

theorem bothHolds ∀ (p: Nat → Nat → Bool): Both p :=
  let q: Nat → Nat → Bool := x y => p x y
  match q with | q => (byComputing, byComputing)
