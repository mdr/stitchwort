-- A tuple pattern takes apart a test fact through its reading, as `Both`
-- does (docs/proposals/proof-tuples.md §4.2): `(a && b) = True` reads as
-- `a = True ∧ b = True`.

theorem leftTrue ∀ (a b: Bool) (h: (a && b) = True): a = True :=
  let (x, _) := h
  x

theorem rightTrue ∀ (a b: Bool) (h: (a && b) = True): b = True := match h with | (_, y) => y
