-- A tuple where a proof of `p ∧ q` is wanted is `Both`: `(rfl, h)` is
-- `Both rfl h` (docs/proposals/proof-tuples.md). This was SW-3419's error,
-- "write `Both`", before D3631 made it the short form.
theorem t ∀ (a: Nat) (h: a = 1): a = a ∧ a = 1 := (rfl, h)
