-- A body line left of a header continuation line that holds an open bracket
-- is a child of the declaration, not of that line (idempotence; SW-2466).
theorem t ∀ (same: (a b) c d (x => rfl) (y => rfl) e = f): Void := g
