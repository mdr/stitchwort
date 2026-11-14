-- A bracket that opens on its own line joins the line above whether or not
-- the lines inside it start at its column (idempotence; SW-2466).
theorem applicationWithTail: Void := g (h x y (x => rfl) D, E, F)

theorem plainElements: Void := f (a, b)
