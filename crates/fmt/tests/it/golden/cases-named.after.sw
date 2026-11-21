-- `cases` with the values to split: a comma list on the keyword's line, with or
-- without `then`.
theorem t ∀ (a b: Bool): (a || b) = (b || a) := cases a, b then byComputing

theorem u ∀ (a: Bool): (a || a) = a := cases a

theorem v ∀ (a b: Bool): (a || b) = (b || a) := cases a, b then byComputing
