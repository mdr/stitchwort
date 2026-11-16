-- expect-error: E-UNKNOWN-NAME
-- There is no `simp`: a Stitchwort proof computes (`byComputing`), rewrites
-- (`rewrite …`) or uses arithmetic (`arithmetic`).
theorem one: 1 = 1 := simp
