-- expect-error: E-UNKNOWN-NAME
-- Lean's `by` opens a tactic block; a Stitchwort proof is a term written
-- where the proof goes, such as `byComputing` or `arithmetic`.
theorem one: 1 = 1 := by simp
