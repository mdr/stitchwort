-- expect-error: E-PARSE
-- `∀` is `forall` (D3458), whose parameters are followed by `=>`, not by
-- the `,` of Lean and Rocq. The error says so.
theorem leRefl: ∀ x, x <= x := ?
