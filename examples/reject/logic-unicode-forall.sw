-- expect-error: E-PARSE
-- `∀` isn't one of the Unicode spellings (D1200, D1208): "for all" is a
-- function type, `(x: Nat) -> x <= x`. The error says so.
theorem leRefl: ∀ x, x <= x := ?
