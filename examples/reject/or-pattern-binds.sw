-- expect-error: E-OR-PATTERN-BINDS
-- Every alternative of an or-pattern binds the same names: the arm's body is
-- checked once for each, and `same` would have no value when `Inr _`
-- matched.
theorem shortText ∀ (text: Text) (spelt: (text = "a" ∨ text = "b") ∨ text = "c"): text.length = 1 :=
  match spelt with
    | Inl (Inl same) | Inr _ => rewrite same
    | Inl (Inr same) => rewrite same
