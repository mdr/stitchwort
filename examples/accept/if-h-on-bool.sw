-- `if h: b` on a `Bool` gives `h: b = True` in the `then` branch and its
-- negation in the `else` branch (SW-1015, bool-as-proposition.md §4.6).

theorem choose ∀ (b: Bool): Or (b = True) (Not (b = True)) := if h: b then Inl h else Inr h
