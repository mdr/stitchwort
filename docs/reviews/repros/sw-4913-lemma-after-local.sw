-- SW-4913: an equation about a local definition, written after it in the
-- owner, is checked once the definition is final, so it holds.
theorem t ∀ (b: Bool): b = b :=
  def go: Nat → Nat
    | Zero => 2
    | Succ k =>
      let pick: Nat := match b with
        | True => go k
        | False => go k
      pick
  let s: go Zero = 2 := byComputing
  byComputing
