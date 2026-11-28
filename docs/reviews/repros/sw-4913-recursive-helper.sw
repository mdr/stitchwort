-- SW-4913, shape (b): the `match` calls the local definition it is in, so
-- the two are one group, and the equation about the `match` is checked in
-- that group's bodies. The elaborator refuses the `byComputing`, not the
-- kernel.
theorem t ∀ (b: Bool): b = b :=
  def go: Nat → Nat
    | Zero => 2
    | Succ k =>
      let pick: Nat := match b with
        | True => go k
        | False => go k
      let same: pick = 0 := byComputing
      go k
  byComputing
