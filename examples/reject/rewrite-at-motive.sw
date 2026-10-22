-- expect-error: E-REWRITE-MOTIVE
-- `g d` carries a proof that `d != 0`. Replacing `d` by a variable in the type
-- of `h` leaves that proof about `d`, so the type with `d` abstracted isn't
-- well formed.
def bad (g: (d: Nat) -> [auto ok: d != 0] -> Nat) (d: Nat) (e: Nat) (k: d = e) [auto p: d != 0] (h: g d = 1): Nat :=
  let h2 := rewrite k at h
  0
