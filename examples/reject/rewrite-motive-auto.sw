-- expect-error: E-REWRITE-MOTIVE
-- `g d` carries a proof that `d != 0`. Replacing `d` by a variable leaves that
-- proof about `d`, so the goal with `d` abstracted isn't well formed.
theorem bad (g: (d: Nat) -> [auto ok: d != 0] -> Nat) (d: Nat) (e: Nat) (h: d = e) [auto p: d != 0]:
    g d + 1 = g d + 1 :=
  rewrite h
