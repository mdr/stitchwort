-- expect-error: E-TYPE-MISMATCH
-- A lemma about a composite function, `() => j (p ())`, used for a pure
-- named one. `one ()` is `Succ (Succ 0)`, so the lemma's `j (p ())` would
-- have to be abstracted out of it, and that has many solutions: `_` is
-- not solved for `p` and `j`, and must not be guessed. Lazy delta
-- (SW-1227) doesn't apply: it unfolds a call to meet a call of another
-- definition, and `j (p ())` here is an unknown applied, not a call.
def Holds (f: () → Nat): Prop := f () = f ()

theorem composite (p: () → Nat) (j: Nat → Nat): Holds (() => j (p ())) := rfl

def one(): Nat := Succ (Succ 0)

theorem oneHolds: Holds one := composite _ _
