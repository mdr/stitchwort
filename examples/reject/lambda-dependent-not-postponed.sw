-- expect-error: E-CANNOT-INFER
-- A lambda isn't checked after the later arguments when a later argument's
-- type depends on it: here `same`'s type mentions `f`, so `\p => p.name` is
-- checked where it is, before `ann` has fixed `p`'s type.

type Person = { name : Text }

def ann : Person := { name = "Ann" }

def applyChecked (f : a -> Text) (same : f = f) (x : a) : Text := f x

def name : Text := applyChecked (\p => p.name) Refl ann
