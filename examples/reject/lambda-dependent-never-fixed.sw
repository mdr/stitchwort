-- expect-error: E-CANNOT-INFER
-- A lambda checked after the later arguments, because its parameter type
-- isn't known where it is, still fails when none of them fixes that type:
-- `same`'s type mentions `f`, and `rfl` proves it whatever `f` is, so `p`'s
-- type is never known. The error is the one checking it in place gave.

type Person = { name: Text }

def applyChecked (f: a → Text) (same: f = f): Text := "checked"

def name: Text := applyChecked (p => p.name) rfl
