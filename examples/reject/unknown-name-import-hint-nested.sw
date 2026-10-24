-- expect-error: E-UNKNOWN-NAME
-- `Done` is `Std.Effect.Comp.Done`; the hint's import path is written in
-- full, as an import path is read (SW-403).
def x: Nat := Done
