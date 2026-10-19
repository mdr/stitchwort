-- expect-error: E-TYPE-MISMATCH
-- A pair is checked against its pair type, component by component.
def bad: (Nat, Bool) := (1, 2)
