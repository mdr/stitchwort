-- expect-error: E-TYPE-MISMATCH
-- A pair is checked against its pair type, component by component.
bad : (Nat, Bool)
bad = (1, 2)
