-- expect-error: E-REFL
-- A default must work for any values of the earlier parameters, since a
-- call may give them and leave this one out
-- (docs/proposals/signature-defaults.md §5.2).

def board (size: Nat := 8) (square: size = 8 := rfl): Nat := size * size
