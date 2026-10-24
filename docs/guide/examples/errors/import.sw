def numbers (line: Text): List Nat := (line.split ',').filterMap Text.toNat
