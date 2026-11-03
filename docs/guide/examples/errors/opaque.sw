opaque def checksum (xs: List Nat): Nat := xs.foldLeft 0 (sum x => (sum * 31 + x) % 65521)

theorem checksumNil: checksum [] = 0 := rfl
