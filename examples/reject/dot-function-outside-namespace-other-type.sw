-- expect-error: E-UNKNOWN-FIELD
-- `report.size` looks for `Report.size` only. The `size` in scope takes a
-- `List Nat`, not a `Report`, so no note suggests calling it.

type Report = { levels: List Nat }

def size (levels: List Nat): Nat := levels.length

def sizeOf (report: Report): Nat := report.size
