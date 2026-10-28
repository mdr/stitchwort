-- expect-error: E-UNKNOWN-FIELD
-- `report.withoutFirst` looks for `Report.withoutFirst` only. The
-- `withoutFirst` beside `Report` takes a `Report`, so a note suggests the
-- plain call.

type Report = { levels: List Nat }

def withoutFirst (report: Report): Report := { levels = report.levels.tailOf }

def shorter (report: Report): Report := report.withoutFirst
