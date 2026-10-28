-- expect-error: E-UNKNOWN-FIELD
-- `report.removing 0` looks for `Report.removing` only. The `removing` in
-- scope takes the `Report` second, so the note names that parameter.

type Report = { levels: List Nat }

def removing (index: Nat) (report: Report): Report := { levels = report.levels.removeAt index }

def shorter (report: Report): Report := report.removing 0
