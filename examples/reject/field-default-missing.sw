-- expect-error: E-RECORD-FIELD
-- Only fields with defaults may be left out; the note names them
-- (docs/proposals/named-arguments.md §6.3).

type RangeOptions = {
  start: Nat := 0,
  stop: Nat,
  step: Nat := 1
}

def missing: RangeOptions := { start = 2 }
