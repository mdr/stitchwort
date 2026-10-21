-- expect-error: E-TYPE-MISMATCH
-- A numeral is a `Nat` or an `Int`, never another type: generic code
-- writes `Add.zero` (docs/proposals/interfaces.md §5.13).
def total [auto add: Add a] (xs: List a): a := xs.foldLeft (acc x => acc + x) 0
