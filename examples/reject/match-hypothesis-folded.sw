-- expect-error: E-TYPE-MISMATCH
-- A named `match` hypothesis keeps the call the program wrote: the message
-- shows `isBig n = True`, not the table that `isBig` reads from.
import Std (List)

def table: List Nat := [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120]

def isBig (n: Nat): Bool := table.getOr n 0 == 50

theorem wrongStep (n: Nat): isBig n = False :=
  match big: isBig n with
    | True => big
    | False => rfl
