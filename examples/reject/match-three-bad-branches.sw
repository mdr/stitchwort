-- expect-error: E-TYPE-MISMATCH
-- Every wrong branch is reported in one run, not just the first.
def f: Bool → Nat → Nat
  | True, n => True
  | False, Zero => False
  | False, Succ m => "no"
