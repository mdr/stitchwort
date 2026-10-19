-- expect-error: E-TYPE-MISMATCH
-- A negative number pattern is an `Int`; a `Nat` argument has no negative
-- numbers to match.
def f: Nat -> Nat
  | (-1) => 1
  | _ => 2
