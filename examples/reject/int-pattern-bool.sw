-- expect-error: E-TYPE-MISMATCH
-- A number pattern needs a numeric argument type; `Bool` is not one.
def f: Bool → Nat
  | (-1) => 1
  | _ => 2
