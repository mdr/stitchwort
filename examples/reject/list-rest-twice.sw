-- expect-error: E-PARSE
-- Only one `..` tail is allowed.
def f: List Nat → Nat
  | [x, ..a, ..b] => x
  | _ => 0
