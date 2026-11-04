-- expect-error: E-PARSE
-- Patterns take `..` only last, even though expressions allow it anywhere.
def lastOf: List Nat → Nat
  | [..init, last] => last
  | _ => 0
