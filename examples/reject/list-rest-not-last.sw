-- expect-error: E-PARSE
-- `..` must be the last item of a list pattern.
def f: List Nat -> Nat
  | [..rest, x] => x
  | _ => 0
