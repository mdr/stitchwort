-- expect-error: E-PARSE
-- A keyword can't be a pattern's variable.
def previous (n: Nat): Nat := match n with
  | Succ return => return
  | Zero => 0
