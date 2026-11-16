-- expect-error: E-TEXT-PATTERN
-- A constructor's arguments end before `++`, as in an expression, so this is
-- `(Some "a") ++ rest`, whose left isn't a text literal: brackets fix it.
def startsWithA (t: Option Text): Bool := match t with
  | Some "a" ++ rest => True
  | _ => False
