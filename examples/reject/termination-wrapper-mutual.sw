-- expect-error: E-TERMINATION
-- Pairs with accept/termination-wrapper-honest.sw: in a group, the wrapper
-- that `unwrap` builds is bigger than the list it was given, so `wrapped`
-- and `unwrap` call each other for ever.
type W (a: Type): Type = | MkW (x: a)

def wrapped: W (List Nat) → Nat
  | MkW [_, ..r] => unwrap r
  | _ => 0

def unwrap: List Nat → Nat
  | r => wrapped (MkW [0, 0, ..r])
