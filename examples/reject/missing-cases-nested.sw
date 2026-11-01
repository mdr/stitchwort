-- expect-error: E-NONEXHAUSTIVE
-- Missing cases that are nested in a pair are listed whole: `(None, False)`
-- and `(Some _, True)`, not the constructor one level down.
type Opt (a: Type) =
  | None
  | Some (x: a)

def pick: (Opt Nat, Bool) → Nat
  | (Some _, False) => 1
  | (None, True) => 2
