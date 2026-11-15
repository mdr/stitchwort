-- expect-error: E-TERMINATION
-- Pairs with accept/termination-wrapper-honest.sw (`firstBranch`): nothing
-- is strictly inside a function, and a one-field constructor whose field is
-- a recursive function field never counts as a wrapper (its size is above
-- every result of the function, not one more than the function). Shifting
-- the function's argument keeps the tree as big, so both run for ever.
type W (a: Type): Type = | MkW (x: a)
type Tr: Type = | Leaf | Sup (kids: Nat → Tr)

def shiftedInW: W Tr → Nat
  | MkW (Sup kids) => shiftedInW (MkW (Sup (n => kids (n + 1))))
  | _ => 0

def shifted: Tr → Nat
  | Sup kids => shifted (Sup (n => kids (n + 1)))
  | _ => 0
