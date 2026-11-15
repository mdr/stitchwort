-- expect-error: E-TERMINATION
-- Pairs with accept/termination-wrapper-honest.sw (`swapped`): a wrapper is
-- smaller than the parameter it was matched out of, not another one. In
-- `fromOther`, `r` comes from the second list, which grows; in `growOther`
-- the first wrapper grows while the second shrinks. Both run for ever.
type W (a: Type): Type = | MkW (x: a)

def fromOther: W (List Nat) → List Nat → Nat
  | MkW v, [_, ..r] => fromOther (MkW r) [0, 0, ..r]
  | _, _ => 0

def growOther: W (List Nat) → W (List Nat) → Nat
  | MkW [_, ..r], MkW q => growOther (MkW [0, 0, ..q]) (MkW r)
  | _, _ => 0
