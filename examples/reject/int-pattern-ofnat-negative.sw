-- expect-error: E-TYPE-MISMATCH
-- `OfNat` wraps a `Nat`, which has no negative numbers. Write `(-1)` on its
-- own to match the negative `Int`.
def f: Int → Nat
  | OfNat (-1) => 1
  | _ => 2
