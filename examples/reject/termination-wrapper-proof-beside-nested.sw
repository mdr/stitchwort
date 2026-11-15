-- expect-error: E-TERMINATION
-- termination-wrapper-proof-beside.sw one level down: `MkW`'s one field
-- holds `MkD xs q`, and the call rebuilds it as `MkD xs (MkPBox …)` with a
-- new proof. That isn't a part of the argument, so it can't be the `u` of
-- the wrapper rule: a proof built beside the part can carry a bigger value,
-- which the second clause takes back out
-- (docs/reviews/SW-3412-text-rest-relanded.md, d6).
import Std (List, Nat, Unit)
type PBox (a: Type): Prop = | MkPBox (x: a)
type D: Type = | MkD (xs: List Nat) (q: PBox W)
type W: Type = | MkW (d: D)
theorem t: W → Unit
  | MkW (MkD [_, ..xs] q) => t (MkW (MkD xs (MkPBox (MkW (MkD [0, 0, 0] q)))))
  | MkW (MkD [] (MkPBox w)) => t w
