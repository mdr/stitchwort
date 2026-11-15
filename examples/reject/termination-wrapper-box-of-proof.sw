-- expect-error: E-TERMINATION
-- The wrapper `MkW` and its one field are data, but the descent from
-- `MkBox (MkLoop n)` to `MkBox n` happens inside `MkBox`'s proof field:
-- `MkW (MkBox n)` isn't a wrapper around a strict part, and it's the
-- same value as `w` to the kernel (docs/reviews/SW-3412-text-rest-relanded.md, a4).
import Std (Void)
type Loop: Prop = | MkLoop (next: Loop)
type Box (a: Prop): Type = | MkBox (h: a)
type W: Type = | MkW (b: Box Loop)
def f (w: W): Void := match w with
  | MkW (MkBox l) =>
    match l with
      | MkLoop n => f (MkW (MkBox n))
