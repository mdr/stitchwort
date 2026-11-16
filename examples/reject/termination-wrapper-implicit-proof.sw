-- expect-error: E-TERMINATION
-- The one field is an implicit proof, erased at runtime: not a wrapper,
-- as in termination-wrapper-proof-irrelevance-07.sw. Pairs with the
-- implicit data field accepted in accept/termination-wrapper-honest.sw.
import Std (Void)

type Loop: Prop = | MkLoop (next: Loop)

type Wi: Type = | MkWi [h: Loop]

def f (w: Wi): Void := match w with
  | MkWi [h := l] =>
    match l with
      | MkLoop n => f (MkWi [h := n])
