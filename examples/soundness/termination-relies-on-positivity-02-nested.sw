-- expect-error: E-POSITIVITY
-- Termination relies on this refusal (termination.rs's header, "Two
-- orders"): the loop of termination-relies-on-positivity-01-direct.sw,
-- with the proof's type reaching `W` through nesting. `T`'s parameter `a`
-- isn't nestable, since `x`'s type mentions the earlier field `p`, whose
-- type mentions `a` (nestable condition 5). Without that, `MkW (Mk <proof
-- holding the argument> x)` would be recorded smaller than `MkW (In (Mk p
-- x))`, the second clause would take the bigger value back out, and `f`
-- would loop.
import Std (Unit)

type PBox (a: Type): Prop = | MkPBox (x: a)
type Tag (a: Type) (p: PBox a): Type = | MkTag
type T (a: Type): Type = | Mk (p: PBox a) (x: Tag a p) | In (t: T a)
type W: Type = | MkW (t: T W)

theorem f: W → Unit
  | MkW (In (Mk p x)) => f (MkW (Mk (MkPBox (MkW (In (In (Mk p x))))) x))
  | MkW (Mk (MkPBox w) x) => f w
  | MkW (In (In t)) => f (MkW (In t))
