-- expect-error: E-POSITIVITY
-- Termination relies on this refusal (termination.rs's header, "Two
-- orders"; docs/reviews/SW-3376-wrapper-rule-soundness.md F2, p11):
-- termination-relies-on-positivity-04-proposition-parameter.sw with the
-- pinned proof one level down, in `Q T`. `Q`'s parameter isn't nestable
-- (condition 5: `x` mentions `p`, whose type mentions `a`), so `T` is
-- refused; otherwise the rebuilt `Node (MkQ (Hold <bigger>) x)` would count
-- as the matched `Node (MkQ p x)`, and `f` would loop.
import Std (Unit)

type Big (a: Type): Prop = | Stop | Hold (d: a)
type PBox (a: Type) (p: Big a): Type = | MkPBox
type Q (a: Type): Type = | MkQ (p: Big a) (x: PBox a p)
type T: Type = | Node (q: Q T) | In (t: T)

theorem f: T → Unit
  | In (Node (MkQ p x)) => f (Node (MkQ (Hold (In (In (Node (MkQ p x))))) x))
  | Node (MkQ (Hold t) x) => f t
  | In (In t) => f (In t)
  | _ => Trivial
