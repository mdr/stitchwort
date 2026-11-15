-- expect-error: E-POSITIVITY
-- Termination relies on this refusal (termination.rs's header, "Two
-- orders"): termination-relies-on-positivity-02-nested.sw with the type
-- reached through two levels of nesting, `R` inside `W R` inside `T R`.
-- `T`'s parameter isn't nestable (condition 5), so neither is `W`'s, and `R`
-- is refused; otherwise `f` would loop as in 02, each call recorded smaller.
import Std (Unit)

type PBox (a: Type): Prop = | MkPBox (x: a)
type Tag (a: Type) (p: PBox a): Type = | MkTag
type T (a: Type): Type = | Mk (p: PBox a) (x: Tag a p) | In (t: T a)
type W (a: Type): Type = | MkW (t: T a)
type R: Type = | MkR (w: W R)

theorem f: W R → Unit
  | MkW (In (Mk p x)) => f (MkW (Mk (MkPBox (MkR (MkW (In (In (Mk p x)))))) x))
  | MkW (Mk (MkPBox (MkR w)) x) => f w
  | MkW (In (In t)) => f (MkW (In t))
