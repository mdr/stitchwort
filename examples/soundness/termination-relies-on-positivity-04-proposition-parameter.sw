-- expect-error: E-POSITIVITY
-- Termination relies on this refusal (termination.rs's header, "Two
-- orders"; docs/reviews/SW-3376-wrapper-rule-soundness.md F2, p09): the
-- loop of termination-relies-on-positivity-01-direct.sw with the pinned
-- proof `p: Big T` and the pinning field's type `PBox T p` taking it as a
-- proposition parameter. `x` depends on `p`, which holds a `T`, so `T` is
-- refused; otherwise `Mk (Hold <bigger>) x` would count as the matched
-- `Mk p x`, and `f` would loop with every call recorded smaller.
-- Removing that rule alone doesn't let the loop through: `T` also sits inside
-- `PBox`, whose later parameter `p` mentions `a` (nestable condition 2), and
-- either refusal holds on its own. With both removed (tried by hand, not a
-- kernel change), `f` is accepted and `rfl` on `f` of a closed value never
-- finishes.
import Std (Unit)

type Big (a: Type): Prop = | Stop | Hold (d: a)
type PBox (a: Type) (p: Big a): Type = | MkPBox
type T: Type = | Leaf | Mk (p: Big T) (x: PBox T p) | In (t: T)

theorem f: T → Unit
  | In (Mk p x) => f (Mk (Hold (In (In (Mk p x)))) x)
  | Mk (Hold t) x => f t
  | In (In t) => f (In t)
  | _ => Trivial
