-- expect-error: E-POSITIVITY
-- Termination relies on this refusal (termination.rs's header, "Two
-- orders"). `x`'s type pins `p`, so the checker takes `Mk <anything> x` for
-- the matched `Mk p x`; `Tag`'s parameter is a proof, which comparison
-- skips, so it may hold a value bigger than the argument. If `p`'s type could
-- hold a `T` (a field depending on one that holds `T`), `f` would put the
-- argument into the proof in the first clause, dig it out in the second and
-- shrink it back in the third: each call is recorded smaller, and `f` loops.
-- Removing that rule alone doesn't let the loop through: `T` also sits inside
-- `Tag`, whose later parameter `p` mentions `a` (nestable condition 2), and
-- either refusal holds on its own. With both removed (tried by hand, not a
-- kernel change), `f` is accepted and `rfl` on `f` of a closed value never
-- finishes.
import Std (Unit)

type PBox (a: Type): Prop = | MkPBox (x: a)
type Tag (a: Type) (p: PBox a): Type = | MkTag
type T: Type = | Mk (p: PBox T) (x: Tag T p) | In (t: T)

theorem f: T → Unit
  | In (Mk p x) => f (Mk (MkPBox (In (In (Mk p x)))) x)
  | Mk (MkPBox t) x => f t
  | In (In t) => f (In t)
