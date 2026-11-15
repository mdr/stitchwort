-- Accepted, and terminates, but only up to proofs (termination.rs's
-- header, "Two orders"; docs/reviews/SW-3412-text-rest-relanded.md F1).
-- In the first clause the new argument holds a value bigger than the old
-- one, inside the proof `MkAny …`: `x`'s type pins `p`, and `PA`'s
-- parameter is a proof, which comparison skips, so the checker takes
-- `Mk <anything> x` for the matched `Mk p x`, and `MkW` of it is a wrapper
-- around a strict part. Height with proofs counted as nothing goes down;
-- height of the terms goes up. It can't loop because the bigger value can't
-- come back: `Any` hides its type, and a proposition whose type could hold
-- a `W` is refused (soundness/termination-relies-on-positivity-*.sw).
import Std (Unit)
type Any: Prop = | MkAny [a: Type] (x: a)
type PA (p: Any): Type = | MkPA
type T: Type = | Mk (p: Any) (x: PA p) | In (t: T)
type W: Type = | MkW (t: T)
theorem f: W → Unit
  | MkW (In (Mk p x)) => f (MkW (Mk (MkAny (MkW (In (In (Mk p x))))) x))
  | MkW (In (In t)) => f (MkW (In t))
  | MkW (Mk p x) => Trivial
