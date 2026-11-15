-- expect-error: E-TERMINATION
-- A wrapper over a proposition parameter, at a different proposition on
-- each call: `Box (Chain k)` to `Box (Chain (Succ k))`. The one field is
-- still a proof at every instance (its declared type is in `Prop`), so
-- `MkBox n` isn't smaller, whatever the instance.
import Std (Nat, Void)

type Box (a: Prop): Type = | MkBox (h: a)

type Chain: Nat → Prop = | Link [k: Nat] (next: Chain (Succ k)): Chain k

def f [k: Nat]: Box (Chain k) → Void
  | MkBox (Link n) => f (MkBox n)
