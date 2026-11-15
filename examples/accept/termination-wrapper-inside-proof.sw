-- Where the wrapped value sits may be inside a proof; the wrapper's own
-- descent may not (termination.rs's header, "Relevant data only";
-- docs/reviews/SW-3412-text-rest-relanded.md F2). The inner `MkW2 …` is
-- reached from the parameter through the proof `MkPBox`, by the plain field
-- rule, and `MkW2 r` is a wrapper around a strict part of it, by steps of
-- data. It's no worse than calling `g` on the inner value itself, and since
-- a match on `PBox`'s data field can only produce a proof (E-PROP-ELIM), `g`
-- returns a proof and never runs.
import Std (List, Nat, Unit)
type PBox (a: Type): Prop = | MkPBox (x: a)
type W: Type = | Leaf | Deep (pf: PBox W2)
type W2: Type = | MkW2 (w: List W)
theorem g: W2 → Unit
  | MkW2 [Deep (MkPBox (MkW2 [_, ..r])), .._] => g (MkW2 r)
  | MkW2 _ => Trivial
