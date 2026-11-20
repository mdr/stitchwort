-- An implicit argument fixed only by an explicit argument's type, where
-- another implicit of the same call faces a lambda: `Ends (Nest 2 x) (n =>
-- 2 ≤ n)` against `Ends ?doc ?post`. `?doc` blocks `Ends`'s unfolding while
-- the other side computes, so comparing the unfoldings can't solve it, and
-- `?post` is applied there to a sum, not a variable, so that comparison
-- can't solve `?post` either. The calls' arguments solve both, once that
-- comparison has failed: an unknown function facing a lambda is solved
-- this way only beside an unknown that is data (`?doc`, a `Box`) facing a
-- known argument (SW-4316; SW-4305 for the first-order case).

type Box = | Text (width: Nat) | Nest (by: Nat) (inner: Box)

def Box.size: Box → Nat
  | Text width => width
  | Nest by inner => by + inner.size

def Ends (doc: Box) (post: Nat → Prop): Prop := ∀ (k: Nat) => post (doc.size + k)

theorem endsHolds ∀ [doc: Box] [post: Nat → Prop] (ends: Ends doc post): post doc.size := ends 0

theorem nestEnds ∀ (x: Box) (ends: Ends (Nest 2 x) (n => 2 ≤ n)): 2 ≤ 2 + x.size :=
  let held := endsHolds ends
  held
