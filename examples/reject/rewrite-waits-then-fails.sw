-- expect-error: E-REWRITE-NOTHING
-- A `rewrite` that waits for a `.field` in its goal (docs/proposals/
-- postponement.md, step 4.2) and still finds nothing once the goal is
-- known: its error is its own, against the goal now known, as its annotated
-- twin's is (`annotated`, below, gives the same message).
import Std (Eq, Nat)

type Box = { size: Nat }

def sizes (b: Box): b.size = b.size :=
  let f := c => (rewrite Nat.addComm c.size 1 in rfl: c.size = c.size)
  f b

def annotated (b: Box): b.size = b.size :=
  let f := (c: Box) => (rewrite Nat.addComm c.size 1 in rfl: c.size = c.size)
  f b
