-- A `rewrite` whose goal holds a `.field` still waiting for its receiver's
-- type (docs/proposals/postponement.md, step 4.2). `c` is a let-bound
-- lambda's parameter, whose type only `f b` fixes, so when the `rewrite` is
-- elaborated `c.size` is waiting and the rule's left side can't be looked
-- for. The `rewrite` fails, the goal holds an unknown the declaration will
-- still settle, so it waits, whole, and is tried again once `c` is a `Box`.
import Std (Eq, Nat)

type Box = { size: Nat }

theorem addZeroAgain ∀ (n: Nat): n + 0 = n := Nat.addZero n

def sizes (b: Box): b.size + 0 = b.size :=
  let f := c => (rewrite addZeroAgain c.size in rfl: c.size + 0 = c.size)
  f b

-- With `c`'s type written, nothing waits.
def annotated (b: Box): b.size + 0 = b.size :=
  let f := (c: Box) => (rewrite addZeroAgain c.size in rfl: c.size + 0 = c.size)
  f b
