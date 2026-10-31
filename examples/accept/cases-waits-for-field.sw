-- `cases` whose goal holds `.field`s still waiting for their receiver's
-- type (docs/proposals/postponement.md, step 4.2). `g` is a let-bound
-- lambda's parameter, whose type only `p f` fixes, so when `cases` is
-- elaborated `g.a` and `g.b` are waiting and there is nothing to split on.
-- It fails, the goal holds unknowns the declaration will still settle, so
-- it waits, whole, and is tried again once `g` is a `Flags`: it splits
-- `g.a` and `g.b`, and each case computes.
import Std (Bool, Eq)

type Flags = { a: Bool, b: Bool }

def swapped (f: Flags): (f.a ∨ f.b) = (f.b ∨ f.a) :=
  let p := g => (cases: (g.a ∨ g.b) = (g.b ∨ g.a))
  p f

-- With `g`'s type written, nothing waits.
def annotated (f: Flags): (f.a ∨ f.b) = (f.b ∨ f.a) :=
  let p := (g: Flags) => (cases: (g.a ∨ g.b) = (g.b ∨ g.a))
  p f
