-- A number literal with nothing expected waits for its type, as one checked
-- against an unknown type does (stage 7, D2126, in
-- docs/proposals/postponement.md): here inside tuples, which infer their
-- parts, so the list's element type is said only by the record the lambda
-- after it builds. AoC 2021 day 17's list of velocities (SW-978); before,
-- each literal was a `Nat` at once, and `-4` failed.
import Std (Int, List, Nat)

type Velocity = { dx: Int, dy: Int }

def velocities: List Velocity := [(7, 2), (6, 3), (17, -4)].map (((dx, dy)) => { dx, dy })

test "negative kept" := velocities.map (v => v.dy) == [2, 3, -4]

-- A literal's type is an unknown of its own, not one applied to the
-- variables in scope: `one` keeps its type through the `match` on `t`,
-- which substitutes `Node x kids` for `t` in the types in scope.
type Tree = | Node (value: Nat) (kids: List Tree)

def sumTreeLifted (t: Tree): Nat :=
  let one := 1
  let Node x kids := t
  x * one + List.length kids

-- In a `calc`, the first term's literal is resumed once a step has said
-- the chain's type, before the step is decided by computation.
theorem zeroLe ∀ (n m: Nat) (h: n ≤ m): 0 ≤ m := calc 0
  _ ≤ n
  _ ≤ m := h
