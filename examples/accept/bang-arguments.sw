-- A `!` after an operand, with a space before it and none after it, starts a
-- negated argument: `f !x` is `f (!x)` (docs/proposals/negative-arguments.md,
-- stage 3). `!` has no binary meaning, so there is nothing to confuse it with.
import Std (Bool, List)

def keep (b: Bool): Bool := b
def both (a: Bool) (b: Bool): Bool := a && b
type Item = { done: Bool }

test "a name" := (b => keep !b) False = True
test "the same term as the brackets" := keep !False = keep (!False)
theorem sameTerm: keep !False = keep (!False) := rfl
test "a later argument" := both True !False = True
test "two negated arguments" := both !False !False = True
def doneOf (i: Item): Bool := keep !i.done
test "a field" := doneOf { done = True } = False
test "the arguments take one atom each" := both !False !False && True = True
test "a bracket" := keep !(True && False) = True

-- `x !in xs` is its own operator.
test "not in" := 4 !in [1, 2, 3]
test "in, negated" := (2 !in [1, 2, 3]) = False

-- A block line starting `!` is a statement, not an argument of the line above.
def lastOne (a: Bool): Bool :=
  let b := keep a
  !b

test "a block line" := lastOne True = False
