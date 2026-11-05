-- `Fail` is an ability for giving up with a message. `need` turns an
-- `Option` into a value or a failure, `fail` stops with a message, and the
-- type says so: `{Fail}`.
import Std (Fail)
import Std.Fail (fail, need, toResult)

type Move =
  | Left (steps: Nat)
  | Right (steps: Nat)

def Move.read (line: Text): {Fail} Move :=
  let (direction, rest) := need line.trim.uncons "expected a move, got nothing"
  let steps := rest.toNatOrFail
  if direction == 'L' then Left steps
  else if direction == 'R' then Right steps
  else fail "expected L or R, got '${line}'"

-- `map` takes a function that may fail, too; the first failure wins.
-- `toResult` is a handler: it turns the failure into an `Err`.
def parse (lines: List Text): Result (List Move) Text :=
  toResult (() => lines.map Move.read)

test "all good" := parse ["L5", " R3"] == Ok [Left 5, Right 3]
test "bad direction" := parse ["L5", "X3"] == Err "expected L or R, got 'X3'"
test "bad number" := parse ["Lx"] == Err "expected a whole number, got 'x'"
