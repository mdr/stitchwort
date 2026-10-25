-- A failure deep inside partial recursion (docs/proposals/partial-stage-2.md):
-- the first input line picks the loop and the second its depth. Neither
-- overflows a stack, however deep: `descend` waits on each recursive call,
-- `countdown` is a tail call and runs in constant frames. Both fail at the
-- bottom, and `stitchwort run` reports it, after what was printed.
-- (run: fails)
import Std (IO, Fail, Text)

-- Not a tail call: a million levels wait for the failure at the bottom.
def descend: Nat -> {Fail, Partial} Nat
  | 0 => Fail.fail "hit the bottom"
  | Succ below => 1 + descend below

-- A tail call: the failure comes after `depth` iterations.
def countdown: Nat -> {Fail, Partial} ()
  | 0 => Fail.fail "counted down to 0"
  | Succ below => countdown below

def main(): {IO, Fail, Partial} () :=
  let loop := Fail.need (IO.readLine()) "expected the name of a loop"
  let depth := Text.toNatOrFail (Fail.need (IO.readLine()) "expected a depth")
  IO.print "going ${depth} deep"
  if loop == "descend" then IO.print "reached ${descend depth}" else countdown depth
