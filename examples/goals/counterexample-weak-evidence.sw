-- A false statement whose hypothesis only short lists satisfy (SW-903):
-- `[0, 1, 2, 3, 4, 5]` is a counterexample, but random lists that long are
-- almost never increasing, so the search finds none. It doesn't say so as if
-- it were good evidence: `check --counterexamples --verbose` says the
-- hypotheses held only for inputs of a few constructors, far fewer than the
-- inputs made, and calls it weak evidence (crates/driver/tests/counterexamples.rs).
import Std (List, Nat)

def increasing: List Nat → Bool
  | Nil => True
  | Cons _ Nil => True
  | Cons a (Cons b rest) => a < b && increasing (Cons b rest)

theorem shortIncreasing (xs: List Nat) (h: increasing xs = True): xs.length < 6 := ?
