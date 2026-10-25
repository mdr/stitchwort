-- (run: random) prints a different number each run, so the runner comparisons skip it.
-- A random number: the seed is fresh each run (`IO.randomSeed`), the
-- generator is pure (`Random.below`), and `IO.simulate` gives seed 0.
import Std (IO, Nat, Pair, Random, Text)

def main (): {IO} () :=
  let (roll, _) := Random.between (IO.randomSeed ()) 1 6
  IO.print "You rolled ${roll}."

-- Under `IO.simulate` the seed is 0, so the roll is always the same: the
-- first output for seed 0, 16294208416658607535, is 1 + 16294208416658607535 % 6.
test "main under simulate rolls the same every time" :=
  (IO.simulate [] main).fst == ["You rolled 2."]

test "the seed is 0 under simulate" :=
  (IO.simulate [] (() => IO.randomSeed ())).snd == 0

-- `IO.simulateWith` picks the seed, so a test can drive `main` on any one.
test "simulateWith gives the seed" :=
  (IO.simulateWith 7 [] (() => IO.randomSeed ())).snd == 7

test "main under simulateWith rolls what that seed gives" :=
  (IO.simulateWith 1 [] main).fst == ["You rolled ${(Random.between 1 1 6).fst}."]
