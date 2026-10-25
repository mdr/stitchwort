-- Handlers around partial code (docs/proposals/partial-handlers.md, D1254).
-- A handler may wrap code that might not finish, and then the handler might
-- not finish either, so its result's type says `Partial` too. The handler
-- sees each operation and the rest of the program, as it does around total
-- code; the program's recursive calls pass straight through it.
import Std (Empty, Fail, Nat)

-- Fails at 3, on its way down.
def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Empty.absurd (Fail.stop "three") else if n == 0 then 0 else countdown (n - 1)

-- A handler written in place: the failure becomes a value, but `caught` is
-- still partial, since `countdown` is.
def caught (n: Nat): {Partial} Result Nat Text :=
  handle countdown n with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

-- A handler that never resumes drops the rest of the program, loop and all.
def spin (n: Nat): {Partial} Nat := spin (n + 1)

def stopThenSpin(): {Fail, Partial} Nat :=
  let stopped := Fail.stop "no"
  spin 0

def dropped(): {Partial} Result Nat Text :=
  handle stopThenSpin() with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

-- A handler that says `Partial` in its own type (the roguelike's `seeded`):
-- it takes a partial program, and its result is always partial.
ability Random where
  next: () → {Random} Nat

-- One step of a linear congruential generator, modulo 2^31.
def lcg (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648

def seeded (seed: Nat) (prog: () → {Random, Partial | e} a): {Partial | e} a :=
  let run: Nat → {Partial | e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current =>
        let following := lcg current
        resume (following / 65536) following
  run seed

-- Rolls a die until it shows six: a loop with no bound.
def rollsUntilSix (count: Nat): {Random, Partial} Nat :=
  if next () % 6 == 5 then count + 1 else rollsUntilSix (count + 1)

test "a failure is caught" := caught 5 == Err "three"
test "no failure" := caught 2 == Ok 0
test "stopping drops the loop" := dropped() == Err "no"
-- Seed 1 rolls 3, 5, 4, 2, 2, then a six (a roll is its number mod 6, plus 1).
test "a seeded loop" := seeded 1 (() => rollsUntilSix 0) == 6
test "the same seed, the same rolls" :=
  seeded 7 (() => rollsUntilSix 0) == seeded 7 (() => rollsUntilSix 0)

def showResult: Result Nat Text → Text
  | Ok n => "Ok " ++ Nat.toText n
  | Err msg => "Err " ++ msg

-- Runs on all three runners (`run`, `run --reference`, `run --js`), which
-- print the same.
def main(): {IO, Partial} () :=
  IO.print (showResult (caught 5))
  IO.print (showResult (caught 2))
  IO.print (showResult (dropped()))
  IO.print ("rolls until a six: " ++ Nat.toText (seeded 1 (() => rollsUntilSix 0)))
