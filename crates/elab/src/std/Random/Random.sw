-- `Random`: a pure pseudo-random generator. The state is a `Nat` below 2^64;
-- each step gives a number and the next state, so a program is replayable
-- from its seed. Get a seed from `IO.randomSeed ()` (fresh each run; 0 under
-- `IO.simulate`), or pass any number in a test.
--
--   def main (): {IO} () :=
--     let (roll, _) := Random.between (IO.randomSeed ()) 1 6
--     IO.print "You rolled ${roll}."
--
-- The generator is SplitMix64 (Steele, Lea and Flood; Vigna's public-domain C
-- version: https://prng.di.unimi.it/splitmix64.c). The 64-bit wraparound of
-- the C code is done with `% 2^64`, and its xor and shift with arithmetic.
-- It is not for cryptography.

-- 2^64, the size of the state.
def Random.modulus: Nat := 18446744073709551616

-- Exclusive or of the lowest `bits` bits of two numbers, one bit at a time.
def Random.xorBits: Nat → Nat → Nat → Nat
  | Zero, a, b => 0
  | Succ n, a, b => (a % 2 + b % 2) % 2 + 2 * Random.xorBits n (a / 2) (b / 2)

-- Exclusive or of two numbers below 2^64.
def Random.xor64 (a: Nat) (b: Nat): Nat := Random.xorBits 64 a b

-- One SplitMix64 step: the output for `state`, and the next state.
def Random.next (state: Nat): Pair Nat Nat :=
  let following := (state + 11400714819323198485) % Random.modulus
  let z1 := (Random.xor64 following (following / 1073741824) * 13787848793156543929) % Random.modulus
  let z2 := (Random.xor64 z1 (z1 / 134217728) * 10723151780598845931) % Random.modulus
  MkPair (Random.xor64 z2 (z2 / 2147483648)) following

-- A number from 0 up to but not including `bound`, and the next state. A
-- `bound` of 0 gives 0. Taking the remainder of 64 bits favours small numbers
-- by a part in 2^64 / bound: nothing for a game's purposes.
def Random.below (state: Nat) (bound: Nat): Pair Nat Nat :=
  let (output, following) := Random.next state
  MkPair (if bound == 0 then 0 else output % Succ (bound - 1)) following

-- A number from `low` to `high`, both included (`low` if `high` is smaller),
-- and the next state.
def Random.between (state: Nat) (low: Nat) (high: Nat): Pair Nat Nat :=
  let (offset, following) := Random.below state (high + 1 - low)
  MkPair (low + offset) following

-- Whether a 1-in-`chances` event happens, and the next state.
def Random.chance (state: Nat) (chances: Nat): Pair Bool Nat :=
  let (roll, following) := Random.below state chances
  MkPair (roll == 0) following

-- The first outputs, as published for the reference implementation: the
-- tests of `rand_xoshiro` seed with 1477776061723855037
-- (https://github.com/rust-random/rngs/blob/master/rand_xoshiro/src/splitmix64.rs).
test "Random.next: reference outputs" :=
  let (a, s1) := Random.next 1477776061723855037
  let (b, s2) := Random.next s1
  let (c, s3) := Random.next s2
  let (d, s4) := Random.next s3
  let (e, s5) := Random.next s4
  a == 1985237415132408290 ∧ b == 2979275885539914483 ∧ c == 13511426838097143398
    ∧ d == 8488337342461049707 ∧ e == 15141737807933549159

-- Seed 0, from the same C code (checked against an independent run of it).
test "Random.next: seed 0" := (Random.next 0).fst == 16294208416658607535
test "Random.next: state moves by the golden gamma" := (Random.next 0).snd == 11400714819323198485
test "Random.xor64" := Random.xor64 12 10 == 6 ∧ Random.xor64 0 18446744073709551615 == 18446744073709551615
test "Random.below: bound 0" := (Random.below 5 0).fst == 0
test "Random.below: in range" := (Random.below 5 10).fst < 10
test "Random.between: in range" :=
  let (n, _) := Random.between 7 3 5
  3 <= n ∧ n <= 5
test "Random.between: one value" := (Random.between 7 4 4).fst == 4
test "Random.chance: 1 in 1" := (Random.chance 3 1).fst
