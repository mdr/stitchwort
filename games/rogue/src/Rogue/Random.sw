-- Randomness: the `Random` ability, a seeded handler for it, and `Dice`, the
-- pure rolls one turn makes from one random number.

namespace Rogue

ability Random where
  next: () → {Random} Nat

-- One step of a linear congruential generator (the constants of the C
-- standard's example `rand`), modulo 2^31.
def lcg (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648

-- Answers `next` from a generator started at `seed`: each answer is the top
-- 15 bits of the generator's next state, which are the well-mixed ones.
def seeded (seed: Nat) (prog: () → {Random | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current =>
        let following := lcg current
        resume (following / 65536) following
  run seed

-- The rolls of one turn, all made from one random number, so that a turn
-- performs `Random` exactly once (see Proofs/Step.sw for why that helps).
type Dice = { seed: Nat }

-- Roll number `index` of the turn: a number from 0 up to `most`.
def Dice.upTo (dice: Dice) (index: Nat) (most: Nat): Nat :=
  (lcg (lcg (dice.seed + index * 7919)) / 65536) % (most + 1)

-- Roll number `index`: 1 in `chances`.
def Dice.chance (dice: Dice) (index: Nat) (chances: Nat): Bool := dice.upTo index (chances - 1) == 0
