-- The program's step is the puzzle's: `nextSecret` prunes each side before
-- its XOR instead of after it, and skips the middle prune, whose XOR is
-- already below the modulus (`nextSecretEvolves`). `Nat.xor` is the
-- puzzle's bitwise XOR, and nothing else is (`mixBitwise`,
-- `bitwiseXorUnique`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Bool, Eq, List, Nat)

-- `mix` is the puzzle's bitwise XOR.
theorem mixBitwise (value: Nat) (secret: Nat): BitwiseXor value secret (mix value secret) :=
  i =>
    Eq.trans (Eq.sym (Nat.testBitDiv (Nat.xor value secret) i))
      (Eq.trans (Nat.testBitXor i value secret) (rewrite Nat.testBitDiv value i, Nat.testBitDiv secret i in rfl))

-- And it is the only number that is.
theorem bitwiseXorUnique (x: Nat) (y: Nat) (result: Nat) (bitwise: BitwiseXor x y result): result = mix x y :=
  Nat.eqOfTestBit result (mix x y)
    (i =>
      Eq.trans (Nat.testBitDiv result i)
        (Eq.trans (bitwise i) (Eq.sym (Eq.trans (Nat.testBitDiv (mix x y) i) (mixBitwise x y i)))))

theorem powModulus: Nat.pow 2 24 = modulus := rfl

-- Pruning a mix is mixing the pruned sides.
theorem pruneMix (value: Nat) (secret: Nat): prune (mix value secret) = Nat.xor (value % modulus) (secret % modulus) := Nat.xorModPow 24 value secret

theorem belowModulus (n: Nat): n % modulus < modulus := Nat.modLess n modulus (Nat.succNotZero 16777215)

theorem nextSecretEvolves (secret: Nat): nextSecret secret = evolve secret :=
  let first := Nat.xor (secret * 64 % modulus) (secret % modulus)
  let firstSmall: first < modulus := Nat.xorBelow 24 (secret * 64 % modulus) (secret % modulus) (belowModulus (secret * 64)) (belowModulus secret)
  let second := Nat.xor (first / 32) first
  let secondSmall: second < modulus := Nat.xorBelow 24 (first / 32) first (omega [firstSmall]) firstSmall
  rewrite pruneMix (secret * 64) secret in
    rewrite pruneMix (first / 32) first, Nat.modSmall (first / 32) modulus (omega [firstSmall]), Nat.modSmall first modulus firstSmall in
      rewrite pruneMix (second * 2048) second, Nat.modSmall second modulus secondSmall in rfl

-- Iterating equal steps gives equal results.
theorem iterateCong (step: Nat → Nat) (other: Nat → Nat) (same: (secret: Nat) → step secret = other secret): (count: Nat) → (secret: Nat) →
    Nat.iterate count step secret = Nat.iterate count other secret
  | Zero, secret => rfl
  | Succ count, secret => rewrite same secret in iterateCong step other same count (other secret)

theorem part1Correct (buyers: List Nat): solvePart1 buyers = part1 buyers :=
  List.sumByCong buyers (buyer => Nat.iterate 2000 nextSecret buyer) (buyer => Nat.iterate 2000 evolve buyer)
    (buyer => iterateCong nextSecret evolve nextSecretEvolves 2000 buyer)
