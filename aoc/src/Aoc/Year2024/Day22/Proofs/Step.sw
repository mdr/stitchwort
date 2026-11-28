--| The program's step is the puzzle's: `nextSecret` prunes each side before
--| its XOR instead of after it, and skips the middle prune, whose XOR is
--| already below the modulus (`nextSecretEvolves`). `Nat.xor` is the
--| puzzle's bitwise XOR, and nothing else is (`mixBitwise`,
--| `bitwiseXorUnique`).

namespace Aoc.Year2024.Day22.Proofs
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (..)
import Std (Bool, Eq, List, Nat)

--| `mix` is the puzzle's bitwise XOR.
theorem mixBitwise ∀ (value secret: Nat): BitwiseXor value secret (mix value secret) := i =>
  calc bitSet (mix value secret) i
    _ = Nat.testBit (Nat.xor value secret) i := Eq.flipped (Nat.testBitDiv (Nat.xor value secret) i)
    _ = Bool.xor (Nat.testBit value i) (Nat.testBit secret i) := Nat.testBitXor i value secret
    _ = Bool.xor (bitSet value i) (bitSet secret i) := rewrite Nat.testBitDiv value i, Nat.testBitDiv secret i

--| And it is the only number that is.
theorem bitwiseXorUnique ∀ (x y result: Nat) (bitwise: BitwiseXor x y result): result = mix x y :=
  Nat.eqOfTestBit result (mix x y) (i =>
    calc Nat.testBit result i
      _ = bitSet result i := Nat.testBitDiv result i
      _ = Bool.xor (bitSet x i) (bitSet y i) := bitwise i
      _ = Nat.testBit (mix x y) i := Eq.flipped (Eq.trans (Nat.testBitDiv (mix x y) i) (mixBitwise x y i)))

theorem powModulus: Nat.pow 2 24 = modulus := byComputing

--| Pruning a mix is mixing the pruned sides.
theorem pruneMix ∀ (value secret: Nat): prune (mix value secret) = Nat.xor (value % modulus) (secret % modulus) :=
  Nat.xorModPow 24 value secret

theorem belowModulus ∀ (n: Nat): n % modulus < modulus := Nat.modLess n modulus (Nat.succNotZero 16777215)

theorem nextSecretEvolves ∀ (secret: Nat): nextSecret secret = evolve secret :=
  let first := Nat.xor (secret * 64 % modulus) (secret % modulus)
  let firstSmall: first < modulus :=
    Nat.xorBelow 24 (secret * 64 % modulus) (secret % modulus) (belowModulus (secret * 64)) (belowModulus secret)
  let second := Nat.xor (first / 32) first
  let secondSmall: second < modulus := Nat.xorBelow 24 (first / 32) first (arithmetic [firstSmall]) firstSmall
  rewrite pruneMix (secret * 64) secret,
      pruneMix (first / 32) first,
      Nat.modSmall (first / 32) modulus (arithmetic [firstSmall]),
      Nat.modSmall first modulus firstSmall,
      pruneMix (second * 2048) second,
      Nat.modSmall second modulus secondSmall

theorem part1Correct ∀ (buyers: List Nat): solvePart1 buyers = part1 buyers :=
  List.sumByCong buyers (buyer => (secrets buyer).at 2000) (buyer => Nat.iterate 2000 evolve buyer) (buyer =>
    Nat.iterateCong 2000 nextSecret evolve buyer nextSecretEvolves)
