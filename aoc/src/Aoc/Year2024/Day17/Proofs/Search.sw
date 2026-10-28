-- Part 2's search. Whatever it returns is positive and outputs the target
-- (`lowestSound`), for any output function. For an output function of the
-- loop shape (`LoopShape`), every value that outputs the target is a
-- candidate (`candidatesComplete`), so the search finds one if there is one
-- (`lowestComplete`) and returns the least (`lowestLeast`).

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, List, Nat, Option, Or, Void)

-- `a` is `a / 8` times 8 plus a number below 8, so it is among the values
-- built from `a / 8`.
theorem amongLows (a: Nat): a ∈ List.map (List.range 8) (low => a / 8 * 8 + low) :=
  rewrite Eq.sym (Nat.divModEq a 8 (Nat.succNotZero 7)) at
    List.memMap (List.range 8) (a % 8) (List.memRangeFromIntro (a % 8) 8 0 (Nat.zeroLe (a % 8)) (Nat.modLess a 8 (Nat.succNotZero 7)))
      (low => a / 8 * 8 + low)

-- For an output of the loop shape, every value that outputs `target` is a
-- candidate for it.
theorem candidatesComplete (output: Nat → List Nat) (shape: LoopShape output): (target: List Nat) → (a: Nat) → output a = target → a ∈ candidates output target
  | Nil, a, outputs =>
    match shape a with
      | Witness first same => Void.exfalso (List.consNotNil first _ (Eq.trans (Eq.sym same) outputs))
  | Cons value rest, a, outputs =>
    match shape a with
      | Witness first same =>
        let tail: rest = (if a < 8 then Nil else output (a / 8)) := Eq.cong (list => List.drop list 1) (Eq.trans (Eq.sym outputs) same)
        let high: a / 8 ∈ candidates output rest :=
          match small: a < 8 with
            | True => rewrite tail in Inl (Eq.sym (Nat.divSmall a 8 small))
            | False => candidatesComplete output shape rest (a / 8) (Eq.sym tail)
        List.memFilterIntro _ (candidate => output candidate == Cons value rest) a
          (List.memFlatMapIntro (high => List.map (List.range 8) (low => high * 8 + low)) (a / 8) a (candidates output rest) high (amongLows a))
          (rewrite outputs in DecEq.refl (Cons value rest))

-- What the search returns is positive and outputs the target.
theorem lowestSound (output: Nat → List Nat) (target: List Nat) (a: Nat) (found: lowestOutputting output target = Some a): And (0 < a) (output a = target) :=
  let kept := And.right (List.memFilter _ _ a (And.left (List.minimumSome _ a found)))
  Both (Bool.andLeft _ _ kept) (DecEq.sound (output a) target (Bool.andRight _ _ kept))

-- Every positive value that outputs the target is a final candidate.
theorem finalCandidate (output: Nat → List Nat) (shape: LoopShape output) (target: List Nat) (other: Nat) (positive: 0 < other) (outputs: output other = target):
    other ∈ List.filter (candidates output target) (a => 0 < a ∧ output a == target) :=
  List.memFilterIntro _ (a => 0 < a ∧ output a == target) other (candidatesComplete output shape target other outputs)
    (Bool.andIntro _ _ positive (rewrite outputs in DecEq.refl target))

-- For an output of the loop shape, the search returns at most any positive
-- value that outputs the target.
theorem lowestLeast (output: Nat → List Nat) (shape: LoopShape output) (target: List Nat) (a: Nat) (found: lowestOutputting output target = Some a)
    (other: Nat) (positive: 0 < other) (outputs: output other = target): a ≤ other :=
  And.right (List.minimumSome _ a found) other (finalCandidate output shape target other positive outputs)

-- For an output of the loop shape, the search finds a value if there is one.
theorem lowestComplete (output: Nat → List Nat) (shape: LoopShape output) (target: List Nat) (other: Nat) (positive: 0 < other) (outputs: output other = target):
    ∃ (a: Nat) => lowestOutputting output target = Some a :=
  List.minimumExists _ other (finalCandidate output shape target other positive outputs)
