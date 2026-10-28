-- In a well-formed device, a wire carries at most one value
-- (`carriesUnique`), however the gates are wired, loops included, so the
-- device outputs at most one number (`outputsUnique`).

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

-- With the names distinct, a name starts with one value.
theorem initialUnique (wire: Wire) (first: Bool) (second: Bool): (pairs: List (Wire, Bool)) → List.Distinct (pairs.map (.fst)) →
    (wire, first) ∈ pairs → (wire, second) ∈ pairs → first = second
  | Nil, distinct, inFirst, inSecond => Void.exfalso inFirst
  | Cons pair rest, Both fresh distinct, Inl isFirst, Inl isSecond => Eq.cong Pair.snd (Eq.trans (Eq.sym isFirst) isSecond)
  | Cons pair rest, Both fresh distinct, Inl isFirst, Inr inSecond =>
    Void.exfalso (fresh (rewrite isFirst in List.memMap rest (wire, second) inSecond (.fst)))
  | Cons pair rest, Both fresh distinct, Inr inFirst, Inl isSecond =>
    Void.exfalso (fresh (rewrite isSecond in List.memMap rest (wire, first) inFirst (.fst)))
  | Cons pair rest, Both fresh distinct, Inr inFirst, Inr inSecond => initialUnique wire first second rest distinct inFirst inSecond

-- With the outputs distinct, a wire is the output of one gate.
theorem gateUnique (first: Gate) (second: Gate): (gates: List Gate) → List.Distinct (gates.map (.output)) →
    first ∈ gates → second ∈ gates → first.output = second.output → first = second
  | Nil, distinct, inFirst, inSecond, same => Void.exfalso inFirst
  | Cons gate rest, Both fresh distinct, Inl isFirst, Inl isSecond, same => Eq.trans (Eq.sym isFirst) isSecond
  | Cons gate rest, Both fresh distinct, Inl isFirst, Inr inSecond, same =>
    Void.exfalso (fresh (rewrite isFirst, same in List.memMap rest second inSecond (.output)))
  | Cons gate rest, Both fresh distinct, Inr inFirst, Inl isSecond, same =>
    Void.exfalso (fresh (rewrite isSecond, <- same in List.memMap rest first inFirst (.output)))
  | Cons gate rest, Both fresh distinct, Inr inFirst, Inr inSecond, same => gateUnique first second rest distinct inFirst inSecond same

-- A wire carries at most one value.
theorem carriesUnique (device: Device) (wellFormed: WellFormed device): (wire: Wire) → (first: Bool) → (second: Bool) →
    Carries device wire first → Carries device wire second → first = second
  | wire, first, second, Starts inFirst, Starts inSecond => initialUnique wire first second device.initial wellFormed.right.left inFirst inSecond
  | wire, first, second, Starts inFirst, Fires gate wired onto left right leftCarries rightCarries output =>
    Void.exfalso (wellFormed.right.right gate wired (rewrite onto in List.memMap device.initial (wire, first) inFirst (.fst)))
  | wire, first, second, Fires gate wired onto left right leftCarries rightCarries output, Starts inSecond =>
    Void.exfalso (wellFormed.right.right gate wired (rewrite onto in List.memMap device.initial (wire, second) inSecond (.fst)))
  | wire, first, second, Fires gate wired onto left right leftCarries rightCarries output,
    Fires otherGate otherWired otherOnto otherLeft otherRight otherLeftCarries otherRightCarries otherOutput =>
    let same := gateUnique gate otherGate device.gates wellFormed.left wired otherWired (Eq.trans onto (Eq.sym otherOnto))
    let leftSame := carriesUnique device wellFormed gate.left left otherLeft leftCarries (rewrite same in otherLeftCarries)
    let rightSame := carriesUnique device wellFormed gate.right right otherRight rightCarries (rewrite same in otherRightCarries)
    rewrite output, otherOutput, same, leftSame, rightSame in rfl

-- A device outputs at most one number.
theorem outputsUnique (device: Device) (wellFormed: WellFormed device) (first: Nat) (second: Nat)
    (outputsFirst: Outputs device first) (outputsSecond: Outputs device second): first = second :=
  Nat.eqOfTestBit first second (bit =>
    match List.decMem (Z bit) device.wires with
      | Yes there =>
        carriesUnique device wellFormed (Z bit) _ _ (outputsFirst.left bit there) (outputsSecond.left bit there)
      | No absent => Eq.trans (outputsFirst.right bit absent) (Eq.sym (outputsSecond.right bit absent)))
