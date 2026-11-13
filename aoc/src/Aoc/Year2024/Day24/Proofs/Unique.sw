--| In a well-formed device, a wire carries at most one value
--| (`carriesUnique`), however the gates are wired, loops included, so the
--| device outputs at most one number (`outputsUnique`).

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| With the names distinct, a name starts with one value.
theorem initialUnique ∀ (wire: Wire) (first: Bool) (second: Bool) (pairs: List (Wire, Bool)) (h: List.Distinct (pairs.map .fst))
    (h1: (wire, first) ∈ pairs) (h2: (wire, second) ∈ pairs): first = second := match pairs, h, h1, h2 with
      | [], distinct, inFirst, inSecond => Void.exfalso inFirst
      | [pair, ..rest], Both fresh distinct, Inl isFirst, Inl isSecond => Eq.cong Pair.snd (Eq.trans (Eq.sym isFirst) isSecond)
      | [pair, ..rest], Both fresh distinct, Inl isFirst, Inr inSecond =>
        Void.exfalso (fresh (rewrite isFirst in List.memMap rest (wire, second) inSecond .fst))
      | [pair, ..rest], Both fresh distinct, Inr inFirst, Inl isSecond =>
        Void.exfalso (fresh (rewrite isSecond in List.memMap rest (wire, first) inFirst .fst))
      | [pair, ..rest], Both fresh distinct, Inr inFirst, Inr inSecond => initialUnique wire first second rest distinct inFirst inSecond

--| With the outputs distinct, a wire is the output of one gate.
theorem gateUnique ∀ (first: Gate) (second: Gate) (gates: List Gate) (h: List.Distinct (gates.map .output))
    (h1: first ∈ gates) (h2: second ∈ gates) (same: first.output = second.output): first = second :=
  match gates, h, h1, h2 with
    | [], distinct, inFirst, inSecond => Void.exfalso inFirst
    | [gate, ..rest], Both fresh distinct, Inl isFirst, Inl isSecond => Eq.trans (Eq.sym isFirst) isSecond
    | [gate, ..rest], Both fresh distinct, Inl isFirst, Inr inSecond =>
      Void.exfalso (fresh (rewrite isFirst, same in List.memMap rest second inSecond .output))
    | [gate, ..rest], Both fresh distinct, Inr inFirst, Inl isSecond =>
      Void.exfalso (fresh (rewrite isSecond, <- same in List.memMap rest first inFirst .output))
    | [gate, ..rest], Both fresh distinct, Inr inFirst, Inr inSecond => gateUnique first second rest distinct inFirst inSecond same

--| A wire carries at most one value.
theorem carriesUnique ∀ (device: Device) (wellFormed: WellFormed device) (wire: Wire) (first second: Bool)
    (h: Carries device wire first) (h1: Carries device wire second): first = second := match h, h1 with
      | Starts inFirst, Starts inSecond => initialUnique wire first second device.initial wellFormed.right.left inFirst inSecond
      | Starts inFirst, Fires gate wired onto left right leftCarries rightCarries output =>
        Void.exfalso (wellFormed.right.right gate wired (rewrite onto in List.memMap device.initial (wire, first) inFirst .fst))
      | Fires gate wired onto left right leftCarries rightCarries output, Starts inSecond =>
        Void.exfalso (wellFormed.right.right gate wired (rewrite onto in List.memMap device.initial (wire, second) inSecond .fst))
      | Fires gate wired onto left right leftCarries rightCarries output, Fires otherGate otherWired otherOnto otherLeft otherRight otherLeftCarries otherRightCarries otherOutput =>
        let same := gateUnique gate otherGate device.gates wellFormed.left wired otherWired (Eq.trans onto (Eq.sym otherOnto))
        let leftSame := carriesUnique device wellFormed gate.left left otherLeft leftCarries (rewrite same in otherLeftCarries)
        let rightSame := carriesUnique device wellFormed gate.right right otherRight rightCarries (rewrite same in otherRightCarries)
        rewrite output, otherOutput, same, leftSame, rightSame in rfl

--| A device outputs at most one number.
theorem outputsUnique ∀ (device: Device) (wellFormed: WellFormed device) (first: Nat) (second: Nat)
    (outputsFirst: Outputs device first) (outputsSecond: Outputs device second): first = second :=
  Nat.eqOfTestBit first second (bit =>
    if there: Z bit ∈ device.wires then
      carriesUnique device wellFormed (Z bit) _ _ (outputsFirst.left bit there) (outputsSecond.left bit there)
    else Eq.trans (outputsFirst.right bit there) (Eq.sym (outputsSecond.right bit there)))
