--| In a well-formed device, a wire carries at most one value
--| (`carriesUnique`), however the gates are wired, loops included, so the
--| device outputs at most one number (`outputsUnique`).

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| With the names distinct, a name starts with one value.
theorem initialUnique ∀ (wire: Wire) (first second: Bool) (pairs: List (Wire, Bool))
    (h: List.Distinct (pairs.map .fst))
    (h1: (wire, first) ∈ pairs)
    (h2: (wire, second) ∈ pairs):
    first = second :=
  match pairs, h, h1, h2 with
    | [], distinct, inFirst, inSecond => inFirst.impossible
    | [pair, ..rest], Both fresh distinct, Inl isFirst, Inl isSecond =>
      Eq.cong Pair.snd (Eq.trans isFirst.flipped isSecond)
    | [pair, ..rest], Both fresh distinct, Inl isFirst, Inr inSecond =>
      Void.impossible (fresh (rewrite isFirst then List.memMap rest (wire, second) inSecond .fst))
    | [pair, ..rest], Both fresh distinct, Inr inFirst, Inl isSecond =>
      Void.impossible (fresh (rewrite isSecond then List.memMap rest (wire, first) inFirst .fst))
    | [pair, ..rest], Both fresh distinct, Inr inFirst, Inr inSecond =>
      initialUnique wire first second rest distinct inFirst inSecond

--| With the outputs distinct, a wire is the output of one gate.
theorem gateUnique ∀ (first second: Gate) (gates: List Gate)
    (h: List.Distinct (gates.map .output))
    (h1: first ∈ gates)
    (h2: second ∈ gates)
    (same: first.output = second.output):
    first = second :=
  match gates, h, h1, h2 with
    | [], distinct, inFirst, inSecond => inFirst.impossible
    | [gate, ..rest], Both fresh distinct, Inl isFirst, Inl isSecond => Eq.trans isFirst.flipped isSecond
    | [gate, ..rest], Both fresh distinct, Inl isFirst, Inr inSecond =>
      Void.impossible (fresh (rewrite isFirst, same then List.memMap rest second inSecond .output))
    | [gate, ..rest], Both fresh distinct, Inr inFirst, Inl isSecond =>
      Void.impossible (fresh (rewrite isSecond, <- same then List.memMap rest first inFirst .output))
    | [gate, ..rest], Both fresh distinct, Inr inFirst, Inr inSecond =>
      gateUnique first second rest distinct inFirst inSecond same

--| A wire carries at most one value.
theorem carriesUnique ∀ (device: Device)
    (wellFormed: WellFormed device)
    (wire: Wire) (first second: Bool)
    (h: Carries device wire first)
    (h1: Carries device wire second):
    first = second :=
  match h, h1 with
    | Starts inFirst, Starts inSecond =>
      initialUnique wire first second device.initial wellFormed.right.left inFirst inSecond
    | Starts inFirst, Fires gate wired onto left right leftCarries rightCarries output =>
      Void.impossible
        (wellFormed.right.right gate wired (rewrite onto then List.memMap device.initial (wire, first) inFirst .fst))
    | Fires gate wired onto left right leftCarries rightCarries output, Starts inSecond =>
      Void.impossible
        (wellFormed.right.right gate wired (rewrite onto then List.memMap device.initial (wire, second) inSecond .fst))
    | Fires gate wired onto left right leftCarries rightCarries output, Fires otherGate otherWired otherOnto otherLeft
          otherRight otherLeftCarries otherRightCarries otherOutput =>
      let same :=
        gateUnique gate otherGate device.gates wellFormed.left wired otherWired (Eq.trans onto otherOnto.flipped)
      let leftSame :=
        carriesUnique device wellFormed gate.left left otherLeft leftCarries (rewrite same then otherLeftCarries)
      let rightSame :=
        carriesUnique device wellFormed gate.right right otherRight rightCarries (rewrite same then otherRightCarries)
      rewrite output, otherOutput, same, leftSame, rightSame

--| A device outputs at most one number.
theorem outputsUnique ∀ (device: Device)
    (wellFormed: WellFormed device) (first second: Nat)
    (outputsFirst: Outputs device first)
    (outputsSecond: Outputs device second):
    first = second :=
  Nat.eqOfTestBit first second (bit =>
    if there: Z bit ∈ device.wires then
      carriesUnique device wellFormed (Z bit) _ _ (outputsFirst.left bit there) (outputsSecond.left bit there)
    else Eq.trans (outputsFirst.right bit there) (outputsSecond.right bit there).flipped)
