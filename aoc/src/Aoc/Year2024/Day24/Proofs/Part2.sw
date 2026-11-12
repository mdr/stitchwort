--| Part 2 is sound for every device: the swaps it returns, at most four,
--| make the gates pass `isAdder`, so by the adder theorem they add any two
--| numbers of the device's width (`part2Sound`). That the swaps are the
--| only ones that do is not proved: the puzzle promises one answer.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Text, Void)

--| Gates that pass `isAdder` add, and each wire is the output of at most
--| one of them.
theorem adderAdds (gates: List Gate) (bits: Nat) (adder: isAdder gates bits = True): Adds bits gates ∧ wellWired gates = True :=
  let rest := Bool.andRight adder
  Both (shapeAdds gates bits (DecEq.sound (Bool.andRight rest)) (Bool.andLeft rest)) (Bool.andLeft adder)

--| What `repair` returns: the swaps it was given, then at most `budget`
--| more, which make the gates an adder.
def Repaired (bits: Nat) (budget: Nat) (gates: List Gate) (swaps: List (Wire, Wire)) (result: List (Wire, Wire)): Prop :=
  ∃ (more: List (Wire, Wire)) => result = List.append swaps more ∧ (more.length ≤ budget ∧ isAdder (applySwaps gates more) bits = True)

--| `repair` on gates that already pass.
theorem repairDone (bits: Nat) (budget: Nat) (gates: List Gate) (swaps: List (Wire, Wire)) (result: List (Wire, Wire))
    (found: (if isAdder gates bits then Some swaps else None) = Some result): Repaired bits budget gates swaps result :=
  match adder: isAdder gates bits with
    | True => Witness [] (Both (rewrite List.appendNil swaps in Eq.sym (Option.someInjective found)) (Both (omega) adder))

theorem repairSound (bits: Nat) (budget: Nat) (gates: List Gate) (swaps result: List (Wire, Wire))
    (found: repair budget bits gates swaps = Some result): Repaired bits budget gates swaps result :=
  match budget with
    | Zero =>
      match checked: checkAdder gates bits with
        | Passes carry => repairDone bits 0 gates swaps result found
    | Succ fewer =>
      match checked: checkAdder gates bits with
        | Passes carry => repairDone bits (Succ fewer) gates swaps result found
        | Faulty fixes suspects =>
          match List.memOfFindMap (fix => repair fewer bits (swapOutputs gates fix) (List.append swaps [fix])) (swapsToTry fixes suspects) result found with
            | Witness fix (Both _ fixed) =>
              match repairSound bits fewer (swapOutputs gates fix) (List.append swaps [fix]) result fixed with
                | Witness more (Both isResult (Both short adder)) =>
                  Witness [fix, ..more] (Both (rewrite isResult, List.appendAssoc swaps [fix] more in rfl) (Both (omega) adder))

--| Part 2, sound for every device: the answer names at most four swaps,
--| which make the device's gates add any two numbers as wide as its x
--| wires, each wire the output of at most one gate.
theorem part2Sound (device: Device) (answer: Text) (solved: solvePart2 device = Some answer):
    ∃ (swaps: List (Wire, Wire)) =>
      answer = swapNames swaps
        ∧ (swaps.length ≤ 4 ∧ (Adds device.inputBits (applySwaps device.gates swaps) ∧ wellWired (applySwaps device.gates swaps) = True)) :=
  Option.mapEqSome (repair 4 device.inputBits device.gates []) swapNames answer solved (swaps repaired named =>
    match repairSound device.inputBits 4 device.gates [] swaps repaired with
      | Witness more (Both isSwaps (Both short adder)) =>
        Witness more (Both (Eq.trans (Eq.sym named) (Eq.cong swapNames isSwaps)) (Both short (adderAdds (applySwaps device.gates more) device.inputBits adder))))

--| The names of the x pairs are x wires, and of the y pairs y wires.
theorem xNamed (bits: Nat) (x: Nat) (wire: Wire) (member: wire ∈ ((List.range 0 bits).map (k => (X k, x.testBit k))).map .fst):
    wire.xBit.isSome = True :=
  match List.memMapElim .fst wire _ member with
    | Witness pair (Both inPairs isWire) =>
      match List.memMapElim (k => (X k, Nat.testBit x k)) pair _ inPairs with
        | Witness k (Both inRange isPair) => rewrite <- isWire, <- isPair in rfl

theorem yNamed (bits: Nat) (y: Nat) (wire: Wire) (member: wire ∈ ((List.range 0 bits).map (k => (Y k, y.testBit k))).map .fst):
    wire.yBit.isSome = True :=
  match List.memMapElim .fst wire _ member with
    | Witness pair (Both inPairs isWire) =>
      match List.memMapElim (k => (Y k, Nat.testBit y k)) pair _ inPairs with
        | Witness k (Both inRange isPair) => rewrite <- isWire, <- isPair in rfl

theorem notXAndY (wire: Wire) (isX: wire.xBit.isSome = True) (isY: wire.yBit.isSome = True): Void :=
  match wire with
    | Other name => Bool.falseNotTrue isX

theorem notInputOutput (wire: Wire) (output: (wire.xBit.isNone ∧ wire.yBit.isNone) = True) (input: (wire.xBit.isSome ∨ wire.yBit.isSome) = True): Void :=
  match wire with
    | Other name => Bool.falseNotTrue input

--| Well-wired gates, with the x and y wires of two numbers as the wires
--| that start with values, make a well-formed device.
theorem wellFormedInputs (bits: Nat) (x: Nat) (y: Nat) (gates: List Gate) (wired: wellWired gates = True):
    WellFormed { initial = inputsFor bits x y, gates } :=
  let xPairs := (List.range 0 bits).map (k => (X k, Nat.testBit x k))
  let yPairs := (List.range 0 bits).map (k => (Y k, Nat.testBit y k))
  let xDistinct: List.Distinct (xPairs.map .fst) :=
    rewrite List.mapMap (List.range 0 bits) .fst (k => (X k, Nat.testBit x k)) in
      List.distinctMap (List.range 0 bits) (List.distinctRangeFrom bits 0) _ (i j same => Option.someInjective (Eq.cong Wire.xBit same))
  let yDistinct: List.Distinct (yPairs.map .fst) :=
    rewrite List.mapMap (List.range 0 bits) .fst (k => (Y k, Nat.testBit y k)) in
      List.distinctMap (List.range 0 bits) (List.distinctRangeFrom bits 0) _ (i j same => Option.someInjective (Eq.cong Wire.yBit same))
  let disjoint: List.Disjoint (xPairs.map .fst) (yPairs.map .fst) :=
    List.allOfMem _ _ (wire inX inY => notXAndY wire (xNamed bits x wire inX) (yNamed bits y wire inY))
  Both ((List.isDistinctIff (gates.map .output)).forward (Bool.andLeft wired))
    (Both (List.distinctMapAppend .fst xPairs yPairs xDistinct yDistinct disjoint)
      (gate member named =>
        let notInput := List.allMember (gate => gate.output.xBit.isNone ∧ gate.output.yBit.isNone) gates (Bool.andRight wired) gate member
        let input: (gate.output.xBit.isSome ∨ gate.output.yBit.isSome) = True :=
          match List.memAppend gate.output (xPairs.map .fst) (yPairs.map .fst) (rewrite <- List.mapAppend xPairs yPairs .fst in named) with
            | Inl inX => rewrite xNamed bits x gate.output inX in rfl
            | Inr inY => rewrite yNamed bits y gate.output inY in Bool.orTrue _
        notInputOutput gate.output notInput input))

--| Part 2, end to end: the device with the swaps the answer names, given
--| any two numbers as wide as its x wires, settles to their sum on its z
--| wires.
theorem part2Correct (device: Device) (answer: Text) (solved: solvePart2 device = Some answer):
    ∃ (swaps: List (Wire, Wire)) =>
      answer = swapNames swaps
        ∧ (swaps.length ≤ 4
          ∧ (∀ (x y: Nat) => x < Nat.pow 2 device.inputBits → y < Nat.pow 2 device.inputBits →
            solvePart1 { initial = inputsFor device.inputBits x y, gates = applySwaps device.gates swaps } = Some (x + y))) :=
  match part2Sound device answer solved with
    | Witness swaps (Both named (Both short (Both adds wired))) =>
      Witness swaps (Both named (Both short (x y xSmall ySmall =>
        part1Complete { initial = inputsFor device.inputBits x y, gates = applySwaps device.gates swaps }
          (wellFormedInputs device.inputBits x y (applySwaps device.gates swaps) wired) (x + y) (adds x y xSmall ySmall))))
