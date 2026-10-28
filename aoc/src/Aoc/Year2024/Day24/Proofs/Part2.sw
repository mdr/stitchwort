-- Part 2 is sound for every device: the swaps it returns, at most four,
-- make the gates pass `isAdder`, so by the adder theorem they add any two
-- numbers of the device's width (`part2Sound`). That the swaps are the
-- only ones that do is not proved: the puzzle promises one answer.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Text, Void)

-- Gates that pass `isAdder` add, and each wire is the output of at most
-- one of them.
theorem adderAdds (gates: List Gate) (bits: Nat) (adder: isAdder gates bits = True): Adds bits gates ∧ wellWired gates = True :=
  let rest := Bool.andRight _ _ adder
  Both (shapeAdds gates bits (DecEq.sound _ _ (Bool.andRight _ _ rest)) (Bool.andLeft _ _ rest)) (Bool.andLeft _ _ adder)

-- What `repair` returns: the swaps it was given, then at most `budget`
-- more, which make the gates an adder.
def Repaired (bits: Nat) (budget: Nat) (gates: List Gate) (swaps: List (Wire, Wire)) (result: List (Wire, Wire)): Prop :=
  ∃ (more: List (Wire, Wire)) => result = List.append swaps more ∧ (more.length ≤ budget ∧ isAdder (applySwaps gates more) bits = True)

-- `repair` on gates that already pass.
theorem repairDone (bits: Nat) (budget: Nat) (gates: List Gate) (swaps: List (Wire, Wire)) (result: List (Wire, Wire))
    (found: (if isAdder gates bits then Some swaps else None) = Some result): Repaired bits budget gates swaps result :=
  match adder: isAdder gates bits with
    | True => Witness Nil (Both (rewrite List.appendNil swaps in Eq.sym (Option.someInjective swaps result found)) (Both (omega) adder))
    | False => Void.exfalso (Option.noneNotSome result found)

theorem repairSound (bits: Nat): (budget: Nat) → (gates: List Gate) → (swaps: List (Wire, Wire)) → (result: List (Wire, Wire)) →
    repair budget bits gates swaps = Some result → Repaired bits budget gates swaps result
  | Zero, gates, swaps, result, found =>
    match checked: checkAdder gates bits with
      | Passes carry => repairDone bits 0 gates swaps result found
      | Faulty fixes => Void.exfalso (Option.noneNotSome result found)
  | Succ fewer, gates, swaps, result, found =>
    match checked: checkAdder gates bits with
      | Passes carry => repairDone bits (Succ fewer) gates swaps result found
      | Faulty fixes =>
        match findMapSome (fix => repair fewer bits (swapOutputs gates fix) (List.append swaps [fix])) result fixes found with
          | Witness fix fixed =>
            match repairSound bits fewer (swapOutputs gates fix) (List.append swaps [fix]) result fixed with
              | Witness more (Both isResult (Both short adder)) =>
                Witness (Cons fix more) (Both (rewrite isResult, List.appendAssoc swaps [fix] more in rfl) (Both (omega) adder))

-- Part 2, sound for every device: the answer names at most four swaps,
-- which make the device's gates add any two numbers as wide as its x
-- wires, each wire the output of at most one gate.
theorem part2Sound (device: Device) (answer: Text) (solved: solvePart2 device = Some answer):
    ∃ (swaps: List (Wire, Wire)) =>
      answer = swapNames swaps
        ∧ (swaps.length ≤ 4 ∧ (Adds device.inputBits (applySwaps device.gates swaps) ∧ wellWired (applySwaps device.gates swaps) = True)) :=
  Option.mapEqSome (repair 4 device.inputBits device.gates []) swapNames answer solved (swaps repaired named =>
    match repairSound device.inputBits 4 device.gates [] swaps repaired with
      | Witness more (Both isSwaps (Both short adder)) =>
        Witness more (Both (Eq.trans (Eq.sym named) (Eq.cong swapNames isSwaps)) (Both short (adderAdds (applySwaps device.gates more) device.inputBits adder))))
