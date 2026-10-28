-- Part 1 is sound for every device: each value the gates settle to is one
-- the wire carries by the puzzle's rules (`settleSound`), so the number
-- read from the z wires is the one the device outputs (`part1Sound`).

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Option, Void)

-- Every value in `values` is one its wire carries.
def Sound (device: Device) (values: Values): Prop := (wire: Wire) → (value: Bool) → values.get wire = Some value → Carries device wire value

theorem initialSound (device: Device): Sound device (Map.fromList device.initial) :=
  (wire value found => Starts (lookupLastMem wire value device.initial (Eq.trans (Eq.sym (Map.getFromList wire device.initial)) found)))

-- The program's gates are the puzzle's.
theorem applyIsGateOutput: (operation: Operation) → (left: Bool) → (right: Bool) → operation.apply left right = gateOutput operation left right
  | And, left, right => cases
  | Or, left, right => cases
  | Xor, left, right => cases

-- A gate that fires outputs what its wire carries.
theorem fireSound (device: Device) (values: Values) (sound: Sound device values) (gate: Gate) (wired: gate ∈ device.gates) (value: Bool)
    (fired: gate.fire values = Some value): Carries device gate.output value :=
  Option.flatMapEqSome (values.get gate.left) (left => values.get gate.right |> .map (right => gate.operation.apply left right)) value fired
    (left leftIs rightPart =>
      Option.mapEqSome (values.get gate.right) (right => gate.operation.apply left right) value rightPart (right rightIs applied =>
        Fires gate wired rfl left right (sound gate.left left leftIs) (sound gate.right right rightIs)
          (Eq.trans (Eq.sym applied) (applyIsGateOutput gate.operation left right))))

-- `fireAll`, inserting into any map.
def fireOnto (values: Values) (settled: Values) (ready: List Gate): Values :=
  ready.foldLeft settled (settled gate => settled.insert gate.output ((gate.fire values).getOrElse False))

theorem fireOntoSound (device: Device) (values: Values) (sound: Sound device values):
    (ready: List Gate) → ((gate: Gate) → gate ∈ ready → gate ∈ device.gates ∧ gate.ready values = True) →
    (settled: Values) → Sound device settled → Sound device (fireOnto values settled ready)
  | Nil, fit, settled, settledSound, wire, value, found => settledSound wire value found
  | Cons gate rest, fit, settled, settledSound, wire, value, found =>
    let gateFits := fit gate (Inl rfl)
    match fired: gate.fire values with
      | None => Void.exfalso (Bool.falseNotTrue gateFits.right)
      | Some output =>
        fireOntoSound device values sound rest (other member => fit other (Inr member)) _
          (other otherValue inMap =>
            match Map.getInsertCases settled gate.output output other otherValue inMap with
              | Inl (Both isOutput isValue) =>
                rewrite isOutput, isValue in fireSound device values sound gate gateFits.left output fired
              | Inr before => settledSound other otherValue before)
          wire value found

-- One round of `settle`: another when some gate is ready, else done.
theorem settleMore (values: Values) (waiting: List Gate)
    (fewer: Nat.leq (Succ (waiting.filter (gate => ¬(gate.ready values))).length) waiting.length = True):
    settle values waiting = settle (fireAll values (waiting.filter (gate => gate.ready values))) (waiting.filter (gate => ¬(gate.ready values))) :=
  rewrite settle.unfold values waiting in
  rewrite fewer in
  rfl

theorem settleDone (values: Values) (waiting: List Gate)
    (done: Nat.leq (Succ (waiting.filter (gate => ¬(gate.ready values))).length) waiting.length = False): settle values waiting = values :=
  rewrite settle.unfold values waiting in
  rewrite done in
  rfl

-- The gates settle to values their wires carry, from values they carry.
theorem settleSound (device: Device) (values: Values) (waiting: List Gate) (sound: Sound device values)
    (wired: (gate: Gate) → gate ∈ waiting → gate ∈ device.gates): Sound device (settle values waiting)
    decreasing waiting.length
:=
  match fewer: (waiting.filter (gate => ¬(gate.ready values))).length < waiting.length with
    | False => rewrite settleDone values waiting fewer in sound
    | True =>
      let fit: (gate: Gate) → gate ∈ waiting.filter (gate => gate.ready values) → gate ∈ device.gates ∧ gate.ready values = True :=
        (gate member =>
          let kept := List.memFilter waiting (gate => gate.ready values) gate member
          Both (wired gate kept.left) kept.right)
      rewrite settleMore values waiting fewer in
        settleSound device (fireAll values (waiting.filter (gate => gate.ready values))) (waiting.filter (gate => ¬(gate.ready values)))
          (fireOntoSound device values sound (waiting.filter (gate => gate.ready values)) fit values sound)
          (gate member => wired gate (List.memFilter waiting (gate => ¬(gate.ready values)) gate member).left)
          [decreasing := fewer]

theorem settledSound (device: Device): Sound device device.settled :=
  settleSound device (Map.fromList device.initial) device.gates (initialSound device) (gate member => member)

-- Part 1, sound for every device: the number read is one the device
-- outputs. (A device whose z wires don't all get values, as in a loop,
-- gives none.)
theorem part1Sound (device: Device) (number: Nat) (solved: solvePart1 device = Some number): Outputs device number :=
  let count := bitCount Wire.zBit device.wires
  let zValue := (bit: Nat) => if device.wires.contains (Z bit) then device.settled.get (Z bit) else Some False
  Option.mapEqSome (zBits device device.settled) fromBits number solved (bits bitsAre isNumber =>
    Both
      (bit member =>
        let below := countFromAbove Wire.zBit (Z bit) bit rfl device.wires 0 member
        match rangeBits zValue count 0 bits bitsAre bit below with
          | Witness value (Both valueIs bitIs) =>
            let isIn := (List.memContains device.wires (Z bit)).backward member
            let found: device.settled.get (Z bit) = Some value := rewrite Nat.addZero bit, isIn at valueIs in valueIs
            rewrite <- isNumber, bitIs in settledSound device (Z bit) value found)
      (bit notMember =>
        match below: bit < count with
          | True =>
            match rangeBits zValue count 0 bits bitsAre bit below with
              | Witness value (Both valueIs bitIs) =>
                let isOut := Bool.falseOfNotTrue _ (isIn => notMember ((List.memContains device.wires (Z bit)).forward isIn))
                let noWire: Some False = Some value := rewrite Nat.addZero bit, isOut at valueIs in valueIs
                rewrite <- isNumber, bitIs in Eq.sym (Option.someInjective False value noWire)
          | False => rewrite <- isNumber in rangeBitsBeyond zValue count 0 bits bitsAre bit (omega)))
