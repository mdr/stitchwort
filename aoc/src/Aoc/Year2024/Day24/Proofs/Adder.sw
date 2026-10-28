-- The adder theorem: gates of the ripple-carry shape, as `checkAdder`
-- checks it, add. Each bit's gates carry its sum bit and the carry out,
-- given the carry in (`fullAdderCarries`); by induction up the bits, every
-- z wire carries its bit of x + y (`checkFromCarries`).

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

-- Each operation gives the same with its inputs either way round.
theorem gateOutputComm: (operation: Operation) → (a: Bool) → (b: Bool) → gateOutput operation a b = gateOutput operation b a
  | And, a, b => cases
  | Or, a, b => cases
  | Xor, a, b => cases

-- Whether a gate does `operation` on `a` and `b`, either way round, as
-- `outputOf` looks for it.
def doesOn (operation: Operation) (a: Wire) (b: Wire) (gate: Gate): Bool :=
  gate.operation == operation ∧ (gate.left == a ∧ gate.right == b ∨ gate.left == b ∧ gate.right == a)

-- What `outputOf` finds is the output of such a gate.
theorem outputOfFound (gates: List Gate) (operation: Operation) (a: Wire) (b: Wire) (output: Wire)
    (found: outputOf gates operation a b = Some output):
    ∃ (gate: Gate) => gate ∈ gates ∧ gate.output = output ∧ doesOn operation a b gate = True :=
  Option.mapEqSome (gates.find (doesOn operation a b)) (.output) output found (gate isFound onto =>
    let passes := List.findSome gates (doesOn operation a b) gate isFound
    Witness gate (Both passes.right (Both onto passes.left)))

-- The gate `outputOf` finds outputs, onto its wire, what its operation
-- gives for its inputs.
theorem outputCarries (device: Device) (operation: Operation) (a: Wire) (b: Wire) (output: Wire)
    (found: outputOf device.gates operation a b = Some output) (aValue: Bool) (bValue: Bool)
    (aCarries: Carries device a aValue) (bCarries: Carries device b bValue): Carries device output (gateOutput operation aValue bValue) :=
  match outputOfFound device.gates operation a b output found with
    | Witness gate (Both member (Both onto does)) =>
      let operationIs := DecEq.sound gate.operation operation (Bool.andLeft _ _ does)
      Bool.orElim _ _ _ (Bool.andRight _ _ does)
        (straight =>
          Fires gate member onto aValue bValue (rewrite DecEq.sound gate.left a (Bool.andLeft _ _ straight) in aCarries)
            (rewrite DecEq.sound gate.right b (Bool.andRight _ _ straight) in bCarries) (rewrite operationIs in rfl))
        (crossed =>
          Fires gate member onto bValue aValue (rewrite DecEq.sound gate.left b (Bool.andLeft _ _ crossed) in bCarries)
            (rewrite DecEq.sound gate.right a (Bool.andRight _ _ crossed) in aCarries) (rewrite operationIs in gateOutputComm operation aValue bValue))

-- Whether a check passed.
def checkPassed (check: BitCheck): Bool :=
  match check with
    | Passes carry => True
    | Faulty fixes suspects => False

-- The carry wire of a check that passed.
def carryOr (check: BitCheck) (fallback: Wire): Wire :=
  match check with
    | Passes carry => carry
    | Faulty fixes suspects => fallback

theorem faultyNotPasses (fixes: List (Wire, Wire)) (suspects: List Wire) (carry: Wire) (same: Faulty fixes suspects = Passes carry): Void :=
  Bool.falseNotTrue (Eq.cong checkPassed same)

theorem passesInjective (first: Wire) (second: Wire) (same: Passes first = Passes second): first = second :=
  Eq.cong (check => carryOr check first) same

-- A full adder's sum gate and carry gates, as `gateOutput`s.
theorem sumGates (x: Bool) (y: Bool) (carry: Bool): gateOutput Xor (gateOutput Xor x y) carry = Bool.xor (Bool.xor x y) carry := cases

theorem carryGates (x: Bool) (y: Bool) (carry: Bool):
    gateOutput Or (gateOutput And x y) (gateOutput And (gateOutput Xor x y) carry) = carryOut x y carry :=
  cases

-- Bit `bit`'s full adder passing: with the carry wire from below carrying
-- `carry`, the z wire carries the sum bit, and the next carry wire the
-- carry out.
theorem fullAdderCarries (device: Device) (bit: Nat) (carryWire: Wire) (next: Wire)
    (passes: checkFullAdder device.gates bit carryWire = Passes next) (x: Bool) (y: Bool) (carry: Bool)
    (xCarries: Carries device (X bit) x) (yCarries: Carries device (Y bit) y) (carryCarries: Carries device carryWire carry):
    Carries device (Z bit) (Bool.xor (Bool.xor x y) carry) ∧ Carries device next (carryOut x y carry) :=
  match partialIs: outputOf device.gates Xor (X bit) (Y bit) with
    | None => Void.exfalso (faultyNotPasses _ _ next passes)
    | Some partial =>
      match generatedIs: outputOf device.gates And (X bit) (Y bit) with
        | None => Void.exfalso (faultyNotPasses _ _ next passes)
        | Some generated =>
          match sumIs: outputOf device.gates Xor partial carryWire with
            | None => Void.exfalso (faultyNotPasses _ _ next passes)
            | Some sum =>
              match passedIs: outputOf device.gates And partial carryWire with
                | None => Void.exfalso (faultyNotPasses _ _ next passes)
                | Some passed =>
                  match onZ: sum == Z bit with
                    | False => Void.exfalso (faultyNotPasses _ _ next passes)
                    | True =>
                      match carryIs: outputOf device.gates Or generated passed with
                        | None => Void.exfalso (faultyNotPasses _ _ next passes)
                        | Some output =>
                          let partialCarries := outputCarries device Xor (X bit) (Y bit) partial partialIs x y xCarries yCarries
                          let generatedCarries := outputCarries device And (X bit) (Y bit) generated generatedIs x y xCarries yCarries
                          let sumCarries := outputCarries device Xor partial carryWire sum sumIs _ carry partialCarries carryCarries
                          let passedCarries := outputCarries device And partial carryWire passed passedIs _ carry partialCarries carryCarries
                          let carryOutCarries := outputCarries device Or generated passed output carryIs _ _ generatedCarries passedCarries
                          Both (rewrite <- DecEq.sound sum (Z bit) onZ, <- sumGates x y carry in sumCarries)
                            (rewrite <- passesInjective output next passes, <- carryGates x y carry in carryOutCarries)

-- A half adder's gates: a full adder's with no carry in.
theorem halfSumGate (x: Bool) (y: Bool): gateOutput Xor x y = Bool.xor (Bool.xor x y) False := cases

theorem halfCarryGate (x: Bool) (y: Bool): gateOutput And x y = carryOut x y False := cases

-- Bit 0's half adder passing: the z wire carries the exclusive or of the
-- inputs, and the carry wire their and.
theorem halfAdderCarries (device: Device) (carryWire: Wire) (passes: checkHalfAdder device.gates = Passes carryWire) (x: Bool) (y: Bool)
    (xCarries: Carries device (X 0) x) (yCarries: Carries device (Y 0) y):
    Carries device (Z 0) (gateOutput Xor x y) ∧ Carries device carryWire (gateOutput And x y) :=
  match sumIs: outputOf device.gates Xor (X 0) (Y 0) with
    | None => Void.exfalso (faultyNotPasses _ _ carryWire passes)
    | Some sum =>
      match carryIs: outputOf device.gates And (X 0) (Y 0) with
        | None => Void.exfalso (faultyNotPasses _ _ carryWire passes)
        | Some carry =>
          match onZ: sum == Z 0 with
            | False => Void.exfalso (faultyNotPasses _ _ carryWire passes)
            | True =>
              Both (rewrite <- DecEq.sound sum (Z 0) onZ in outputCarries device Xor (X 0) (Y 0) sum sumIs x y xCarries yCarries)
                (rewrite <- passesInjective carry carryWire passes in outputCarries device And (X 0) (Y 0) carry carryIs x y xCarries yCarries)

-- The x and y wires below `bits` carry the bits of `x` and `y`.
def InputsCarry (device: Device) (bits: Nat) (x: Nat) (y: Nat): Prop :=
  (bit: Nat) → bit < bits → Carries device (X bit) (Nat.testBit x bit) ∧ Carries device (Y bit) (Nat.testBit y bit)

-- The z wires below `top` carry the bits of `x + y`.
def ZsCarry (device: Device) (x: Nat) (y: Nat) (top: Nat): Prop := (bit: Nat) → bit < top → Carries device (Z bit) (Nat.testBit (x + y) bit)

-- From bit `bit` up to `top`, each full adder passing: with the carry wire
-- into `bit` carrying the carry, every z wire up to `top` carries its bit,
-- and the last carry wire is `Z top`, carrying the carry into `top`.
theorem checkFromCarries (device: Device) (bits: Nat) (x: Nat) (y: Nat) (inputs: InputsCarry device bits x y):
    (remaining: Nat) → (bit: Nat) → (carryWire: Wire) → (final: Wire) → checkFrom device.gates remaining bit carryWire = Passes final →
    (top: Nat) → top = bit + remaining → top ≤ bits → ZsCarry device x y bit → Carries device carryWire (carryInto x y bit) →
    ZsCarry device x y top ∧ (final = Z top ∧ Carries device final (carryInto x y top))
  | Zero, bit, carryWire, final, passes, top, isTop, within, zs, carryCarries =>
    match onZ: carryWire == Z bit with
      | False => Void.exfalso (faultyNotPasses _ _ final passes)
      | True =>
        let atTop := (omega: top = bit)
        let finalIs := Eq.trans (Eq.sym (passesInjective carryWire final passes)) (DecEq.sound carryWire (Z bit) onZ)
        rewrite atTop in Both zs (Both finalIs (rewrite <- passesInjective carryWire final passes in carryCarries))
  | Succ fewer, bit, carryWire, final, passes, top, isTop, within, zs, carryCarries =>
    match fullIs: checkFullAdder device.gates bit carryWire with
      | Faulty fixes suspects => Void.exfalso (faultyNotPasses fixes _ final passes)
      | Passes next =>
        let bitInputs := inputs bit (omega)
        let carried := fullAdderCarries device bit carryWire next fullIs _ _ _ bitInputs.left bitInputs.right carryCarries
        let zsAbove: ZsCarry device x y (bit + 1) := (k below =>
          match before: k < bit with
            | True => zs k before
            | False => rewrite (omega: k = bit), sumBit x y bit in carried.left)
        checkFromCarries device bits x y inputs fewer (bit + 1) next final passes top (omega) within zsAbove
          (rewrite (omega: bit + 1 = Succ bit) in carried.right)

-- Gates of the ripple-carry shape for `bits` bits: every z wire below
-- `bits` carries its bit of `x + y`, and the last carry wire is `Z bits`,
-- carrying the carry into `bits`.
theorem adderCarries (device: Device) (bits: Nat) (x: Nat) (y: Nat) (inputs: InputsCarry device bits x y) (final: Wire)
    (passes: checkAdder device.gates bits = Passes final):
    ZsCarry device x y bits ∧ (final = Z bits ∧ Carries device final (carryInto x y bits)) :=
  match bits with
    | Zero => Void.exfalso (faultyNotPasses _ _ final passes)
    | Succ higher =>
      match halfIs: checkHalfAdder device.gates with
        | Faulty fixes suspects => Void.exfalso (faultyNotPasses fixes _ final passes)
        | Passes carryWire =>
          let lowInputs := inputs 0 (omega)
          let carried := halfAdderCarries device carryWire halfIs _ _ lowInputs.left lowInputs.right
          let zsLow: ZsCarry device x y 1 := (k below => rewrite (omega: k = 0), sumBit x y 0, <- halfSumGate (Nat.testBit x 0) (Nat.testBit y 0) in carried.left)
          checkFromCarries device (Succ higher) x y inputs higher 1 carryWire final passes (Succ higher) (omega) (omega) zsLow
            (rewrite <- halfCarryGate (Nat.testBit x 0) (Nat.testBit y 0) in carried.right)

-- A wire that carries a value is one of the device's wires.
theorem carriesMentioned (device: Device) (wire: Wire) (value: Bool): Carries device wire value → wire ∈ device.wires
  | Starts given => List.memAppendLeft wire _ _ (List.memMap device.initial (wire, value) given (.fst))
  | Fires gate wired onto left right leftCarries rightCarries output =>
    rewrite <- onto in
      List.memAppendRight gate.output _ _
        (List.memFlatMapIntro (each => [each.left, each.right, each.output]) gate gate.output device.gates wired (Inr (Inr (Inl rfl))))

-- With every z wire of the gates at most `bits`, so is every z wire among
-- them.
theorem zWithinBound (bits: Nat) (bit: Nat): (gates: List Gate) → zWithin gates bits = True →
    Z bit ∈ gates.flatMap (gate => [gate.left, gate.right, gate.output]) → bit ≤ bits
  | Nil, within, member => Void.exfalso member
  | Cons gate rest, within, member =>
    match List.memAppend (Z bit) [gate.left, gate.right, gate.output] _ member with
      | Inl here => allMember (wire => wire.zBit.all (found => found ≤ bits)) [gate.left, gate.right, gate.output] (Z bit) (Bool.andLeft _ _ within) here
      | Inr there => zWithinBound bits bit rest (Bool.andRight _ _ within) there

-- The wires that start with values for an adder are x and y wires.
theorem inputsNotZ (bits: Nat) (x: Nat) (y: Nat) (bit: Nat) (member: Z bit ∈ (inputsFor bits x y).map (.fst)): Void :=
  match List.memMapElim (.fst) (Z bit) _ member with
    | Witness pair (Both given isZ) =>
      match List.memAppend pair _ _ given with
        | Inl xs =>
          match List.memMapElim (k => (X k, Nat.testBit x k)) pair _ xs with
            | Witness k (Both inRange isPair) => Option.noneNotSome bit (Eq.cong Wire.zBit (Eq.trans (Eq.cong Pair.fst isPair) isZ))
        | Inr ys =>
          match List.memMapElim (k => (Y k, Nat.testBit y k)) pair _ ys with
            | Witness k (Both inRange isPair) => Option.noneNotSome bit (Eq.cong Wire.zBit (Eq.trans (Eq.cong Pair.fst isPair) isZ))

-- The adder theorem: gates that pass `checkAdder` for `bits` bits, with no
-- z wire above `bits`, add any two numbers of `bits` bits.
theorem shapeAdds (gates: List Gate) (bits: Nat) (shaped: checkAdder gates bits = Passes (Z bits)) (within: zWithin gates bits = True): Adds bits gates :=
  (x y xSmall ySmall =>
    let device: Device := { initial = inputsFor bits x y, gates }
    let inputs: InputsCarry device bits x y := (k below =>
      Both
        (Starts (List.memAppendLeft _ _ _ (List.memMap (List.range bits) k (List.memRangeFromIntro k bits 0 (omega) (omega)) (k => (X k, Nat.testBit x k)))))
        (Starts (List.memAppendRight _ _ _ (List.memMap (List.range bits) k (List.memRangeFromIntro k bits 0 (omega) (omega)) (k => (Y k, Nat.testBit y k))))))
    let carried := adderCarries device bits x y inputs (Z bits) shaped
    let topBit: Nat.testBit (x + y) bits = carryInto x y bits :=
      rewrite sumBit x y bits, testBitSmall x bits xSmall, testBitSmall y bits ySmall in rfl
    let carriesUpTo: (bit: Nat) → bit ≤ bits → Carries device (Z bit) (Nat.testBit (x + y) bit) := (bit within =>
      match below: bit < bits with
        | True => carried.left bit below
        | False => rewrite (omega: bit = bits), topBit in carried.right.right)
    Both
      (bit member =>
        match List.memAppend (Z bit) _ _ member with
          | Inl initial => Void.exfalso (inputsNotZ bits x y bit initial)
          | Inr inGates => carriesUpTo bit (zWithinBound bits bit gates within inGates))
      (bit notMember =>
        match above: bits < bit with
          | True => testBitAbove (x + y) (Succ bits) bit (omega [Nat.powSucc 2 bits]) above
          | False => Void.exfalso (notMember (carriesMentioned device (Z bit) _ (carriesUpTo bit (omega))))))
