-- Part 1 is complete for well-formed devices: every value a wire carries
-- by the puzzle's rules, the gates settle to (`settledComplete`), so when
-- the device outputs a number, the program reads it (`part1Complete`).
-- Loops need no assumption: a gate in one never fires, in the program or
-- in the spec, and the wires it feeds carry nothing in either.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Option, Ord, Void)

-- Firing gates keeps every wire that had a value.
theorem fireOntoKeeps (values: Values) (wire: Wire): (ready: List Gate) → (settled: Values) → settled.contains wire = True →
    (fireOnto values settled ready).contains wire = True
  | Nil, settled, there => there
  | Cons gate rest, settled, there =>
    fireOntoKeeps values wire rest _ (Map.containsInsertKeeps settled gate.output ((gate.fire values).getOrElse False) wire there)

-- Every gate fired puts a value on its output.
theorem fireOntoAdds (values: Values) (gate: Gate): (ready: List Gate) → (settled: Values) → gate ∈ ready →
    (fireOnto values settled ready).contains gate.output = True
  | Nil, settled, member => Void.exfalso member
  | Cons first rest, settled, Inl same =>
    rewrite <- same in fireOntoKeeps values first.output rest _ (Map.containsInsertSame settled first.output ((first.fire values).getOrElse False))
  | Cons first rest, settled, Inr later => fireOntoAdds values gate rest _ later

-- A filter that drops nothing keeps every element.
theorem filterFull (keep: a → Bool): (xs: List a) → Nat.leq (Succ (xs.filter keep).length) xs.length = False → (x: a) → x ∈ xs → keep x = True
  | Nil, full, x, member => Void.exfalso member
  | Cons first rest, full, x, member =>
    match kept: keep first with
      | False => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (omega [filterNoLonger rest keep]: Nat.leq (Succ (rest.filter keep).length) (Succ rest.length) = True)) full))
      | True =>
        match member with
          | Inl same => rewrite <- same in kept
          | Inr later => filterFull keep rest full x later

-- Settling keeps every wire that had a value.
theorem settleKeeps (wire: Wire) (values: Values) (waiting: List Gate) (there: values.contains wire = True): (settle values waiting).contains wire = True
    decreasing waiting.length
:=
  match fewer: (waiting.filter (gate => ¬(gate.ready values))).length < waiting.length with
    | False => rewrite settleDone values waiting fewer in there
    | True =>
      rewrite settleMore values waiting fewer in
        settleKeeps wire (fireAll values (waiting.filter (gate => gate.ready values))) (waiting.filter (gate => ¬(gate.ready values)))
          (fireOntoKeeps values wire (waiting.filter (gate => gate.ready values)) values there)
          [decreasing := fewer]

-- When the gates have settled, each gate either has put a value on its
-- output or isn't ready: one of its inputs has no value.
theorem settleCovers (device: Device) (values: Values) (waiting: List Gate)
    (covered: (gate: Gate) → gate ∈ device.gates → gate ∈ waiting ∨ values.contains gate.output = True) (gate: Gate) (wired: gate ∈ device.gates):
    (settle values waiting).contains gate.output = True ∨ gate.ready (settle values waiting) = False
    decreasing waiting.length
:=
  match fewer: (waiting.filter (gate => ¬(gate.ready values))).length < waiting.length with
    | False =>
      rewrite settleDone values waiting fewer in
        match covered gate wired with
          | Inl member => Inr (Bool.falseOfNotTrue _ (ready => Bool.falseNotTrue (Eq.trans (Eq.sym (rewrite ready in rfl)) (filterFull (gate => ¬(gate.ready values)) waiting fewer gate member))))
          | Inr there => Inl there
    | True =>
      let next := fireAll values (waiting.filter (gate => gate.ready values))
      let nextCovered: (gate: Gate) → gate ∈ device.gates → gate ∈ waiting.filter (gate => ¬(gate.ready values)) ∨ next.contains gate.output = True :=
        (other otherWired =>
          match covered other otherWired with
            | Inr there => Inr (fireOntoKeeps values other.output (waiting.filter (gate => gate.ready values)) values there)
            | Inl member =>
              match isReady: other.ready values with
                | True => Inr (fireOntoAdds values other (waiting.filter (gate => gate.ready values)) values (List.memFilterIntro waiting _ other member isReady))
                | False => Inl (List.memFilterIntro waiting _ other member (rewrite isReady in rfl)))
      rewrite settleMore values waiting fewer in
        settleCovers device next (waiting.filter (gate => ¬(gate.ready values))) nextCovered gate wired [decreasing := fewer]

-- A key among the pairs is found by `Map.lookupLast`.
theorem lookupLastFound [auto ord: Ord k] (key: k) (value: v): (pairs: List (k, v)) → (key, value) ∈ pairs → ∃ (found: v) => Map.lookupLast key pairs = Some found
  | Nil, member => Void.exfalso member
  | Cons (other, otherValue) rest, member =>
    match later: Map.lookupLast key rest with
      | Some laterValue => Witness laterValue rfl
      | None =>
        match member with
          | Inl same => Witness otherValue (rewrite Eq.cong Pair.fst same, Ord.compareSelf key in rfl)
          | Inr inRest =>
            match lookupLastFound key value rest inRest with
              | Witness found isFound => Void.exfalso (Option.noneNotSome found (Eq.trans (Eq.sym later) isFound))

-- Every wire that carries a value has one once the gates settle.
theorem containsComplete (device: Device) (wire: Wire) (value: Bool): Carries device wire value → device.settled.contains wire = True
  | Starts given =>
    match lookupLastFound wire value device.initial given with
      | Witness found isFound =>
        settleKeeps wire (Map.fromList device.initial) device.gates
          (Map.containsOfGet (Map.fromList device.initial) wire found (Eq.trans (Map.getFromList wire device.initial) isFound))
  | Fires gate wired onto left right leftCarries rightCarries output =>
    let covered := settleCovers device (Map.fromList device.initial) device.gates (other member => Inl member) gate wired
    match covered with
      | Inl there => rewrite <- onto in there
      | Inr notReady =>
        match Map.getOfContains device.settled gate.left (containsComplete device gate.left left leftCarries) with
          | Witness leftValue leftIs =>
            match Map.getOfContains device.settled gate.right (containsComplete device gate.right right rightCarries) with
              | Witness rightValue rightIs => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite leftIs, rightIs in rfl)) notReady))

-- In a well-formed device, every value a wire carries is the value the
-- gates settle to.
theorem settledComplete (device: Device) (wellFormed: WellFormed device) (wire: Wire) (value: Bool) (carries: Carries device wire value):
    device.settled.get wire = Some value :=
  match Map.getOfContains device.settled wire (containsComplete device wire value carries) with
    | Witness found isFound => rewrite isFound, carriesUnique device wellFormed wire found value (settledSound device wire found isFound) carries in rfl

-- `allSome` of options that each have a value.
theorem allSomeMap (f: a → Option b) (g: a → b): (xs: List a) → ((x: a) → x ∈ xs → f x = Some (g x)) → allSome (xs.map f) = Some (xs.map g)
  | Nil, each => rfl
  | Cons x rest, each => rewrite each x (Inl rfl), allSomeMap f g rest (other member => each other (Inr member)) in rfl

-- Part 1, complete for well-formed devices: a number the device outputs is
-- the program's answer.
theorem part1Complete (device: Device) (wellFormed: WellFormed device) (number: Nat) (outputs: Outputs device number): solvePart1 device = Some number :=
  let count := bitCount Wire.zBit device.wires
  let zValue := (bit: Nat) => if device.wires.contains (Z bit) then device.settled.get (Z bit) else Some False
  let each: (bit: Nat) → bit ∈ List.range count → zValue bit = Some (Nat.testBit number bit) := (bit member =>
    match there: device.wires.contains (Z bit) with
      | True =>
        settledComplete device wellFormed (Z bit) _ (outputs.left bit ((List.memContains device.wires (Z bit)).forward there))
      | False =>
        rewrite outputs.right bit (isIn => Bool.trueNotFalse (Eq.trans (Eq.sym ((List.memContains device.wires (Z bit)).backward isIn)) there)) in rfl)
  let bitsAre: device.zBits device.settled = Some ((List.range count).map (Nat.testBit number)) := allSomeMap zValue (Nat.testBit number) (List.range count) each
  rewrite bitsAre in
    Eq.cong Some
      (Nat.eqOfTestBit _ number (bit =>
        match below: bit < count with
          | True =>
            match rangeBits zValue count 0 _ bitsAre bit below with
              | Witness value (Both valueIs bitIs) =>
                rewrite bitIs in Option.someInjective _ _ (Eq.trans (Eq.sym valueIs) (rewrite Nat.addZero bit in each bit (List.memRangeFromIntro bit count 0 (omega) below)))
          | False =>
            rewrite rangeBitsBeyond zValue count 0 _ bitsAre bit (omega) in
              Eq.sym (outputs.right bit (isIn => Bool.trueNotFalse (Eq.trans (Eq.sym (omega [countFromAbove Wire.zBit (Z bit) bit rfl device.wires 0 isIn]: Nat.leq (Succ bit) count = True)) below)))))
