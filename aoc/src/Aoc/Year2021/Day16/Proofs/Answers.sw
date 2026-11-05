--| Both answers against the spec: part 1 adds the versions of every packet
--| in the tree, part 2 computes the spec's value, for every well-formed
--| packet that keeps the puzzle's promise; so, by the parser's guarantee,
--| for every packet the parser reads.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (..)
import Std (Bool, Decidable, Eq, Exists, Fail, List, Nat, Option, Result, Text, Void)

theorem versionSumTotal: (packet: Packet) → versionSum packet = (packetsIn packet).sumBy versionOf
  | Literal version groups => rfl
  | Operator version operation lengthType subPackets =>
    rewrite List.sumByCons (packetsInAll subPackets) (Operator version operation lengthType subPackets) versionOf, versionSumsTotal subPackets in rfl

theorem versionSumsTotal: (packets: List Packet) → versionSums packets = (packetsInAll packets).sumBy versionOf
  | [] => rfl
  | [packet, ..rest] => rewrite List.sumByAppend (packetsIn packet) (packetsInAll rest) versionOf, versionSumTotal packet, versionSumsTotal rest in rfl

--| Part 1, for every packet.
theorem part1Correct (packet: Packet): solvePart1 packet = versionTotal packet := versionSumTotal packet

--| A literal's value: its groups, each below 16, read as one binary number.
theorem groupsValue (acc: Nat): (groups: List Nat) → groups.all (group => group < 16) = True →
    groups.foldLeft acc (value group => value * 16 + group) = (groups.flatMap (Nat.toBits 4)).foldLeft acc (acc bit => acc * 2 + bit.toNat)
  | [], small => rfl
  | [group, ..rest], small =>
    let fits: group < Nat.pow 2 4 := omega [Bool.andLeft _ _ small]
    let ih := groupsValue (acc * 16 + group) rest (Bool.andRight _ _ small)
    let inner: List.foldLeft (Nat.toBits 4 group) acc (acc bit => acc * 2 + Bool.toNat bit) = acc * 16 + group :=
      rewrite Nat.fromBitsFrom acc (Nat.toBits 4 group), Nat.fromBitsToBits 4 group fits in rfl
    let step: List.foldLeft (rest.flatMap (Nat.toBits 4)) (List.foldLeft (Nat.toBits 4 group) acc (acc bit => acc * 2 + Bool.toNat bit)) (acc bit => acc * 2 + Bool.toNat bit) =
        List.foldLeft (rest.flatMap (Nat.toBits 4)) (acc * 16 + group) (acc bit => acc * 2 + Bool.toNat bit) :=
      Eq.cong (start => List.foldLeft (rest.flatMap (Nat.toBits 4)) start (acc bit => acc * 2 + Bool.toNat bit)) inner
    let appended: List.foldLeft (Nat.toBits 4 group ++ rest.flatMap (Nat.toBits 4)) acc (acc bit => acc * 2 + Bool.toNat bit) =
        List.foldLeft (rest.flatMap (Nat.toBits 4)) (List.foldLeft (Nat.toBits 4 group) acc (acc bit => acc * 2 + Bool.toNat bit)) (acc bit => acc * 2 + Bool.toNat bit) :=
      List.foldLeftAppend (Nat.toBits 4 group) acc (rest.flatMap (Nat.toBits 4)) (acc bit => acc * 2 + Bool.toNat bit)
    Eq.trans ih (Eq.trans (Eq.sym step) (Eq.sym appended))

--| An operation computes the spec's value from the values it is given,
--| when there are as many as it takes.
theorem applyComputes (operation: Operation) (values: List Nat) (fits: fitsOperation operation values.length = True): Computes operation values (apply operation values) :=
  match operation, values with
    | Sum, values => SumOf values
    | Product, values => ProductOf values
    | Minimum, values =>
      match m: List.minimum values with
        | Some least =>
          let found := List.minimumSome values least m
          MinimumOf found.left found.right
        | None =>
          match values with
            | [] => cases
            | [_, .._] => cases
    | Maximum, values =>
      match m: List.maximum values with
        | Some most =>
          let found := List.maximumSome values most m
          MaximumOf found.left found.right
        | None =>
          match values with
            | [] => cases
            | [_, .._] => cases
    | GreaterThan, [first, second] =>
      match h: (second < first: Bool) with
        | True => Greater first second (omega [h])
        | False => NotGreater first second (omega [h])
    | LessThan, [first, second] =>
      match h: (first < second: Bool) with
        | True => Less first second (omega [h])
        | False => NotLess first second (omega [h])
    | EqualTo, [first, second] =>
      match Nat.decEq first second with
        | Yes same => rewrite same in Equal second
        | No different => NotEqual first second different
    | _, _ => cases

theorem lengthEvaluateAll: (packets: List Packet) → (evaluateAll packets).length = packets.length
  | [] => rfl
  | [_, ..rest] => rewrite lengthEvaluateAll rest in rfl

--| Part 2: a well-formed packet that keeps the promise has the value the
--| program computes.
theorem evaluateCorrect: (packet: Packet) → wellFormed packet = True → promised packet = True → HasValue packet (evaluate packet)
  | Literal version groups, formed, kept => rewrite groupsValue 0 groups (Bool.andRight _ _ (Bool.andRight _ _ formed)) in LiteralValue version groups
  | Operator version operation TotalLength subPackets, formed, kept =>
    OperatorValue (evaluateAllCorrect subPackets (Bool.andRight _ _ (Bool.andRight _ _ formed)) (Bool.andRight _ _ kept))
      (applyComputes operation (evaluateAll subPackets) (rewrite lengthEvaluateAll subPackets in Bool.andLeft _ _ kept))
  | Operator version operation Count subPackets, formed, kept =>
    OperatorValue (evaluateAllCorrect subPackets (Bool.andRight _ _ (Bool.andRight _ _ formed)) (Bool.andRight _ _ kept))
      (applyComputes operation (evaluateAll subPackets) (rewrite lengthEvaluateAll subPackets in Bool.andLeft _ _ kept))

theorem evaluateAllCorrect: (packets: List Packet) → allWellFormed packets = True → allPromised packets = True → Values packets (evaluateAll packets)
  | [], formed, kept => NoValues
  | [packet, ..rest], formed, kept =>
    NextValue (evaluateCorrect packet (Bool.andLeft _ _ formed) (Bool.andLeft _ _ kept)) (evaluateAllCorrect rest (Bool.andRight _ _ formed) (Bool.andRight _ _ kept))

theorem part2Correct (packet: Packet) (formed: wellFormed packet = True) (kept: promised packet = True): HasValue packet (solvePart2 packet) :=
  evaluateCorrect packet formed kept

--| Both answers for whatever the parser reads, with no hypothesis left.
theorem part1FromInput (input: Text) (packet: Packet) (parsed: Fail.toResult (() => parsePacket input) = Ok packet): solvePart1 packet = versionTotal packet :=
  part1Correct packet

theorem part2FromInput (input: Text) (packet: Packet) (parsed: Fail.toResult (() => parsePacket input) = Ok packet): HasValue packet (solvePart2 packet) :=
  match parsePacketReads input packet parsed with
    | Witness bits (Witness rest (Both _ (Both _ (Both _ (Both formed kept))))) => part2Correct packet formed kept
