--| Both answers against the spec: part 1 adds the versions of every packet
--| in the tree, part 2 computes the spec's value, for every well-formed
--| packet; so, by the parser's guarantee, for every packet the parser reads.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, Exists, Fail, List, Nat, NonEmptyList, Option, Result, Text, Void)

theorem versionSumTotal (packet: Packet): versionSum packet = (packetsIn packet).sumBy versionOf := match packet with
  | Literal version groups => rfl
  | Operator version operation lengthType ({ head = first, tail = rest }) =>
    rewrite List.sumByCons (packetsIn first ++ packetsInAll rest) (Operator version operation lengthType (NonEmptyList.cons first rest)) versionOf,
      List.sumByAppend (packetsIn first) (packetsInAll rest) versionOf, versionSumTotal first, versionSumsTotal rest in omega
  | Comparator version comparison lengthType first second =>
    rewrite List.sumByCons (packetsIn first ++ packetsIn second) (Comparator version comparison lengthType first second) versionOf,
      List.sumByAppend (packetsIn first) (packetsIn second) versionOf, versionSumTotal first, versionSumTotal second in omega

theorem versionSumsTotal (packets: List Packet): versionSums packets = (packetsInAll packets).sumBy versionOf :=
  match packets with
    | [] => rfl
    | [packet, ..rest] => rewrite List.sumByAppend (packetsIn packet) (packetsInAll rest) versionOf, versionSumTotal packet, versionSumsTotal rest in rfl

--| Part 1, for every packet.
theorem part1Correct (packet: Packet): solvePart1 packet = versionTotal packet := versionSumTotal packet

--| A literal's value: its groups, each below 16, read as one binary number.
theorem groupsValue (acc: Nat) (groups: List Nat) (small: groups.all (group => group < 16) = True):
    groups.foldLeft acc (value group => value * 16 + group) = (groups.flatMap (Nat.toBits 4)).foldLeft acc (acc bit => acc * 2 + bit.toNat) :=
  match groups with
    | [] => rfl
    | [group, ..rest] =>
      let fits: group < Nat.pow 2 4 := omega [Bool.andLeft small]
      let ih := groupsValue (acc * 16 + group) rest (Bool.andRight small)
      let inner: List.foldLeft (Nat.toBits 4 group) acc (acc bit => acc * 2 + Bool.toNat bit) = acc * 16 + group :=
        rewrite Nat.fromBitsFrom acc (Nat.toBits 4 group), Nat.fromBitsToBits 4 group fits in rfl
      let step: List.foldLeft (rest.flatMap (Nat.toBits 4)) (List.foldLeft (Nat.toBits 4 group) acc (acc bit => acc * 2 + Bool.toNat bit)) (acc bit => acc * 2 + Bool.toNat bit) =
          List.foldLeft (rest.flatMap (Nat.toBits 4)) (acc * 16 + group) (acc bit => acc * 2 + Bool.toNat bit) :=
        Eq.cong (start => List.foldLeft (rest.flatMap (Nat.toBits 4)) start (acc bit => acc * 2 + Bool.toNat bit)) inner
      let appended: List.foldLeft (Nat.toBits 4 group ++ rest.flatMap (Nat.toBits 4)) acc (acc bit => acc * 2 + Bool.toNat bit) =
          List.foldLeft (rest.flatMap (Nat.toBits 4)) (List.foldLeft (Nat.toBits 4 group) acc (acc bit => acc * 2 + Bool.toNat bit)) (acc bit => acc * 2 + Bool.toNat bit) :=
        List.foldLeftAppend (Nat.toBits 4 group) acc (rest.flatMap (Nat.toBits 4)) (acc bit => acc * 2 + Bool.toNat bit)
      Eq.trans ih (Eq.trans (Eq.sym step) (Eq.sym appended))

--| An operation computes the spec's value from the values it is given.
theorem operationComputes (operation: Operation) (values: NonEmptyList Nat): Computes operation values.toList (operation.apply values) :=
  match operation with
    | Sum => SumOf values.toList
    | Product => ProductOf values.toList
    | Minimum =>
      let found := List.minimumSome values.toList values.minimum (NonEmptyList.minimumToList values)
      MinimumOf found.left found.right
    | Maximum =>
      let found := List.maximumSome values.toList values.maximum (NonEmptyList.maximumToList values)
      MaximumOf found.left found.right

--| A comparison computes the spec's value from the two values it is given.
theorem comparisonCompares (comparison: Comparison) (first: Nat) (second: Nat): Compares comparison first second (comparison.apply first second) :=
  match comparison with
    | GreaterThan =>
      match h: (second < first: Bool) with
        | True => Greater first second (omega [h])
        | False => NotGreater first second (omega [h])
    | LessThan =>
      match h: (first < second: Bool) with
        | True => Less first second (omega [h])
        | False => NotLess first second (omega [h])
    | EqualTo =>
      match h: first == second with
        | True => rewrite h.read in Equal second
        | False => NotEqual first second h.read

--| Part 2: a well-formed packet has the value the program computes.
theorem evaluateCorrect (packet: Packet) (formed: wellFormed packet = True): HasValue packet (evaluate packet) :=
  match packet with
    | Literal version groups =>
      let Both _ groupsOk := formed
      rewrite groupsValue 0 groups.toList groupsOk in LiteralValue version groups
    | Operator version operation lengthType ({ head = first, tail = rest }) =>
      let Both _ (Both _ (Both firstOk restOk)) := formed
      OperationValue [operands := { head = first, tail = rest }]
        (NextValue (evaluateCorrect first firstOk) (evaluateAllCorrect rest restOk))
        (operationComputes operation { head = evaluate first, tail = evaluateAll rest })
    | Comparator version comparison lengthType first second =>
      let Both _ (Both _ (Both firstOk secondOk)) := formed
      ComparisonValue (evaluateCorrect first firstOk) (evaluateCorrect second secondOk)
        (comparisonCompares comparison (evaluate first) (evaluate second))

theorem evaluateAllCorrect (packets: List Packet) (formed: allWellFormed packets = True): Values packets (evaluateAll packets) :=
  match packets with
    | [] => NoValues
    | [packet, ..rest] =>
      let Both first more := formed
      NextValue (evaluateCorrect packet first) (evaluateAllCorrect rest more)

theorem part2Correct (packet: Packet) (formed: wellFormed packet = True): HasValue packet (solvePart2 packet) :=
  evaluateCorrect packet formed

--| Both answers for whatever the parser reads, with no hypothesis left.
theorem part1FromInput (input: Text) (packet: Packet) (parsed: Fail.toResult (() => parsePacket input) = Ok packet): solvePart1 packet = versionTotal packet :=
  part1Correct packet

theorem part2FromInput (input: Text) (packet: Packet) (parsed: Fail.toResult (() => parsePacket input) = Ok packet): HasValue packet (solvePart2 packet) :=
  match parsePacketReads input packet parsed with
    | Witness bits (Witness rest (Both _ (Both _ (Both _ formed)))) => part2Correct packet formed
