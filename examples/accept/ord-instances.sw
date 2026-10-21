-- The library's `Ord` (docs/proposals/interfaces.md §6.2, stage 3): a
-- comparison with its laws, and the relations `lessThan` and `lessEq` with
-- their decisions. Instances for numbers, characters, texts, booleans,
-- orderings, lists, `Option`, pairs and vectors; `List.sort`,
-- `List.maximum` and `List.minimum` work on any of them.

import Std (Eq, Vec)

test "numbers" := Ord.compare 3 5 == Less
test "integers" := Ord.compare (-3: Int) 2 == Less
test "characters" := Ord.compare 'b' 'a' == Greater
test "texts" := Ord.compare "apple" "banana" == Less
test "booleans" := Ord.compare False True == Less
test "orderings" := Ord.compare Greater Less == Greater
test "lists" := Ord.compare [1, 2] [1, 3] == Less
test "a list before its extensions" := Ord.compare [1] [1, 0] == Less
test "Option, None first" := Ord.compare None (Some 0) == Less
test "pairs" := Ord.compare (1, "b") (1, "a") == Greater

def v12: Vec Nat 2 := VCons 1 (VCons 2 VNil)
def v13: Vec Nat 2 := VCons 1 (VCons 3 VNil)

test "vectors" := Ord.compare v12 v13 == Less

-- Generic sorting.
test "sort numbers" := [5, 3, 9, 1].sort == [1, 3, 5, 9]
test "sort texts" := ["pear", "apple", "fig"].sort == ["apple", "fig", "pear"]
test "sort pairs" := [(2, "a"), (1, "z"), (1, "b")].sort == [(1, "b"), (1, "z"), (2, "a")]
test "sort lists" := [[2], [1, 5], [1]].sort == [[1], [1, 5], [2]]
test "sort Option" := [Some 2, None, Some 1].sort == [None, Some 1, Some 2]

-- Generic maximum and minimum.
test "maximum" := ["b", "c", "a"].maximum == Some "c"
test "minimum" := [(2, True), (1, False)].minimum == Some (1, False)
test "maximum of none" := ([]: List Int).maximum == None

-- The relations are fields: for `Nat` they're `<` and `<=` themselves.
theorem natLessThan: Ord.lessThan 2 3 = (2 < 3) := rfl
theorem natLessEq: Ord.lessEq 3 3 = (3 <= 3) := rfl

-- Decided from the same dictionary.
test "decided" := Decidable.toBool (Ord.decLessThan "a" "b")

-- Another order, passed by name: a named alternative built with
-- `Ord.fromCompare`, which takes the comparison and its three laws.
def descending: Ord Nat :=
  Ord.fromCompare (x y => Nat.compare y x)
    (x y h => Eq.sym (Nat.compareEqual y x h))
    (x y => Nat.compareFlip y x)
    (x y z h1 h2 => Nat.compareTrans z y x h2 h1)

test "descending" := List.sort [ord := descending] [5, 3, 9, 1] == [9, 5, 3, 1]
test "descending maximum" := List.maximum [ord := descending] [5, 3, 9] == Some 3

-- Ordered by a key that tells values apart: `Ord.byKey`.
type Version = { major: Nat, minor: Nat }

def Version.key (v: Version): (Nat, Nat) := (v.major, v.minor)

theorem Version.keyInjective: (v: Version) -> (w: Version) -> Version.key v = Version.key w -> v = w
  | { major = a, minor = b }, { major = c, minor = d }, h =>
    Eq.trans (Eq.cong (t => ({ major = t, minor = b }: Version)) (Eq.cong Pair.fst h))
      (Eq.cong (t => ({ major = c, minor = t }: Version)) (Eq.cong Pair.snd h))

instance Version.instOrd: Ord Version := Ord.byKey Version.key Version.keyInjective

def v1: Version := { major = 1, minor = 9 }
def v2: Version := { major = 2, minor = 0 }

test "versions" := [v2, v1].sort == [v1, v2]
test "newest" := [v1, v2].maximum == Some v2
