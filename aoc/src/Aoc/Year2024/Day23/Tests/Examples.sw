-- Day 23's tests: the example from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day23.main` doesn't
-- check them.

namespace Aoc.Year2024.Day23.Tests
import Aoc.Year2024.Day23 (..)
import Aoc.Year2024.Day23.Spec (computers, connected, hasT)
import Std (Fail, List, Nat, Result, Set, Text)

def parsed (input: Text): Result Network Text := Fail.toResult (() => parseNetwork input)

-- A network from its connections written as in the input, "kh-tc".
def networkOf (connections: List Text): Network :=
  { connections = connections.map (line => (line.take 2, line.drop 3)) }

def exampleText: Text :=
  "kh-tc\nqp-kh\nde-cg\nka-co\nyn-aq\nqp-ub\ncg-tb\nvc-aq\ntb-ka\nwh-tc\nyn-cg\nkh-ub\nta-co\nde-co\ntc-td\ntb-wq\n"
    ++ "wh-td\nta-ka\ntd-qp\naq-cg\nwq-ub\nub-vc\nde-ta\nwq-aq\nwq-vc\nwh-yn\nka-de\nkh-ta\nco-tc\nwh-qp\ntb-vc\ntd-yn\n"

-- The example's connections, split by hand rather than parsed.
def example: Network := exampleText.split '\n' |> .filter (line => line != "") |> networkOf

-- Sets written as the puzzle lists them, "aq,cg,yn".
def setOf (names: Text): Set Computer := names.split ',' |> Set.fromList

-- The sets as the puzzle lists them: names in order, joined with commas.
def listed (sets: Set (Set Computer)): List Text := sets.toList.map (set => set.toList.joinWith ",")

test "example, part 1" := solvePart1 example == 7
test "example, part 2" := solvePart2 example == "co,de,ka,ta"

-- "In this example, there are 12 such sets of three inter-connected
-- computers".
test "example, every set of three" :=
  listed (setsOfThree example.links)
    == ["aq,cg,yn", "aq,vc,wq", "co,de,ka", "co,de,ta", "co,ka,ta", "de,ka,ta", "kh,qp,ub", "qp,td,wh", "tb,vc,wq", "tc,td,wh", "td,wh,yn", "ub,vc,wq"]

-- "That narrows the list down to 7 sets".
test "example, the sets with a t" :=
  listed (setsOfThree example.links |> .filter mightBeChiefs)
    == ["co,de,ta", "co,ka,ta", "de,ka,ta", "qp,td,wh", "tb,vc,wq", "tc,td,wh", "td,wh,yn"]

-- The spec's sets of three, by brute force over every three computers.
def specSetsOfThree (network: Network): Set (Set Computer) :=
  let names := computers network |> Set.fromList |> .toList
  names
    |> .flatMap (one => names.flatMap (two => names.map (three => Set.fromList [one, two, three])))
    |> Set.fromList
    |> .filter (set => set.size == 3 && set.all (one => set.all (other => one == other || connected network one other)))

test "example, the spec's sets of three agree" :=
  specSetsOfThree example == setsOfThree example.links && (specSetsOfThree example |> .filter hasT |> .size) == 7

-- "Each computer in this set has a connection to every other computer in
-- the set".
test "example, the largest set" := largestClique example.links == setOf "co,de,ka,ta"

test "connections go both ways" := connected example "tc" "kh" && connected example "kh" "tc" && !connected example "kh" "co"

test "no sets of three" :=
  solvePart1 (networkOf ["ta-tb", "tb-tc", "tc-td", "td-ta"]) == 0 && solvePart2 (networkOf ["ta-tb", "tb-tc", "tc-td", "td-ta"]) == "ta,tb"
test "a set of three without a t" := solvePart1 (networkOf ["aa-bb", "bb-cc", "cc-aa"]) == 0
test "a t anywhere in the set counts" := solvePart1 (networkOf ["aa-bb", "bb-tc", "tc-aa"]) == 1
test "t only as the second letter doesn't count" := solvePart1 (networkOf ["at-bt", "bt-ct", "ct-at"]) == 0

-- Four computers all connected make four sets of three, three with ta.
test "four computers all connected" :=
  let network := networkOf ["ta-bb", "ta-cc", "ta-dd", "bb-cc", "bb-dd", "cc-dd"]
  solvePart1 network == 3 && solvePart2 network == "bb,cc,dd,ta"

test "a connection listed twice, both ways" := solvePart1 (networkOf ["ta-bb", "bb-ta", "bb-cc", "cc-ta", "ta-bb"]) == 1

-- A computer connected to itself isn't a set of three with itself.
test "a computer connected to itself" :=
  solvePart1 (networkOf ["ta-ta", "ta-bb"]) == 0 && solvePart2 (networkOf ["ta-ta", "ta-bb"]) == "bb,ta"

-- Two largest sets of the same size: the puzzle says "the largest set", so
-- its inputs have one; the program returns one of them, the first in its
-- search.
test "two largest sets of the same size" :=
  solvePart2 (networkOf ["dd-ee", "ee-ff", "ff-dd", "aa-bb", "bb-cc", "cc-aa"]) == "aa,bb,cc"
    && solvePart2 (networkOf ["dd-ee", "ee-ff", "ff-dd", "aa-bb", "bb-cc", "cc-aa", "cc-dd"]) == "aa,bb,cc"

test "a single connection" := solvePart2 (networkOf ["kh-tc"]) == "kh,tc" && solvePart1 (networkOf ["kh-tc"]) == 0
test "no connections" := solvePart2 (networkOf []) == "" && solvePart1 (networkOf []) == 0

-- A larger set found after a smaller one.
test "the largest set found late" :=
  solvePart2 (networkOf ["aa-bb", "aa-cc", "bb-cc", "zw-zx", "zw-zy", "zw-zz", "zx-zy", "zx-zz", "zy-zz", "aa-zw"]) == "zw,zx,zy,zz"

test "parse" := parsed exampleText == Ok example
test "parse without a final line break" := parsed "kh-tc\nqp-kh" == Ok (networkOf ["kh-tc", "qp-kh"])
test "a capital letter" := parsed "kh-Tc\n" == Err "line 1, column 4: expected a lowercase letter, got 'T'"
test "a name of three letters" := parsed "kh-tcd\n" == Err "line 1, column 6: expected the end of the line, got 'd'"
test "no dash" := parsed "kh tc\n" == Err "line 1, column 3: expected '-', got ' '"
test "no connections to parse" := parsed "" == Err "line 1, column 1: expected a lowercase letter, got the end of the input"
