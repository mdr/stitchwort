--| Advent of Code 2020, day 10: a bag of joltage adapters, one rating a
--| line. An adapter takes an input 1, 2 or 3 jolts below its rating; the
--| outlet gives 0 jolts and the device takes 3 more than the highest
--| adapter. Part 1 chains every adapter, lowest first, and multiplies the
--| number of 1-jolt steps by the number of 3-jolt steps; part 2 counts the
--| ways of choosing adapters that still connect the outlet to the device.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day10.main < inputs/2020/day10.txt
--|
--| Part 2 works back from the device: for each adapter, highest first, the
--| number of ways on from it is the sum over the adapters it can feed,
--| which are among the next few higher ones. The proofs, that the parser
--| reads one number a line and that both answers are the puzzle's, are in
--| `Aoc.Year2020.Day10.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2020.Day10.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day10
import Std (Fail, IO, List, NonEmptyList, Option, Parse)

def main(): {IO, Fail} () :=
  let bag := parseBag IO.readAll()
  IO.print "Part 1: ${bag.distribution |> .orFail "the adapters don't make one chain"}"
  IO.print "Part 2: ${bag.arrangements |> .orFail "the bag is empty"}"

--| The adapters' joltage ratings, as listed.
type Bag = { adapters: List Nat }

def parseBag (input: Text): {Fail} Bag := { adapters = Parse.eachLine input Parse.nat }

--| Whether an adapter (or the outlet) rated `lower` can feed one rated
--| `higher`: 1, 2 or 3 jolts up.
def canFeed (lower higher: Nat): Bool := lower < higher && higher <= lower + 3

--| The device's rating, 3 above the highest adapter; none for an empty bag.
def Bag.device (bag: Bag): Option Nat := bag.adapters.nonEmpty |> .map (adapters => adapters.maximum + 3)

--| Joltages from the outlet to the device, each feeding the next.
type Chain = { joltages: List Nat }

def Chain.fits (chain: Chain): Bool := chain.joltages.chain canFeed

def Chain.differences (chain: Chain): List Nat := chain.joltages.zipWithNext.map (step => step.snd - step.fst)

--| Every adapter in the bag, lowest first, between the outlet and the device.
def Bag.chain (bag: Bag) (device: Nat): Chain := { joltages = [0, ..bag.adapters.sort, device] }

--| Part 1: the number of 1-jolt differences times the number of 3-jolt
--| differences, when the whole bag makes a chain.
def Bag.distribution (bag: Bag): Option Nat :=
  bag.device
    |> .flatMap (device =>
      let chain := bag.chain device
      if chain.fits then Some (chain.differences.count (d => d == 1) * chain.differences.count (d => d == 3)) else None)

--| An adapter, and the number of ways on from it to the device.
type Onward = { joltage: Nat, ways: Nat }

--| The ways on from `joltage`, given the onward counts of the adapters
--| above it, lowest first: straight to the device, or through any of them
--| it can feed. Those are all at the front, within 3 jolts.
def waysFrom (device joltage: Nat) (above: List Onward): Nat :=
  (if canFeed joltage device then 1 else 0)
    + (above.takeWhile (next => next.joltage <= joltage + 3)).sumBy (next =>
      if canFeed joltage next.joltage then next.ways else 0)

--| The onward counts of `adapters` (lowest first), worked out from the
--| highest down.
def onwardFrom (device: Nat): (adapters: List Nat) → List Onward
  | [] => []
  | [adapter, ..higher] =>
    let above := onwardFrom device higher
    [{ joltage = adapter, ways = waysFrom device adapter above }, ..above]

--| Part 2: the number of ways from the outlet to the device.
def Bag.arrangements (bag: Bag): Option Nat :=
  bag.device |> .map (device => waysFrom device 0 (onwardFrom device bag.adapters.sort))
