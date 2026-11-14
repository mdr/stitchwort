--| Part 2: working back from the device counts exactly the spec's
--| arrangements, the subsequences of the sorted bag that connect.

namespace Aoc.Year2020.Day10.Proofs
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10.Spec (..)
import Std (Bool, Eq, List, Nat, Option, Void)

--| The spec's count, from `low` (the outlet, or an adapter) through some of
--| `adapters` to the device.
def connecting (device low: Nat) (adapters: List Nat): Nat :=
  (subsequences adapters).count (kept => [low, ..kept, device].chain Takes)

theorem connectingNil ∀ (device low: Nat): connecting device low [] = (if canFeed low device then 1 else 0) :=
  cases in canFeedTakes low device

--| Each arrangement from `low` leaves out the next adapter, or goes
--| through it.
theorem connectingCons ∀ (device low next: Nat) (higher: List Nat):
    connecting device low [next, ..higher]
      = connecting device low higher + (if canFeed low next then connecting device next higher else 0) :=
  let fits := (kept: List Nat) => [low, ..kept, device].chain Takes
  rewrite List.countAppend (subsequences higher) ((subsequences higher).map (kept => [next, ..kept])) fits,
      List.countMap (subsequences higher) fits (kept => [next, ..kept]),
      canFeedTakes low next in
    match t: Takes low next with
      | True => rfl
      | False => rewrite List.countFalse (subsequences higher) in rfl

def lowerFirst (a b: Onward): Bool := a.joltage <= b.joltage

theorem sortedOnward ∀ (device: Nat) (adapters: List Nat)
    (sorted: List.Sorted Nat.leq adapters):
    List.Sorted lowerFirst (onwardFrom device adapters) :=
  match adapters, sorted with
    | [], sorted => Trivial
    | [adapter], sorted => Both Trivial Trivial
    | [adapter, next, ..higher], Both first rest => Both first (sortedOnward device [next, ..higher] rest)

theorem takeWhileKeep ∀ (x: a) (xs: List a) (p: a → Bool)
    (keep: p x = True):
    [x, ..xs].takeWhile p = [x, ..xs.takeWhile p] :=
  rewrite keep in rfl

theorem takeWhileStop ∀ (x: a) (xs: List a) (p: a → Bool) (stop: p x = False): [x, ..xs].takeWhile p = [] :=
  rewrite stop in rfl

--| What each onward count adds from `joltage`.
def through (joltage: Nat) (next: Onward): Nat := if canFeed joltage next.joltage then next.ways else 0

def near (joltage: Nat) (next: Onward): Bool := next.joltage <= joltage + 3

--| In a table sorted by joltage, those `joltage` can feed are all within 3
--| jolts of it at the front, so the program stops looking at the first
--| further one.
theorem cutAbove ∀ (joltage: Nat) (table: List Onward)
    (h1: List.Sorted lowerFirst table):
    (table.takeWhile (near joltage)).sumBy (through joltage) = table.sumBy (through joltage) :=
  match table, h1 with
    | [], sorted => rfl
    | [first, ..rest], Both head sorted =>
      let all := List.sumByCons rest first (through joltage)
      if h: first.joltage <= joltage + 3 then
        let kept := List.sumByCons (rest.takeWhile (near joltage)) first (through joltage)
        rewrite takeWhileKeep first rest (near joltage) (omega) in
          let later := cutAbove joltage rest sorted
          omega
      else
        let beyond := List.sumByZeroIntro rest (through joltage) (next member =>
          let above := List.sortedHeadLe lowerFirst (x y z xy yz => omega) first next rest (Both head sorted) member
          match c: canFeed joltage next.joltage with
            | True => Void.exfalso (omega)
            | False => rfl)
        let skipped: through joltage first = 0 := match c: canFeed joltage first.joltage with
          | True => Void.exfalso (omega)
          | False => rfl
        rewrite takeWhileStop first rest (near joltage) (omega) in omega

theorem waysFull ∀ (device low: Nat) (table: List Onward)
    (sorted: List.Sorted lowerFirst table):
    waysFrom device low table = (if canFeed low device then 1 else 0) + table.sumBy (through low) :=
  rewrite <- cutAbove low table sorted in rfl

--| The onward count from `low`, over sorted adapters above it, is the
--| spec's number of arrangements from it.
theorem onwardCounts ∀ (device: Nat):
    ∀ (adapters: List Nat) => List.Sorted Nat.leq adapters
      → ∀ (low: Nat) => waysFrom device low (onwardFrom device adapters) = connecting device low adapters
  | [], sorted, low => rewrite connectingNil device low in omega
  | [adapter, ..higher], Both first rest, low =>
    let table := onwardFrom device higher
    let here: Onward := { joltage = adapter, ways = waysFrom device adapter table }
    let whole := waysFull device low [here, ..table] (sortedOnward device [adapter, ..higher] (Both first rest))
    let cons := List.sumByCons table here (through low)
    let fromLow := waysFull device low table (sortedOnward device higher rest)
    let viaLow := onwardCounts device higher rest low
    let viaAdapter := onwardCounts device higher rest adapter
    let split := connectingCons device low adapter higher
    match c: canFeed low adapter with
      | True => omega
      | False => omega

theorem part2Rules ∀ (bag: Bag) (answer: Nat) (found: bag.arrangements = Some answer): Part2 bag.adapters answer :=
  match d: bag.device with
    | Some device =>
      let (Witness highest (Both high same)) := deviceHighest bag device d
      Witness highest
        (Both high
          (rewrite <- same in
            Eq.trans
              (Eq.sym (Option.someInjective found))
              (onwardCounts device bag.adapters.sort (List.sortSortedNat bag.adapters) 0)))

theorem part2Complete ∀ (bag: Bag) (answer: Nat) (spec: Part2 bag.adapters answer): bag.arrangements = Some answer :=
  let (Witness highest (Both high counted)) := spec
  rewrite deviceOfHighest bag highest high in
    Eq.cong Some
      (Eq.trans (onwardCounts (highest + 3) bag.adapters.sort (List.sortSortedNat bag.adapters) 0) (Eq.sym counted))
