--| The program's tests in the spec's words: which adapter feeds which, the
--| device, and a chain that connects is sorted.

namespace Aoc.Year2020.Day10.Proofs
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10.Spec (..)
import Std (Bool, Eq, List, Nat, NonEmptyList, Option, Void)

theorem canFeedTakes (lower: Nat) (higher: Nat): canFeed lower higher = Takes lower higher := cases

theorem fitsConnects (bag: Bag) (device: Nat): (bag.chain device).fits = Connects bag.adapters.sort device :=
  List.chainCong [0, ..bag.adapters.sort, device] canFeed Takes canFeedTakes

theorem deviceHighest (bag: Bag) (device: Nat) (found: bag.device = Some device): ∃ (highest: Nat) => Highest bag.adapters highest ∧ device = highest + 3 :=
  match a: bag.adapters with
    | [first, ..rest] =>
      let ordered: NonEmptyList Nat := [first, ..rest]
      Witness ordered.maximum
        (Both (Both (NonEmptyList.maximumMem ordered) (x member => NonEmptyList.maximumLe ordered x member)) (Eq.sym (Option.someInjective found)))

theorem deviceOfHighest (bag: Bag) (highest: Nat) (high: Highest bag.adapters highest): bag.device = Some (highest + 3) :=
  match a: bag.adapters with
    | [] => Void.exfalso high.left
    | [first, ..rest] =>
      let ordered: NonEmptyList Nat := [first, ..rest]
      let below := NonEmptyList.maximumLe ordered highest high.left
      let above := high.right ordered.maximum (NonEmptyList.maximumMem ordered)
      Eq.cong (top => Some (top + 3)) (omega: ordered.maximum = highest)

theorem differencesCount (joltages: List Nat) (difference: Nat) (positive: 1 ≤ difference):
    ({ joltages }: Chain).differences.count (d => d == difference) = differencesOf joltages difference :=
  rewrite List.countMap joltages.zipWithNext (d => d == difference) (step => step.snd - step.fst) in
    List.countCongMem joltages.zipWithNext _ _ (step member => cases)

theorem connectsSorted (low: Nat) (device: Nat) (chain: List Nat) (connects: List.chain [low, ..chain, device] Takes = True): List.Sorted Nat.leq chain :=
  match chain with
    | [] => Trivial
    | [x, ..rest] =>
      let later := Bool.andRight connects
      Both
        (match rest with
          | [] => Trivial
          | [y, ..more] =>
            let fed: canFeed x y = True := rewrite canFeedTakes in Bool.andLeft later
            omega)
        (connectsSorted x device rest later)
