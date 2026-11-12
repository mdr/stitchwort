--| Part 1: the program's answer is the spec's, and the spec has no other.

namespace Aoc.Year2020.Day10.Proofs
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10.Spec (..)
import Std (Bool, Eq, List, Option, Void)

theorem part1Rules (bag: Bag) (answer: Nat) (found: bag.distribution = Some answer): Part1 bag.adapters answer :=
  match d: bag.device with
    | Some device =>
      let (Witness highest (Both high same)) := deviceHighest bag device d
      match f: (bag.chain device).fits with
        | True =>
          Witness highest (Both high (Witness bag.adapters.sort (Both (List.sortPerm bag.adapters) (Both
            (rewrite <- same, <- fitsConnects bag device in f)
            (rewrite <- same, <- differencesCount [0, ..bag.adapters.sort, device] 1 (omega), <- differencesCount [0, ..bag.adapters.sort, device] 3 (omega) in
              Eq.sym (Option.someInjective found))))))

theorem part1Complete (bag: Bag) (answer: Nat) (spec: Part1 bag.adapters answer): bag.distribution = Some answer :=
  let (Witness highest (Both high (Witness chain (Both perm (Both connects counted))))) := spec
  let isSort: chain = bag.adapters.sort := List.sortOfSortedNat bag.adapters chain (connectsSorted 0 (highest + 3) chain connects) perm
  let fits: (bag.chain (highest + 3)).fits = True := rewrite fitsConnects, <- isSort in connects
  rewrite deviceOfHighest bag highest high in
    match f: (bag.chain (highest + 3)).fits with
      | True =>
        rewrite counted, isSort, <- differencesCount [0, ..bag.adapters.sort, highest + 3] 1 (omega),
          <- differencesCount [0, ..bag.adapters.sort, highest + 3] 3 (omega) in rfl
