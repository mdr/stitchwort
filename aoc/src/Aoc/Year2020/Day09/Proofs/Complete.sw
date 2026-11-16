--| Part 2 never misses: whenever some contiguous run of at least two
--| numbers sums to the target, the sliding window finds one. It never
--| shrinks past the run's start (the window from there would sum to less
--| than the target) nor grows past its end (the window up to there would
--| sum to at least the target, and be the answer).

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)
import Aoc.Year2020.Day09.Spec (Weakness)

--| The window can't be at the run's start and sum to more than it.
theorem shrinksInside ∀ (numbers: List Nat) (target start length: Nat)
    (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat) (count sum from: Nat)
    (at: front = numbers.drop from)
    (total: sum = (front.take count).sum)
    (notBeyond: from + count ≤ start + length)
    (over: target < sum):
    from ≠ start :=
  same =>
    let within: ((numbers.drop start).take count).sum ≤ ((numbers.drop start).take length).sum :=
      List.sumTakeMono (numbers.drop start) count length (arithmetic)
    let windowSum := rewrite at, same at total then total
    arithmetic

--| The window can't end where the run does without summing to at least
--| the target, being as long as the run or longer.
theorem growsInside ∀ (numbers: List Nat) (target start length: Nat)
    (sums: ((numbers.drop start).take length).sum = target)
    (front: List Nat) (count sum from: Nat)
    (at: front = numbers.drop from)
    (fits: count ≤ front.length)
    (total: sum = (front.take count).sum)
    (notPast: from ≤ start)
    (notBeyond: from + count ≤ start + length)
    (under: sum ≤ target) (unfinished: sum = target → 2 ≤ count → Void)
    (long: 2 ≤ length):
    from + count < start + length :=
  if h: from + count < start + length then h
  else
    let skipped: front.drop (start - from) = numbers.drop start :=
      rewrite at, <- List.dropAdd from (start - from) numbers, (arithmetic: from + (start - from) = start)
    let covered := List.sumDropTakeLe front (start - from) length
    let runSum := rewrite <- skipped at sums then sums
    let whole: (front.take (start - from + length)).sum = sum :=
      rewrite (arithmetic: start - from + length = count), total
    Void.impossible (unfinished (arithmetic) (arithmetic))

theorem runFromComplete ∀ (numbers: List Nat) (target start length: Nat)
    (sums: ((numbers.drop start).take length).sum = target)
    (long: 2 ≤ length)
    (inside: start + length ≤ numbers.length)
    (front: List Nat) (count sum: Nat) (rest: List Nat) (from: Nat)
    (at: front = numbers.drop from)
    (fits: count ≤ front.length)
    (after: rest = front.drop count)
    (total: sum = (front.take count).sum)
    (notPast: from ≤ start)
    (notBeyond: from + count ≤ start + length):
    runFrom target front count sum rest ≠ None
    decreasing front.length + rest.length
:=
  rewrite runFrom.unfold target front count sum rest then
    match c: target < sum with
      | True =>
        let beforeStart := shrinksInside numbers target start length sums front count sum from at total notBeyond c
        match front with
          | [] => Void.impossible (arithmetic [Eq.cong List.length at, List.lengthDrop numbers from (arithmetic)])
          | [first, ..later] =>
            match count with
              | Zero =>
                let empty: sum = 0 := total
                Void.impossible (arithmetic)
              | Succ k =>
                runFromComplete numbers target start length sums long inside later k
                  (sum - first)
                  rest
                  (from + 1)
                  (rewrite List.dropAdd from 1 numbers, <- at)
                  (arithmetic)
                  after
                  (arithmetic [List.sumCons first (later.take k)])
                  (arithmetic)
                  (arithmetic)
      | False =>
        match e: sum == target && 2 <= count with
          | True => none => Option.noneNotSome (front.take count) none.flipped
          | False =>
            let unfinished: sum = target → 2 ≤ count → Void := same twoOrMore => arithmetic
            match rest with
              | [] =>
                let reached: from + count < start + length :=
                  growsInside numbers target start length sums front count sum from at fits total notPast notBeyond
                    (arithmetic)
                    unfinished
                    long
                Void.impossible
                  (arithmetic [
                    List.lengthDrop numbers from (arithmetic),
                    List.lengthDrop front count fits,
                    Eq.cong List.length after,
                    Eq.cong List.length at
                  ])
              | [next, ..more] =>
                let reached: from + count < start + length :=
                  growsInside numbers target start length sums front count sum from at fits total notPast notBeyond
                    (arithmetic)
                    unfinished
                    long
                let (Both taken below) := List.takeOfDropCons front count next more after.flipped
                runFromComplete numbers target start length sums long inside front
                  (count + 1)
                  (sum + next)
                  more
                  from
                  at
                  (arithmetic)
                  (rewrite List.dropAdd count 1 front, <- after)
                  (rewrite taken, List.sumAppend (front.take count) [next] then arithmetic)
                  notPast
                  (arithmetic)

theorem runSummingComplete ∀ (data: XmasData) (target start length: Nat)
    (sums: ((data.numbers.drop start).take length).sum = target)
    (long: 2 ≤ length)
    (inside: start + length ≤ data.numbers.length):
    data.runSumming target ≠ None :=
  runFromComplete data.numbers target start length sums long inside data.numbers 0 0 data.numbers 0 byComputing
    (arithmetic)
    byComputing
    byComputing
    (arithmetic)
    (arithmetic)

--| Whenever the data has a weakness for `invalid`, part 2 finds one.
theorem weaknessComplete ∀ (data: XmasData) (invalid answer: Nat)
    (weak: Weakness data.numbers invalid answer):
    data.weakness invalid ≠ None :=
  let (Witness run (Both (Witness start (Witness length isRun)) (Both long (Both total rest)))) := weak
  let same := List.takeOwnLength (data.numbers.drop start) length
  let short := List.lengthTakeLe (data.numbers.drop start) length
  let sums: ((data.numbers.drop start).take run.length).sum = invalid :=
    rewrite isRun, same then (rewrite isRun at total then total)
  let inside: start + run.length ≤ data.numbers.length :=
    if h: start ≤ data.numbers.length then arithmetic [List.lengthDrop data.numbers start h, Eq.cong List.length isRun]
    else
      let empty: run = [] :=
        rewrite isRun, List.dropPast data.numbers start (arithmetic), List.takeAll [] length (arithmetic)
      Void.impossible (arithmetic [Eq.cong List.length empty])
  match r: data.runSumming invalid with
    | None => Void.impossible (runSummingComplete data invalid start run.length sums long inside r)
    | Some found =>
      let (Both contiguous (Both twoOrMore foundSum)) :=
        runFromSound data.numbers invalid found data.numbers 0 0 data.numbers 0 byComputing
          (arithmetic)
          byComputing
          byComputing
          r
      match found with
        | [x, ..xs] => none => Option.noneNotSome _ none.flipped
