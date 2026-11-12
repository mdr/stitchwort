--| Part 2 proved: the program's index of the rules by colour gives each
--| colour the contents the spec reads off the rules, so its count of the
--| bags inside is the spec's, at every depth; when it gives an answer, that
--| is the puzzle's.

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07 (Spec)
import Std (Eq, Exists, Fail, List, Map, Nat, Option, Result, Void)

theorem contentsAgree (rules: List Rule) (colour: Colour): ({ all = rules }: Rules).book.contentsOf colour = Spec.contentsOf rules colour :=
  rewrite Map.getGroupBy Rule.colour colour rules,
    List.filterCongMem rules (rule => Map.Spec.sameKey colour rule.colour) (rule => rule.colour == colour)
      (rule member => Map.Spec.sameKeyDecide colour rule.colour) in
    match List.filter rules (rule => rule.colour == colour) with
      | [] => rfl
      | [first, ..rest] => rfl

theorem bagsAgree (rules: List Rule) (depth: Nat) (colour: Colour): ({ all = rules }: Rules).book.bagsToDepth depth colour = Spec.bagsWithin rules depth colour :=
  match depth with
    | 0 => rfl
    | Succ depth =>
      rewrite contentsAgree rules colour,
        List.mapCong (Spec.contentsOf rules colour)
          (content => ({ all = rules }: Rules).book.bagsToDepth depth content.colour |> .map (inside => content.count * (1 + inside)))
          (content => Spec.bagsWithin rules depth content.colour |> .map (inside => content.count * (1 + inside)))
          (content => rewrite bagsAgree rules depth content.colour in rfl) in
        rfl

--| When part 2 gives an answer, the rules settle the total at some depth,
--| and it is theirs.
theorem part2Rules (rules: Rules) (total: Nat) (solved: Fail.toResult (() => solvePart2 rules) = Ok total): Spec.Part2 rules.all total :=
  match e: rules.book.bagsToDepth (rules.all.length + 1) shinyGold with
    | Some found => Witness (rules.all.length + 1) (rewrite <- bagsAgree rules.all (rules.all.length + 1) shinyGold, e, Result.okInjective solved in rfl)

-- The spec's total doesn't depend on the depth it was settled at.

theorem allSomeKeeps (f: a → Option b) (g: a → Option b) (keeps: ∀ (x: a) (v: b) => f x = Some v → g x = Some v)
    (xs: List a) (ys: List b) (found: List.allSome (xs.map f) = Some ys): List.allSome (xs.map g) = Some ys :=
  match xs with
    | [] => found
    | [x, ..rest] =>
      match fx: f x with
        | Some v =>
          match r: List.allSome (rest.map f) with
            | Some vs => rewrite keeps x v fx, allSomeKeeps f g keeps rest vs r in found

theorem bagsWithinDeeper (rules: List Rule) (depth: Nat) (colour: Colour) (total: Nat)
    (settled: Spec.bagsWithin rules depth colour = Some total): Spec.bagsWithin rules (Succ depth) colour = Some total :=
  match depth with
    | Succ depth =>
      let shallow := (content: Content) => Spec.bagsWithin rules depth content.colour |> .map (inside => content.count * (1 + inside))
      let deep := (content: Content) => Spec.bagsWithin rules (Succ depth) content.colour |> .map (inside => content.count * (1 + inside))
      let keeps: ∀ (content: Content) (v: Nat) => shallow content = Some v → deep content = Some v :=
        content v found =>
          match e: Spec.bagsWithin rules depth content.colour with
            | Some inside => rewrite bagsWithinDeeper rules depth content.colour inside e in found
      match r: List.allSome ((Spec.contentsOf rules colour).map shallow) with
        | Some counts => rewrite allSomeKeeps shallow deep keeps (Spec.contentsOf rules colour) counts r in settled

theorem bagsWithinLater (rules: List Rule) (depth: Nat) (colour: Colour) (total: Nat) (settled: Spec.bagsWithin rules depth colour = Some total)
    (more: Nat): Spec.bagsWithin rules (depth + more) colour = Some total :=
  match more with
    | 0 => rewrite Nat.addZero depth in settled
    | Succ more => bagsWithinDeeper rules (depth + more) colour total (bagsWithinLater rules depth colour total settled more)

--| Part 2's total is unique: rules that settle it at two depths settle it
--| the same.
theorem part2Unique (rules: List Rule) (one: Nat) (other: Nat) (first: Spec.Part2 rules one) (second: Spec.Part2 rules other): one = other :=
  let (Witness depth settled) := first
  let (Witness otherDepth otherSettled) := second
  Option.someInjective
    (Eq.trans (Eq.sym (bagsWithinLater rules depth Spec.shinyGold one settled otherDepth))
      (rewrite Nat.addComm depth otherDepth in bagsWithinLater rules otherDepth Spec.shinyGold other otherSettled depth))
