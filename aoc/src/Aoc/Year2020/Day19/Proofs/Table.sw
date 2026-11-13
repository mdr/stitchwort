--| The matcher gives the same answer whichever way it finds a rule, so the
--| table `matchesCompletely` looks rules up in (`ruleTable`) may stand for
--| the list the spec reads (`Rules.rule`, `ruleNumbered`).

namespace Aoc.Year2020.Day19.Proofs
import Aoc.Year2020.Day19 (..)
import Std (DecEq, Eq, List, Map, Nat, Option, Void)

theorem tableGet ∀ (entries: List (Nat, Rule)) (number: Nat): (ruleTable entries).get number = entries.lookup number :=
  match entries with
    | [] => rfl
    | [(entryNumber, rule), ..later] =>
      match same: entryNumber == number with
        | True => rewrite same.read in Map.getInsert number rule (ruleTable later)
        | False =>
          Eq.trans
            (Map.getInsertOther entryNumber rule number (equal => same.read (Eq.sym equal)) (ruleTable later))
            (tableGet later number)

--| The table finds the rule the list does.
theorem tableRule ∀ (rules: Rules) (number: Nat): (ruleTable rules.numbered).get number = rules.rule number := tableGet rules.numbered number

--| Where two lookups agree, so do the matches.
theorem leftAfterSame ∀ (first: Nat → Option Rule) (second: Nat → Option Rule) (same: ∀ (number: Nat) => first number = second number)
    (fuel number: Nat) (message: List Char): leftAfterWith first fuel number message = leftAfterWith second fuel number message :=
  match fuel with
    | Zero => rfl
    | Succ more =>
      match looked: second number with
        | None => rewrite same number, looked in rfl
        | Some (Letter letter) => rewrite same number, looked in rfl
        | Some (Alternatives sequences) =>
          rewrite same number, looked in
            List.flatMapCong sequences (sequence => leftAfterAllWith first more sequence message) (sequence => leftAfterAllWith second more sequence message)
              (sequence => leftAfterAllSame first second same more sequence message)

theorem leftAfterAllSame ∀ (first: Nat → Option Rule) (second: Nat → Option Rule) (same: ∀ (number: Nat) => first number = second number)
    (fuel: Nat) (sequence: List Nat) (message: List Char): leftAfterAllWith first fuel sequence message = leftAfterAllWith second fuel sequence message :=
  match sequence with
    | [] => rfl
    | [number, ..later] =>
      rewrite leftAfterSame first second same fuel number message in
        List.flatMapCong (leftAfterWith second fuel number message) (left => leftAfterAllWith first fuel later left) (left => leftAfterAllWith second fuel later left)
          (left => leftAfterAllSame first second same fuel later left)
