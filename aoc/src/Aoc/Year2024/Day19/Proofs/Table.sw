--| The program's table holds, for each suffix, the number of towel lists
--| that make it (`tableCorrect`): entry `index` is the suffix after `index`
--| stripes, made by lists of any length up to `count`, once `count` is at
--| least the suffix's length. So the table's first entry is the spec's
--| number of ways (`waysCorrect`).

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

theorem tableCorrect (patterns: List Pattern) (striped: Striped patterns): (design: Design) → (index: Nat) → index ≤ design.length →
    (count: Nat) → design.length - index ≤ count → (waysForSuffixes patterns design).getOr index 0 = matching patterns count (design.drop index)
  | [], Zero, inside, count, enough => Eq.sym (matchingEmpty patterns striped count)
  | [], Succ index, inside, count, enough => Void.exfalso (omega [inside])
  | [first, ..rest], Succ index, inside, count, enough => tableCorrect patterns striped rest index (omega [inside]) count (omega [enough])
  | [first, ..rest], Zero, inside, Zero, enough => Void.exfalso (omega [enough])
  | [first, ..rest], Zero, inside, Succ count, enough =>
    rewrite matchingSucc patterns count [first, ..rest] in
      List.sumByCongMem patterns
        (pattern => if [first, ..rest].startsWith pattern then (waysForSuffixes patterns rest).getOr (pattern.length - 1) 0 else 0)
        (pattern => if [first, ..rest].startsWith pattern then matching patterns count ([first, ..rest].drop pattern.length) else 0)
        (pattern member =>
          match pattern with
            | [] => Void.exfalso (Bool.falseNotTrue (striped [] member))
            | [stripe, ..others] =>
              match starts: [first, ..rest].startsWith [stripe, ..others] with
                | True =>
                  tableCorrect patterns striped rest others.length (omega [List.startsWithLength [first, ..rest] [stripe, ..others] starts]) count
                    (omega [enough])
                | False => rfl)

--| The table's first entry is its entry 0.
theorem firstEntry (patterns: List Pattern): (design: Design) →
    (waysForSuffixes patterns design).headOr 0 = (waysForSuffixes patterns design).getOr 0 0
  | [] => rfl
  | [first, ..rest] => rfl

--| The program counts the puzzle's ways to make any design.
theorem waysCorrect (patterns: List Pattern) (striped: Striped patterns) (design: Design): waysToMake patterns design = ways patterns design :=
  rewrite List.lengthFilter (towelLists patterns design.length) (towels => towels.concat == design), firstEntry patterns design in
    tableCorrect patterns striped design 0 (omega) design.length (omega)
