-- Counting the spec's towel lists: those of at most `count + 1` towels that
-- make a design are the empty list, if the design is empty, and for each
-- pattern the design starts with, that towel followed by a list of at most
-- `count` towels making the rest (`matchingSucc`). This is the recurrence
-- the program's table follows.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

-- Every pattern has at least one stripe.
def Striped (patterns: List Pattern): Prop := (pattern: Pattern) → pattern ∈ patterns → 1 ≤ pattern.length

-- How many lists of at most `count` towels make `design`.
def matching (patterns: List Pattern) (count: Nat) (design: Design): Nat :=
  towelLists patterns count |> .count (towels => towels.concat == design)

-- The lists that start with a towel of `pattern` and make `design`: none,
-- unless the design starts with the pattern, and then those whose other
-- towels make the rest.
theorem matchingAfter (patterns: List Pattern) (count: Nat) (design: Design) (pattern: Pattern):
    (towelLists patterns count).count (towels => List.append pattern towels.concat == design)
      = if design.startsWith pattern then matching patterns count (design.drop pattern.length) else 0 :=
  match starts: design.startsWith pattern with
    | True =>
      List.countCongMem (towelLists patterns count) (towels => List.append pattern towels.concat == design)
        (towels => towels.concat == design.drop pattern.length) (towels member => List.appendEqDrop design pattern starts towels.concat)
    | False =>
      List.countNone (towelLists patterns count) (towels => List.append pattern towels.concat == design)
        (towels member => List.appendNotEq design pattern starts towels.concat)

theorem matchingSucc (patterns: List Pattern) (count: Nat) (design: Design):
    matching patterns (Succ count) design
      = Bool.toNat (Nil == design)
        + patterns.sumBy (pattern => if design.startsWith pattern then matching patterns count (design.drop pattern.length) else 0) :=
  rewrite List.countCons (patterns.flatMap (first => towelLists patterns count |> .map (Cons first))) Nil (towels => towels.concat == design),
    List.countFlatMap (first => towelLists patterns count |> .map (Cons first)) (towels => towels.concat == design) patterns
    in
  Eq.cong (Nat.add (Bool.toNat (Nil == design)))
    (List.sumByCongMem patterns
      (first => (towelLists patterns count |> .map (Cons first)).count (towels => towels.concat == design))
      (pattern => if design.startsWith pattern then matching patterns count (design.drop pattern.length) else 0)
      (pattern member =>
        rewrite List.countMap (towelLists patterns count) (towels => towels.concat == design) (Cons pattern) in
          matchingAfter patterns count design pattern))

-- With every pattern striped, the empty design is made one way, by no
-- towels, however many are allowed.
theorem matchingEmpty (patterns: List Pattern) (striped: Striped patterns): (count: Nat) → matching patterns count Nil = 1
  | Zero => rfl
  | Succ count =>
    rewrite matchingSucc patterns count Nil,
      List.sumByZeroIntro patterns (pattern => if List.startsWith Nil pattern then matching patterns count (List.drop Nil pattern.length) else 0)
        (pattern member =>
          match pattern with
            | Nil => Void.exfalso (Bool.falseNotTrue (striped Nil member))
            | Cons first rest => rfl)
      in rfl
