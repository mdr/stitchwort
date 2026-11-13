--| Counting the spec's towel lists: those of at most `count + 1` towels that
--| make a design are the empty list, if the design is empty, and for each
--| pattern the design starts with, that towel followed by a list of at most
--| `count` towels making the rest (`matchingSucc`). This is the recurrence
--| the program's table follows.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| How many lists of at most `count` towels lay down exactly `stripes`.
def matching (patterns: List Pattern) (count: Nat) (stripes: List Stripe): Nat :=
  towelLists patterns count |> .count (towels => laid towels == stripes)

--| The lists that start with a towel of `pattern` and make `design`: none,
--| unless the design starts with the pattern, and then those whose other
--| towels make the rest.
theorem matchingAfter ∀ (patterns: List Pattern) (count: Nat) (stripes: List Stripe) (pattern: Pattern):
    (towelLists patterns count).count (towels => pattern.stripes.toList.append (laid towels) == stripes)
      = if stripes.startsWith pattern.stripes.toList then matching patterns count (stripes.drop pattern.stripes.toList.length) else 0 :=
  match starts: stripes.startsWith pattern.stripes.toList with
    | True =>
      List.countCongMem _ (towels => List.append pattern.stripes.toList (laid towels) == stripes)
        (towels => laid towels == stripes.drop pattern.stripes.toList.length) (towels member => List.appendEqDrop stripes pattern.stripes.toList starts (laid towels))
    | False =>
      List.countNone (towelLists patterns count) (towels => List.append pattern.stripes.toList (laid towels) == stripes)
        (towels member => List.appendNotEq stripes pattern.stripes.toList starts (laid towels))

theorem matchingSucc ∀ (patterns: List Pattern) (count: Nat) (stripes: List Stripe):
    matching patterns (Succ count) stripes
      = Bool.toNat ([] == stripes)
        + patterns.sumBy (pattern => if stripes.startsWith pattern.stripes.toList then matching patterns count (stripes.drop pattern.stripes.toList.length) else 0) :=
  rewrite List.countCons (patterns.flatMap (first => towelLists patterns count |> .map (Cons first))) [] (towels => laid towels == stripes),
    List.countFlatMap (first => towelLists patterns count |> .map (Cons first)) (towels => laid towels == stripes) patterns
    in
  Eq.cong (Nat.add (Bool.toNat ([] == stripes)))
    (List.sumByCongMem patterns
      (first => (towelLists patterns count |> .map (Cons first)).count (towels => laid towels == stripes))
      (pattern => if stripes.startsWith pattern.stripes.toList then matching patterns count (stripes.drop pattern.stripes.toList.length) else 0)
      (pattern member =>
        rewrite List.countMap (towelLists patterns count) (towels => laid towels == stripes) (Cons pattern) in
          matchingAfter patterns count stripes pattern))

--| The empty design is made one way, by no
--| towels, however many are allowed.
theorem matchingEmpty ∀ (patterns: List Pattern) (count: Nat): matching patterns count [] = 1 := match count with
  | Zero => rfl
  | Succ count =>
    rewrite matchingSucc patterns count [],
      List.sumByZeroIntro patterns (pattern => if List.startsWith [] pattern.stripes.toList then matching patterns count (List.drop [] pattern.stripes.toList.length) else 0)
        (pattern member =>
          rfl)
      in rfl
