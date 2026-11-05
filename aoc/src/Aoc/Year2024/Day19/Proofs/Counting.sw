--| Counting the spec's towel lists: those of at most `count + 1` towels that
--| make a design are the empty list, if the design is empty, and for each
--| pattern the design starts with, that towel followed by a list of at most
--| `count` towels making the rest (`matchingSucc`). This is the recurrence
--| the program's table follows.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

--| Every pattern has at least one stripe.
def Striped (patterns: List Pattern): Prop := (pattern: Pattern) → pattern ∈ patterns → 1 ≤ pattern.stripes.length

--| How many lists of at most `count` towels lay down exactly `stripes`.
def matching (patterns: List Pattern) (count: Nat) (stripes: List Stripe): Nat :=
  towelLists patterns count |> .count (towels => laid towels == stripes)

--| The lists that start with a towel of `pattern` and make `design`: none,
--| unless the design starts with the pattern, and then those whose other
--| towels make the rest.
theorem matchingAfter (patterns: List Pattern) (count: Nat) (stripes: List Stripe) (pattern: Pattern):
    (towelLists patterns count).count (towels => pattern.stripes.append (laid towels) == stripes)
      = if stripes.startsWith pattern.stripes then matching patterns count (stripes.drop pattern.stripes.length) else 0 :=
  match starts: stripes.startsWith pattern.stripes with
    | True =>
      List.countCongMem (towelLists patterns count) (towels => List.append pattern.stripes (laid towels) == stripes)
        (towels => laid towels == stripes.drop pattern.stripes.length) (towels member => List.appendEqDrop stripes pattern.stripes starts (laid towels))
    | False =>
      List.countNone (towelLists patterns count) (towels => List.append pattern.stripes (laid towels) == stripes)
        (towels member => List.appendNotEq stripes pattern.stripes starts (laid towels))

theorem matchingSucc (patterns: List Pattern) (count: Nat) (stripes: List Stripe):
    matching patterns (Succ count) stripes
      = Bool.toNat ([] == stripes)
        + patterns.sumBy (pattern => if stripes.startsWith pattern.stripes then matching patterns count (stripes.drop pattern.stripes.length) else 0) :=
  rewrite List.countCons (patterns.flatMap (first => towelLists patterns count |> .map (Cons first))) [] (towels => laid towels == stripes),
    List.countFlatMap (first => towelLists patterns count |> .map (Cons first)) (towels => laid towels == stripes) patterns
    in
  Eq.cong (Nat.add (Bool.toNat ([] == stripes)))
    (List.sumByCongMem patterns
      (first => (towelLists patterns count |> .map (Cons first)).count (towels => laid towels == stripes))
      (pattern => if stripes.startsWith pattern.stripes then matching patterns count (stripes.drop pattern.stripes.length) else 0)
      (pattern member =>
        rewrite List.countMap (towelLists patterns count) (towels => laid towels == stripes) (Cons pattern) in
          matchingAfter patterns count stripes pattern))

--| With every pattern striped, the empty design is made one way, by no
--| towels, however many are allowed.
theorem matchingEmpty (patterns: List Pattern) (striped: Striped patterns): (count: Nat) → matching patterns count [] = 1
  | Zero => rfl
  | Succ count =>
    rewrite matchingSucc patterns count [],
      List.sumByZeroIntro patterns (pattern => if List.startsWith [] pattern.stripes then matching patterns count (List.drop [] pattern.stripes.length) else 0)
        (pattern member =>
          match pattern with
            | { stripes = [] } => Void.exfalso (Bool.falseNotTrue (striped { stripes = [] } member))
            | { stripes = [first, ..rest] } => rfl)
      in rfl
