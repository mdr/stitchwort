--| The spec looks for towel lists only up to the design's length. That loses
--| none: a design is `possible` exactly when some list of towels, of any
--| length, each with one of the patterns, has the design's stripes in order
--| (`possibleIff`), since every towel has a stripe.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (And, Bool, DecEq, Exists, Iff, List, Nat, NonEmptyList, Void)

--| Every towel in the list has one of the patterns.
def FromPatterns (patterns: List Pattern) (towels: List Pattern): Prop := List.All (towel => towel ∈ patterns) towels

--| `towels`, laid end to end, make `design`.
def Makes (patterns: List Pattern) (towels: List Pattern) (design: Design): Prop :=
  (FromPatterns patterns towels) ∧ (laid towels = design.stripes)

--| The spec's lists are of the patterns and no longer than `count`.
theorem fromTowelLists ∀ (patterns: List Pattern) (count: Nat) (towels: List Pattern) (h: towels ∈ towelLists patterns count):
    (FromPatterns patterns towels) ∧ (towels.length ≤ count) := match count, h with
      | Zero, Inl empty => rewrite <- empty in Both Trivial (omega)
      | Zero, Inr none => Void.exfalso none
      | Succ count, Inl empty => rewrite <- empty in Both Trivial (omega)
      | Succ count, Inr later =>
        List.anyElim (first => towels ∈ (towelLists patterns count |> .map (Cons first))) ((FromPatterns patterns towels) ∧ (towels.length ≤ Succ count))
          patterns (List.memFlatMapElim (first => towelLists patterns count |> .map (Cons first)) towels patterns later)
          (first firstMember mapped =>
            List.anyElim (rest => [first, ..rest] = towels) ((FromPatterns patterns towels) ∧ (towels.length ≤ Succ count)) (towelLists patterns count)
              (List.memMapAny (towelLists patterns count) (Cons first) towels mapped)
              (rest restMember made =>
                let restFacts := fromTowelLists patterns count rest restMember
                rewrite <- made in Both (Both firstMember restFacts.left) (omega [restFacts.right])))

--| Every list of the patterns, no longer than `count`, is one of the spec's.
theorem inTowelLists ∀ (patterns: List Pattern) (count: Nat) (towels: List Pattern) (from: FromPatterns patterns towels) (short: towels.length ≤ count):
    towels ∈ towelLists patterns count := match count, towels, from with
      | Zero, [], from => Inl rfl
      | Succ count, [], from => Inl rfl
      | Succ count, [first, ..rest], Both firstMember restFrom =>
        Inr (List.memFlatMapIntro (first => towelLists patterns count |> .map (Cons first)) first [first, ..rest] patterns firstMember
          (List.memMap (towelLists patterns count) rest (inTowelLists patterns count rest restFrom (omega [short])) (Cons first)))

--| There are no more towels than stripes.
theorem towelsAtMostStripes ∀ (patterns: List Pattern) (towels: List Pattern) (from: FromPatterns patterns towels):
    towels.length ≤ (laid towels).length := match towels, from with
      | [], from => omega
      | [first, ..rest], Both firstMember restFrom =>
        omega [List.lengthAppend first.stripes.toList (laid rest), NonEmptyList.lengthPos first.stripes, towelsAtMostStripes patterns rest restFrom]

--| Whether a list of lists has any (as `possible` asks).
def hasSome (lists: List (List Pattern)): Bool := !lists.isEmpty

theorem someMember ∀ (lists: List (List Pattern)) (some: hasSome lists = True): Exists (List Pattern) (list => list ∈ lists) :=
  match lists with
    | [first, ..rest] => Witness first (Inl rfl)

theorem memberSome ∀ (lists: List (List Pattern)) (list: List Pattern) (member: list ∈ lists): hasSome lists = True :=
  match lists with
    | [first, ..rest] => rfl

--| "Not all designs will be possible": a design is possible exactly when
--| some towels of the patterns make it.
theorem possibleIff ∀ (patterns: List Pattern) (design: Design):
    (possible patterns design = True) ↔ (Exists (List Pattern) (towels => Makes patterns towels design)) := {
  forward = found =>
    Exists.map
      (towels member =>
        let filtered := List.memFilter (towelLists patterns design.stripes.length) (towels => laid towels == design.stripes) member
        Both (fromTowelLists patterns design.stripes.length towels filtered.left).left filtered.right.read)
      (someMember (arrangements patterns design) found),
  backward = made =>
    Exists.elim made (towels (Both from stripes) =>
      memberSome (arrangements patterns design) towels
        (List.memFilterIntro (towelLists patterns design.stripes.length) (towels => laid towels == design.stripes)
          (inTowelLists patterns design.stripes.length towels from (rewrite <- stripes in towelsAtMostStripes patterns towels from))
          (rewrite stripes in DecEq.refl design.stripes)))
}
