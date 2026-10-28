-- The spec looks for towel lists only up to the design's length. That loses
-- none: a design is `possible` exactly when some list of towels, of any
-- length, each with one of the patterns, has the design's stripes in order
-- (`possibleIff`), since every towel has a stripe.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (And, Bool, DecEq, Exists, Iff, List, Nat, Void)

-- Every towel in the list has one of the patterns.
def FromPatterns (patterns: List Pattern) (towels: List Pattern): Prop := List.All (towel => towel ∈ patterns) towels

-- `towels`, laid end to end, make `design`.
def Makes (patterns: List Pattern) (towels: List Pattern) (design: Design): Prop :=
  And (FromPatterns patterns towels) (towels.concat = design)

-- The spec's lists are of the patterns and no longer than `count`.
theorem fromTowelLists (patterns: List Pattern): (count: Nat) → (towels: List Pattern) → towels ∈ towelLists patterns count →
    And (FromPatterns patterns towels) (towels.length ≤ count)
  | Zero, towels, Inl empty => rewrite <- empty in Both Trivial (omega)
  | Zero, towels, Inr none => Void.exfalso none
  | Succ count, towels, Inl empty => rewrite <- empty in Both Trivial (omega)
  | Succ count, towels, Inr later =>
    List.anyElim (first => towels ∈ (towelLists patterns count |> .map (Cons first))) (And (FromPatterns patterns towels) (towels.length ≤ Succ count))
      patterns (List.memFlatMapElim (first => towelLists patterns count |> .map (Cons first)) towels patterns later)
      (first firstMember mapped =>
        List.anyElim (rest => Cons first rest = towels) (And (FromPatterns patterns towels) (towels.length ≤ Succ count)) (towelLists patterns count)
          (List.memMapAny (towelLists patterns count) (Cons first) towels mapped)
          (rest restMember made =>
            let restFacts := fromTowelLists patterns count rest restMember
            rewrite <- made in Both (Both firstMember restFacts.left) (omega [restFacts.right])))

-- Every list of the patterns, no longer than `count`, is one of the spec's.
theorem inTowelLists (patterns: List Pattern): (count: Nat) → (towels: List Pattern) → FromPatterns patterns towels → towels.length ≤ count →
    towels ∈ towelLists patterns count
  | Zero, Nil, from, short => Inl rfl
  | Succ count, Nil, from, short => Inl rfl
  | Zero, Cons first rest, from, short => Void.exfalso (omega [short])
  | Succ count, Cons first rest, Both firstMember restFrom, short =>
    Inr (List.memFlatMapIntro (first => towelLists patterns count |> .map (Cons first)) first (Cons first rest) patterns firstMember
      (List.memMap (towelLists patterns count) rest (inTowelLists patterns count rest restFrom (omega [short])) (Cons first)))

-- With every pattern striped, there are no more towels than stripes.
theorem towelsAtMostStripes (patterns: List Pattern) (striped: Striped patterns): (towels: List Pattern) → FromPatterns patterns towels →
    towels.length ≤ towels.concat.length
  | Nil, from => omega
  | Cons first rest, Both firstMember restFrom =>
    omega [List.lengthAppend first rest.concat, striped first firstMember, towelsAtMostStripes patterns striped rest restFrom]

-- Whether a list of lists has any.
def hasSome (lists: List (List Pattern)): Bool := lists != []

theorem someMember: (lists: List (List Pattern)) → hasSome lists = True → Exists (List Pattern) (list => list ∈ lists)
  | Nil, some => Void.exfalso (Bool.falseNotTrue some)
  | Cons first rest, some => Witness first (Inl rfl)

theorem memberSome: (lists: List (List Pattern)) → (list: List Pattern) → list ∈ lists → hasSome lists = True
  | Nil, list, member => Void.exfalso member
  | Cons first rest, list, member => rfl

-- "Not all designs will be possible": a design is possible exactly when
-- some towels of the patterns make it.
theorem possibleIff (patterns: List Pattern) (striped: Striped patterns) (design: Design):
    Iff (possible patterns design = True) (Exists (List Pattern) (towels => Makes patterns towels design)) := {
  forward = found =>
    Exists.map
      (towels member =>
        let filtered := List.memFilter (towelLists patterns design.length) (towels => towels.concat == design) towels member
        Both (fromTowelLists patterns design.length towels filtered.left).left (DecEq.sound towels.concat design filtered.right))
      (someMember (arrangements patterns design) found),
  backward = made =>
    Exists.elim made (towels (Both from stripes) =>
      memberSome (arrangements patterns design) towels
        (List.memFilterIntro (towelLists patterns design.length) (towels => towels.concat == design) towels
          (inTowelLists patterns design.length towels from (rewrite <- stripes in towelsAtMostStripes patterns striped towels from))
          (rewrite stripes in DecEq.refl design)))
}
