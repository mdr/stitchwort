--| The holders `assign` finds, read as the spec's function from allergens
--| to ingredients: each allergen's holder is the ingredient at its place.

namespace Aoc.Year2020.Day21.Proofs
import Aoc.Year2020.Day21 (..)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| The ingredient at `allergen`'s place in `allergens`, if it has one.
def holderOf: (allergens: List Allergen) → (holders: List Ingredient) → (allergen: Allergen) → Ingredient
  | [first, ..rest], [holder, ..holders], allergen => if allergen == first then holder else holderOf rest holders allergen
  | _, _, allergen => { name = "" }

theorem holderOfLater (first: Allergen) (rest: List Allergen) (holder: Ingredient) (holders: List Ingredient) (allergen: Allergen) (other: allergen ≠ first):
    holderOf [first, ..rest] [holder, ..holders] allergen = holderOf rest holders allergen :=
  match same: allergen == first with
    | True => Void.exfalso (other (DecEq.sound same))
    | False => rfl

theorem inRest (allergen: Allergen) (first: Allergen) (rest: List Allergen) (member: allergen ∈ [first, ..rest]) (other: (allergen == first) = False): allergen ∈ rest :=
  match member with
    | Inl equal => Void.exfalso (DecEq.soundFalse allergen first other (Eq.sym equal))
    | Inr later => later

--| Each allergen's holder, in order, is the list of holders.
theorem mapHolderOf: (allergens: List Allergen) → (holders: List Ingredient) → allergens.length = holders.length → allergens.Distinct →
    allergens.map (holderOf allergens holders) = holders
  | [], [], lengths, distinct => rfl
  | [first, ..rest], [holder, ..holders], lengths, Both fresh distinct =>
    rewrite DecEq.refl first in
      rewrite List.mapCongMem rest (holderOf [first, ..rest] [holder, ..holders]) (holderOf rest holders)
          (allergen member => holderOfLater first rest holder holders allergen (same => fresh (rewrite <- same in member))),
        mapHolderOf rest holders (Nat.succInjective lengths) distinct in rfl
  | [], [holder, ..holders], lengths, distinct => Void.exfalso (Nat.zeroNotSucc _ lengths)
  | [first, ..rest], [], lengths, distinct => Void.exfalso (Nat.succNotZero _ lengths)

--| A listed allergen's holder is related to it as the holders are to the
--| allergens.
theorem holderOfRelated (related: Ingredient → Allergen → Prop): (allergens: List Allergen) → (holders: List Ingredient) →
    List.All2 related holders allergens → (allergen: Allergen) → allergen ∈ allergens → related (holderOf allergens holders allergen) allergen
  | [first, ..rest], [holder, ..holders], Both here later, allergen, member =>
    match same: allergen == first with
      | True => rewrite DecEq.sound same in here
      | False =>
        holderOfRelated related rest holders later allergen (inRest allergen first rest member same)
  | [], holders, related2, allergen, member => Void.exfalso member
  | [first, ..rest], [], related2, allergen, member => Void.exfalso related2

theorem holderOfMember: (allergens: List Allergen) → (holders: List Ingredient) → allergens.length = holders.length →
    (allergen: Allergen) → allergen ∈ allergens → holderOf allergens holders allergen ∈ holders
  | [], holders, lengths, allergen, member => Void.exfalso member
  | [first, ..rest], [], lengths, allergen, member => Void.exfalso (Nat.succNotZero _ lengths)
  | [first, ..rest], [holder, ..holders], lengths, allergen, member =>
    match here: allergen == first with
      | True => Inl rfl
      | False => Inr (holderOfMember rest holders (Nat.succInjective lengths) allergen (inRest allergen first rest member here))

theorem holderOfInjective: (allergens: List Allergen) → (holders: List Ingredient) → allergens.length = holders.length → holders.Distinct →
    (first: Allergen) → (second: Allergen) → first ∈ allergens → second ∈ allergens → holderOf allergens holders first = holderOf allergens holders second → first = second
  | [], holders, lengths, distinct, first, second, inFirst, inSecond, same => Void.exfalso inFirst
  | [head, ..rest], [], lengths, distinct, first, second, inFirst, inSecond, same => Void.exfalso (Nat.succNotZero _ lengths)
  | [head, ..rest], [holder, ..holders], lengths, Both fresh distinct, first, second, inFirst, inSecond, same =>
    match firstHere: first == head with
      | True =>
        match secondHere: second == head with
          | True => Eq.trans (DecEq.sound firstHere) (Eq.sym (DecEq.sound secondHere))
          | False =>
            Void.exfalso (fresh (rewrite same in holderOfMember rest holders (Nat.succInjective lengths) second (inRest second head rest inSecond secondHere)))
      | False =>
        match secondHere: second == head with
          | True =>
            Void.exfalso (fresh (rewrite <- same in holderOfMember rest holders (Nat.succInjective lengths) first (inRest first head rest inFirst firstHere)))
          | False =>
            holderOfInjective rest holders (Nat.succInjective lengths) distinct first second (inRest first head rest inFirst firstHere)
              (inRest second head rest inSecond secondHere) same
