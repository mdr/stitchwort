--| Part 1: given some way the allergens could be (the puzzle promises
--| one), an ingredient is safe exactly when it is in no candidate list,
--| that is, when for every allergen some food lists it without the
--| ingredient. One way: a holder is in every food listing its allergen.
--| The other: an ingredient in every food listing `allergen`, held by no
--| allergen in a way the allergens could be, could take `allergen` over in
--| that way.

namespace Aoc.Year2020.Day21.Proofs
import Aoc.Year2020.Day21 (..)
import Aoc.Year2020.Day21 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)

--| `holder` with `allergen` moved to `ingredient`.
def moveTo (holder: Allergen → Ingredient) (allergen: Allergen) (ingredient: Ingredient) (other: Allergen): Ingredient :=
  if other == allergen then ingredient else holder other

--| Moving an allergen to an ingredient that holds no allergen, and is in
--| every food listing it, is another way the allergens could be.
theorem moveHolding ∀ (list: FoodList) (holder: Allergen → Ingredient) (holding: Spec.Holding list holder) (allergen: Allergen) (ingredient: Ingredient)
    (every: InEvery list ingredient allergen) (unheld: ∀ (other: Allergen) => Spec.Listed list other → holder other ≠ ingredient):
    Spec.Holding list (moveTo holder allergen ingredient) :=
  Both
    (first second firstListed secondListed same =>
      match firstMoved: first == allergen with
        | True =>
          match secondMoved: second == allergen with
            | True => Eq.trans firstMoved.read (Eq.sym secondMoved.read)
            | False => Void.exfalso (unheld second secondListed (Eq.sym same))
        | False =>
          match secondMoved: second == allergen with
            | True => Void.exfalso (unheld first firstListed same)
            | False => And.left holding first second firstListed secondListed same)
    (food inFoods other listed =>
      match moved: other == allergen with
        | True => every food inFoods (rewrite <- moved.read in listed)
        | False => And.right holding food inFoods other listed)

theorem safeIff ∀ (list: FoodList) (promise: ∃ (holder: Allergen → Ingredient) => Spec.Holding list holder) (ingredient: Ingredient):
    list.isSafe ingredient = True ↔ ¬Spec.CanContain list ingredient :=
  {
    forward = safe can =>
      match can with
        | Witness holder (Both holding (Witness allergen (Both listed held))) =>
          let could: list.couldHold ingredient allergen = True :=
            (couldHoldIff list ingredient allergen).backward (food inFoods inFood => rewrite <- held in And.right holding food inFoods allergen inFood)
          let some: list.allergens.any (other => list.couldHold ingredient other) = True :=
            Witness allergen (Both ((memAllergens list allergen).backward listed) could)
          Bool.trueNotFalse (Eq.trans (Eq.sym some) safe.read),
    backward = cannot =>
      match some: list.allergens.any (allergen => list.couldHold ingredient allergen) with
        | False => rfl
        | True =>
          let Witness allergen (Both member could) := some
          match promise with
            | Witness holder holding =>
              let listed := (memAllergens list allergen).forward member
              match taken: list.allergens.any (other => holder other == ingredient) with
                | True =>
                  let Witness other (Both inAllergens holds) := taken
                  let holds: (holder other == ingredient) = True := holds
                  Void.exfalso (cannot (Witness holder (Both holding (Witness other (Both ((memAllergens list other).forward inAllergens) holds.read)))))
                | False =>
                  let unheld: ∀ (other: Allergen) => Spec.Listed list other → holder other ≠ ingredient :=
                    other otherListed =>
                      let missed: (holder other == ingredient) = False := taken.read other ((memAllergens list other).backward otherListed)
                      missed.read
                  let moved := moveHolding list holder holding allergen ingredient ((couldHoldIff list ingredient allergen).forward could) unheld
                  Void.exfalso (cannot (Witness (moveTo holder allergen ingredient) (Both moved (Witness allergen (Both listed (rewrite DecEq.refl allergen in rfl))))))
  }

--| Part 1: given a way the allergens could be, the answer is the spec's.
theorem safeAppearancesSpec ∀ (list: FoodList) (promise: ∃ (holder: Allergen → Ingredient) => Spec.Holding list holder): Spec.Part1 list list.safeAppearances :=
  (List.countWithIff list.isSafe (safeIff list promise) (list.foods.flatMap .ingredients) list.safeAppearances).backward
    (Eq.sym (List.countFlatMap .ingredients list.isSafe list.foods))
