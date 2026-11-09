--| Part 2: when the elimination settles every allergen, its holders are a
--| way the allergens could be (`Aoc.Common.assignFinds`), and any other
--| way gives the same holders (`Aoc.Common.assignOnly`), so the canonical
--| list is the spec's, and the only one.

namespace Aoc.Year2020.Day21.Proofs
import Aoc.Year2020.Day21 (..)
import Aoc.Year2020.Day21 (Spec)
import Aoc.Common.Proofs (assignFinds, assignOnly)
import Std (Bool, DecEq, Eq, List, Nat, Option, Ord, Ordering, Text, Void)

theorem distinctMapOn (f: a → b): (xs: List a) → xs.Distinct → ((x: a) → (y: a) → x ∈ xs → y ∈ xs → f x = f y → x = y) → (xs.map f).Distinct
  | [], distinct, injective => Trivial
  | [x, ..xs], Both fresh distinct, injective =>
    Both
      (member =>
        match List.memMapElim f (f x) xs member with
          | Witness y (Both inRest same) => fresh (rewrite injective x y (Inl rfl) (Inr inRest) (Eq.sym same) in inRest))
      (distinctMapOn f xs distinct (first second inFirst inSecond same => injective first second (Inr inFirst) (Inr inSecond) same))

theorem all2MapBoth (related: b → c → Prop) (f: a → b) (g: a → c): (xs: List a) → ((x: a) → x ∈ xs → related (f x) (g x)) →
    List.All2 related (xs.map f) (xs.map g)
  | [], pointwise => Trivial
  | [x, ..xs], pointwise => Both (pointwise x (Inl rfl)) (all2MapBoth related f g xs (y member => pointwise y (Inr member)))

theorem all2OfMapRight (g: b → c) (related: a → c → Prop): (xs: List a) → (ys: List b) → List.All2 related xs (ys.map g) → List.All2 (x y => related x (g y)) xs ys
  | [], [], all => Trivial
  | [x, ..xs], [y, ..ys], all => Both (And.left all) (all2OfMapRight g related xs ys (And.right all))
  | [], [y, ..ys], all => Void.exfalso all
  | [x, ..xs], [], all => Void.exfalso all

theorem holdersFound (list: FoodList) (holders: List Ingredient) (found: list.holders = Some holders):
    List.All2 (holder allergen => holder ∈ list.candidates allergen) holders list.allergens ∧ holders.Distinct ∧ list.allergens.length = holders.length :=
  match assignFinds (list.allergens.map list.candidates) holders found with
    | Both members distinct =>
      Both (all2OfMapRight list.candidates (item items => item ∈ items) holders list.allergens members)
        (Both distinct
          (Eq.trans (Eq.sym (List.lengthMap list.allergens list.candidates))
            (Eq.sym (List.all2Length _ holders (list.allergens.map list.candidates) members))))

--| The holders the elimination finds are a way the allergens could be.
theorem holdersHolding (list: FoodList) (holders: List Ingredient) (found: list.holders = Some holders):
    Spec.Holding list (holderOf list.allergens holders) :=
  match holdersFound list holders found with
    | Both members (Both distinct lengths) =>
      Both
        (first second firstListed secondListed same =>
          holderOfInjective list.allergens holders lengths distinct first second
            ((memAllergens list first).backward firstListed) ((memAllergens list second).backward secondListed) same)
        (food inFoods allergen listed =>
          let candidate := holderOfRelated (holder allergen => holder ∈ list.candidates allergen) list.allergens holders members allergen
            ((memAllergens list allergen).backward (Witness food (Both inFoods listed)))
          let could := And.right (List.memFilter list.ingredients (ingredient => list.couldHold ingredient allergen) candidate)
          (couldHoldIff list _ allergen).forward could food inFoods listed)

--| Part 2: if the program gives an answer, it is the spec's canonical
--| dangerous ingredient list.
theorem dangerousValid (list: FoodList) (answer: Text) (found: list.dangerousList = Some answer): Spec.Part2 list answer :=
  match settled: list.holders with
    | Some holders =>
      match holdersFound list holders settled with
        | Both members (Both distinct lengths) =>
          Witness (holderOf list.allergens holders)
            (Both (holdersHolding list holders settled)
              (Witness list.allergens
                (Both (distinctAllergens list)
                  (Both (memAllergens list)
                    (Both (alphabeticalAllergens list)
                      (rewrite mapHolderOf list.allergens holders lengths (distinctAllergens list) in Eq.sym (Option.someInjective found)))))))
    | None => Void.exfalso (Option.noneNotSome answer found)

--| In any way the allergens could be, a listed allergen's holder is one of
--| the program's candidates for it.
theorem holderCandidate (list: FoodList) (holder: Allergen → Ingredient) (holding: Spec.Holding list holder) (allergen: Allergen) (listed: Spec.Listed list allergen):
    holder allergen ∈ list.candidates allergen :=
  match listed with
    | Witness food (Both inFoods inFood) =>
      List.memFilterIntro list.ingredients (ingredient => list.couldHold ingredient allergen)
        ((memIngredients list (holder allergen)).backward (Witness food (Both inFoods (And.right holding food inFoods allergen inFood))))
        ((couldHoldIff list (holder allergen) allergen).backward (other inOther listedThere => And.right holding other inOther allergen listedThere))

--| Two lists of allergens, each with no repeats and alphabetical, with
--| the same members, are the same list.
theorem sameAlphabetical (order: List Allergen) (other: List Allergen) (orderDistinct: order.Distinct) (otherDistinct: other.Distinct)
    (orderAlphabetical: Spec.Alphabetical order) (otherAlphabetical: Spec.Alphabetical other)
    (members: (allergen: Allergen) → allergen ∈ order ↔ allergen ∈ other): order = other :=
  List.sortedPermEq (first second => Ordering.isLessEq (Text.compare first.name second.name))
    (first second third => Ord.isLessEqTrans first.name second.name third.name)
    (first second before after => Allergen.ext first second (Ord.isLessEqAntisymm first.name second.name before after))
    order other orderAlphabetical otherAlphabetical
    (List.permOfSameMembers order other orderDistinct otherDistinct (allergen => (members allergen).forward) (allergen => (members allergen).backward))

--| Part 2's answer, when there is one, is the only canonical list: every
--| way the allergens could be gives the same one.
theorem dangerousOnly (list: FoodList) (answer: Text) (found: list.dangerousList = Some answer) (other: Text) (fits: Spec.Part2 list other):
    other = answer :=
  match fits with
    | Witness holder (Both holding (Witness order (Both distinct (Both members (Both alphabetical same))))) =>
      let sameOrder: order = list.allergens :=
        sameAlphabetical order list.allergens distinct (distinctAllergens list) alphabetical (alphabeticalAllergens list)
          (allergen => { forward = member => (memAllergens list allergen).backward ((members allergen).forward member), backward = member => (members allergen).backward ((memAllergens list allergen).forward member) })
      match settled: list.holders with
        | Some holders =>
          let sameHolders: list.allergens.map holder = holders :=
            assignOnly (list.allergens.map list.candidates) holders settled (list.allergens.map holder)
              (all2MapBoth (item items => item ∈ items) holder list.candidates list.allergens
                (allergen member => holderCandidate list holder holding allergen ((memAllergens list allergen).forward member)))
              (distinctMapOn holder list.allergens (distinctAllergens list)
                (first second inFirst inSecond => And.left holding first second ((memAllergens list first).forward inFirst) ((memAllergens list second).forward inSecond)))
          rewrite same, sameOrder, sameHolders in Option.someInjective found
        | None => Void.exfalso (Option.noneNotSome answer found)
