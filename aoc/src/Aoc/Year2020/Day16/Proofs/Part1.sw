--| Part 1: the error rate the program adds up is the spec's.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16 (Spec)
import Std (Bool, Eq, List)

theorem errorTerm ∀ (notes: Notes) (value: Nat):
    (if not (notes.fitsSomeField value) then value else 0)
      = (if Spec.validForSomeField notes.rules value then 0 else value) :=
  match fits: Spec.validForSomeField notes.rules value with
    | True => rfl
    | False => rfl

theorem errorRateSpec ∀ (notes: Notes): Spec.Part1 notes notes.errorRate := calc notes.errorRate
  _ = (notes.nearby.flatMap .values).sumBy (value => if not (notes.fitsSomeField value) then value else 0) :=
    rewrite List.sumIsSumBy, List.sumByFilter in rfl
  _ = notes.nearby.sumBy (ticket =>
      ticket.values.sumBy (value => if not (notes.fitsSomeField value) then value else 0)) := List.sumByFlatMap _ _ _
  _ = Spec.errorRate notes :=
    List.sumByCong notes.nearby _ _ (ticket => List.sumByCong ticket.values _ _ (errorTerm notes))
