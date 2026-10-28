-- The spec's "some combination of operators" as a search forwards, one
-- operator at a time, and the facts about it the proofs need.

namespace Aoc.Year2024.Day07.Proofs
import Aoc.Year2024.Day07 (..)
import Aoc.Year2024.Day07.Spec (..)
import Std (Bool, Eq, List, Nat)

-- Whether some choice of the operators between `start` and the numbers
-- gives a value that is `wanted`.
def reaches (operators: List Operator) (start: Nat) (wanted: Nat → Bool): List Nat → Bool
  | Nil => wanted start
  | Cons number rest => operators.any (operator => reaches operators (combine operator start number) wanted rest)

-- The spec's "any combination" is the forwards search.
theorem combinationsReach (operators: List Operator) (wanted: Nat → Bool): (numbers: List Nat) → (start: Nat) →
    (combinations operators numbers.length).any (chosen => wanted (evaluate start (chosen.zip numbers))) = reaches operators start wanted numbers
  | Nil, start => cases
  | Cons number rest, start =>
    Eq.trans (List.anyFlatMap (operator => combinations operators rest.length |> .map (Cons operator))
        (chosen => wanted (evaluate start (chosen.zip (Cons number rest)))) operators)
      (List.anyCong operators _ _ (operator =>
        Eq.trans (List.anyMap (combinations operators rest.length) (chosen => wanted (evaluate start (chosen.zip (Cons number rest)))) (Cons operator))
          (combinationsReach operators wanted rest (combine operator start number))))

-- The search depends only on which values are wanted.
theorem reachesCong (operators: List Operator) (wanted1: Nat → Bool) (wanted2: Nat → Bool) (same: (value: Nat) → wanted1 value = wanted2 value):
    (numbers: List Nat) → (start: Nat) → reaches operators start wanted1 numbers = reaches operators start wanted2 numbers
  | Nil, start => same start
  | Cons number rest, start =>
    List.anyCong operators _ _ (operator => reachesCong operators wanted1 wanted2 same rest (combine operator start number))

-- Nothing wanted is never reached.
theorem reachesNothing (operators: List Operator): (numbers: List Nat) → (start: Nat) → reaches operators start (value => False) numbers = False
  | Nil, start => rfl
  | Cons number rest, start => List.anyFalse operators _ (operator => reachesNothing operators rest (combine operator start number))

-- Anything is reached, when there is an operator to choose.
theorem reachesAnything (operators: List Operator) (some: Operator) (has: some ∈ operators):
    (numbers: List Nat) → (start: Nat) → reaches operators start (value => True) numbers = True
  | Nil, start => rfl
  | Cons number rest, start =>
    List.anyOfMem operators _ some (reachesAnything operators some has rest (combine some start number)) has

-- A condition that doesn't depend on the value comes out of the search.
theorem reachesAnd (operators: List Operator) (condition: Bool) (wanted: Nat → Bool) (numbers: List Nat) (start: Nat):
    reaches operators start (value => condition && wanted value) numbers = (condition && reaches operators start wanted numbers) :=
  match condition with
    | True => rfl
    | False => reachesNothing operators numbers start

-- A choice among `others` at the end comes out of the search.
theorem reachesAny (operators: List Operator) (others: List Operator) (wanted: Operator → Nat → Bool):
    (numbers: List Nat) → (start: Nat) →
    reaches operators start (value => others.any (other => wanted other value)) numbers = others.any (other => reaches operators start (wanted other) numbers)
  | Nil, start => rfl
  | Cons number rest, start =>
    Eq.trans (List.anyCong operators _ _ (operator => reachesAny operators others wanted rest (combine operator start number)))
      (List.anyComm (operator other => reaches operators (combine operator start number) (wanted other) rest) others operators)

-- The last number is the last operator's right side.
theorem reachesAppend (operators: List Operator) (wanted: Nat → Bool) (last: Nat): (numbers: List Nat) → (start: Nat) →
    reaches operators start wanted (numbers.append [last])
      = reaches operators start (value => operators.any (operator => wanted (combine operator value last))) numbers
  | Nil, start => rfl
  | Cons number rest, start =>
    List.anyCong operators _ _ (operator => reachesAppend operators wanted last rest (combine operator start number))
