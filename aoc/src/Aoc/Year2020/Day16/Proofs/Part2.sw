--| Part 2: the order the elimination finds is an order of the fields the
--| puzzle allows, and the answer is its departure product.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

def openSlot (candidates: List Rule): Slot := { candidates, field = None }

theorem keepsOpen: (candidates: List (List Rule)) → Keeps (candidates.map openSlot) candidates
  | [] => Trivial
  | [fields, ..candidates] => Both (Both rfl (rule none => Void.exfalso (Option.noneNotSome rule none))) (keepsOpen candidates)

theorem openSettled: (candidates: List (List Rule)) → settledFields (candidates.map openSlot) = []
  | [] => rfl
  | [fields, ..candidates] => openSettled candidates

theorem onceOpen (candidates: List (List Rule)): Once (candidates.map openSlot) :=
  rule => rewrite openSettled candidates in Nat.zeroLe 1

theorem validTicketValid (notes: Notes) (ticket: Ticket) (nearby: ticket ∈ notes.nearby) (valid: Spec.ValidTicket notes.rules ticket):
    ticket ∈ notes.validTickets :=
  List.memFilterIntro notes.nearby notes.isValid nearby valid

--| If the elimination settles every position, its order is one the puzzle
--| allows.
theorem fieldOrderValid (notes: Notes) (order: List Rule) (found: notes.fieldOrder = Some order): Spec.FieldOrder notes order :=
  match lengths: notes.validTickets.all (ticket => ticket.values.length == notes.rules.length) with
    | True =>
      match candidatesFit notes lengths with
        | Both wide (Both within allow) =>
          match eliminateFinds notes.candidates notes.rules.length (notes.candidates.map openSlot) (keepsOpen notes.candidates) (onceOpen notes.candidates) order found with
            | Both members counts =>
              let fromRules := List.all2Compose (rule fields wider member inner => inner rule member) order notes.candidates _ members within
              Both (Eq.trans (List.all2Length _ order notes.candidates members) wide)
                (Both (List.distinctOfCounts order counts)
                  (Both (rule member => List.all2Replicate notes.rules order notes.rules.length fromRules rule member)
                    (ticket nearby valid =>
                      List.all2Compose (rule fields value member allows => allows rule member) order notes.candidates ticket.values members
                        (allow ticket (validTicketValid notes ticket nearby valid)))))
    | False => Void.exfalso (Option.noneNotSome order found)

theorem departureProductSpec: (order: List Rule) → (values: List Nat) → ({ values }: Ticket).departureProduct order = Spec.departureProduct order values
  | [rule, ..order], [value, ..values] =>
    match departure: rule.field.startsWith "departure" with
      | True => rewrite List.productCons value _ in Eq.cong (rest => value * rest) (departureProductSpec order values)
      | False => rewrite Nat.oneMul (Spec.departureProduct order values) in departureProductSpec order values
  | [], values => rfl
  | [rule, ..order], [] => rfl

--| Part 2: if the program gives an answer, it is the departure product
--| under an order of the fields the puzzle allows.
theorem departureProductValid (notes: Notes) (answer: Nat) (found: notes.departureProduct = Some answer): Spec.Part2 notes answer :=
  match ordered: notes.fieldOrder with
    | Some order => Witness order (Both (fieldOrderValid notes order ordered) (rewrite <- Option.someInjective found in departureProductSpec order notes.yours.values))
    | None => Void.exfalso (Option.noneNotSome answer found)
