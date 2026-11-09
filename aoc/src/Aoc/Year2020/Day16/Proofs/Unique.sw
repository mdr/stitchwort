--| No other order of the fields fits: each position's field in any order
--| the puzzle allows is among its candidates, so if the elimination settles
--| every position (`Aoc.Common.assignOnly`), the order it finds is the only
--| one.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16 (Spec)
import Aoc.Common.Proofs (assignOnly)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

theorem narrowAgrees: ∀ (other: List Rule) (candidates: List (List Rule)) (values: List Nat) =>
    List.All2 (rule fields => rule ∈ fields) other candidates → List.All2 (rule value => rule.allows value = True) other values →
    List.All2 (rule fields => rule ∈ fields) other (List.zipWith candidates values allowing)
  | [], [], [], members, allows => Trivial
  | [rule, ..other], [fields, ..candidates], [value, ..values], members, allows =>
    Both (List.memFilterIntro fields (field => field.allows value) (And.left members) (And.left allows))
      (narrowAgrees other candidates values (And.right members) (And.right allows))
  | [], [], [value, ..values], members, allows => Void.exfalso allows
  | [], [fields, ..candidates], values, members, allows => Void.exfalso members
  | [rule, ..other], [], values, members, allows => Void.exfalso members
  | [rule, ..other], [fields, ..candidates], [], members, allows => Void.exfalso allows

theorem foldAgrees (other: List Rule): ∀ (tickets: List Ticket) (candidates: List (List Rule)) =>
    List.All2 (rule fields => rule ∈ fields) other candidates →
    (∀ (ticket: Ticket) => ticket ∈ tickets → List.All2 (rule value => rule.allows value = True) other ticket.values) →
    List.All2 (rule fields => rule ∈ fields) other (tickets.foldLeft candidates narrow)
  | [], candidates, members, allows => members
  | [ticket, ..tickets], candidates, members, allows =>
    foldAgrees other tickets (narrow candidates ticket) (narrowAgrees other candidates ticket.values members (allows ticket (Inl rfl)))
      (later member => allows later (Inr member))

theorem replicateAgrees (rules: List Rule): ∀ (other: List Rule) (count: Nat) => other.length = count → (∀ (rule: Rule) => rule ∈ other → rule ∈ rules) →
    List.All2 (rule fields => rule ∈ fields) other (List.replicate count rules)
  | [], Zero, same, members => Trivial
  | [], Succ count, same, members => Void.exfalso (Nat.zeroNotSucc _ same)
  | [rule, ..other], Zero, same, members => Void.exfalso (Nat.succNotZero _ same)
  | [rule, ..other], Succ count, same, members =>
    Both (members rule (Inl rfl)) (replicateAgrees rules other count (Nat.succInjective same) (later member => members later (Inr member)))

--| If the elimination settles every position, every order the puzzle
--| allows is the one it found.
theorem fieldOrderOnly (notes: Notes) (order: List Rule) (found: notes.fieldOrder = Some order) (other: List Rule) (fits: Spec.FieldOrder notes other):
    other = order :=
  match lengths: notes.validTickets.all (ticket => ticket.values.length == notes.rules.length) with
    | True =>
      match fits with
        | Both length (Both distinct (Both members tickets)) =>
          let inCandidates :=
            foldAgrees other notes.validTickets (List.replicate notes.rules.length notes.rules) (replicateAgrees notes.rules other notes.rules.length length members)
              (ticket member =>
                let kept := List.memFilter notes.nearby notes.isValid member
                tickets ticket (And.left kept) (And.right kept))
          assignOnly notes.candidates order found other inCandidates distinct
    | False => Void.exfalso (Option.noneNotSome order found)
