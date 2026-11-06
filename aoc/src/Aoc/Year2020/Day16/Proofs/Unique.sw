--| No other order of the fields fits: each position's field in any order
--| the puzzle allows is among its candidates, and every field the
--| elimination settles is forced, so if the elimination settles every
--| position, the order it finds is the only one.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Aoc.Year2020.Day16 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

--| `other` gives each position a field among its candidates, and the
--| field settled there, if any.
def Agrees (other: List Rule) (slots: List Slot): Prop :=
  List.All2 (rule slot => rule ∈ slot.candidates ∧ ((field: Rule) → slot.field = Some field → rule = field)) other slots

--| A field settled somewhere is `other`'s field there.
theorem settledIn (field: Rule): (other: List Rule) → (slots: List Slot) → Agrees other slots → field ∈ settledFields slots → field ∈ other
  | [], [], agrees, member => Void.exfalso member
  | [rule, ..other], [slot, ..slots], agrees, member =>
    match List.memAppend field (settledFields [slot]) (settledFields slots) (rewrite <- settledCons slot slots in member) with
      | Inl here =>
        match settledField: slot.field with
          | Some settledHere =>
            let same: field = settledHere := match here with
              | Inl same => Eq.sym same
              | Inr none => Void.exfalso none
            Inl (rewrite same in And.right (And.left agrees) settledHere rfl)
          | None => Void.exfalso here
      | Inr later => Inr (settledIn field other slots (And.right agrees) later)
  | [], [slot, ..slots], agrees, member => Void.exfalso agrees
  | [rule, ..other], [], agrees, member => Void.exfalso agrees

--| An order of distinct fields gives a position not yet settled a field
--| settled nowhere, and none of `outside`.
theorem freshOf (outside: List Rule): (other: List Rule) → (slots: List Slot) → Agrees other slots → other.Distinct →
    ((field: Rule) → field ∈ outside → field ∉ other) →
    List.All2 (rule slot => slot.field = None → rule ∉ outside ++ settledFields slots) other slots
  | [], [], agrees, distinct, apart => Trivial
  | [rule, ..other], [slot, ..slots], Both (Both candidate settledHere) agrees, Both fresh distinct, apart =>
    let restApart: (field: Rule) → field ∈ outside ++ settledFields [slot] → field ∉ other := field member =>
      match List.memAppend field outside (settledFields [slot]) member with
        | Inl outer => inOther => apart field outer (Inr inOther)
        | Inr here =>
          match settledField: slot.field with
            | Some settledThere =>
              let same: field = settledThere := match here with
                | Inl same => Eq.sym same
                | Inr none => Void.exfalso none
              rewrite same, <- settledHere settledThere rfl in fresh
            | None => Void.exfalso here
    Both
      (isOpen member =>
        match List.memAppend rule outside (settledFields [slot, ..slots]) member with
          | Inl outer => apart rule outer (Inl rfl)
          | Inr settled =>
            match List.memAppend rule (settledFields [slot]) (settledFields slots) (rewrite <- settledCons slot slots in settled) with
              | Inl here => rewrite isOpen at here in Void.exfalso here
              | Inr later => fresh (settledIn rule other slots agrees later))
      (List.all2Weaken (laterRule laterSlot unsettled isOpen => rewrite settledCons slot slots, <- List.appendAssoc outside (settledFields [slot]) (settledFields slots) in unsettled isOpen) other slots
        (freshOf (outside ++ settledFields [slot]) other slots agrees distinct restApart))
  | [], [slot, ..slots], agrees, distinct, apart => Void.exfalso agrees
  | [rule, ..other], [], agrees, distinct, apart => Void.exfalso agrees

theorem passAgrees (settled: List Rule) (rule: Rule) (other: List Rule) (slot: Slot) (slots: List Slot) (next: List Slot)
    (found: (settle settled slots).map (Cons slot) = Some next) (agrees: Agrees [rule, ..other] [slot, ..slots])
    (rest: (after: List Slot) → settle settled slots = Some after → Agrees other after): Agrees [rule, ..other] next :=
  match later: settle settled slots with
    | Some after => rewrite <- Option.someInjective found in Both (And.left agrees) (rest after rfl)
    | None => Void.exfalso (Option.noneNotSome next found)

--| A round keeps an order that agrees, when no position yet to be settled
--| has a settled field in it.
theorem settleAgrees (settled: List Rule): (other: List Rule) → (slots: List Slot) → (next: List Slot) → settle settled slots = Some next →
    Agrees other slots → List.All2 (rule slot => slot.field = None → rule ∉ settled) other slots → Agrees other next
  | other, [], next, found, agrees, fresh => Void.exfalso (Option.noneNotSome next found)
  | [], [slot, ..slots], next, found, agrees, fresh => Void.exfalso agrees
  | [rule, ..other], [slot, ..slots], next, found, agrees, fresh =>
    let rest := (after: List Slot) (later: settle settled slots = Some after) => settleAgrees settled other slots after later (And.right agrees) (And.right fresh)
    let pass := (passed: (settle settled slots).map (Cons slot) = Some next) => passAgrees settled rule other slot slots next passed agrees rest
    match field: slot.field with
      | Some existing =>
        pass found
      | None =>
        match left: slot.remaining settled with
          | [] =>
            pass found
          | [only] =>
            let notSettled: (settled.contains rule) = False := match contained: settled.contains rule with
              | True => Void.exfalso (And.left fresh rfl ((List.memContains settled rule).forward contained))
              | False => rfl
            let remains: rule ∈ slot.remaining settled :=
              List.memFilterIntro slot.candidates (field => not (settled.contains field)) (And.left (And.left agrees)) (rewrite notSettled in rfl)
            let forced: rule = only := match (rewrite left at remains in remains) with
              | Inl same => Eq.sym same
              | Inr none => Void.exfalso none
            rewrite <- Option.someInjective found in
              Both (Both (And.left (And.left agrees)) (field same => rewrite forced in Option.someInjective same)) (And.right agrees)
          | [first, second, ..more] =>
            pass found

theorem settledSame: (other: List Rule) → (order: List Rule) → (slots: List Slot) → Agrees other slots →
    List.All2 (rule slot => slot.field = Some rule) order slots → other = order
  | [], [], [], agrees, fields => rfl
  | [rule, ..other], [field, ..order], [slot, ..slots], agrees, fields =>
    rewrite And.right (And.left agrees) field (And.left fields), settledSame other order slots (And.right agrees) (And.right fields) in rfl
  | [], [], [slot, ..slots], agrees, fields => Void.exfalso agrees
  | [], [field, ..order], [], agrees, fields => Void.exfalso fields
  | [], [field, ..order], [slot, ..slots], agrees, fields => Void.exfalso agrees
  | [rule, ..other], [], [], agrees, fields => Void.exfalso agrees
  | [rule, ..other], [], [slot, ..slots], agrees, fields => Void.exfalso fields
  | [rule, ..other], [field, ..order], [], agrees, fields => Void.exfalso agrees

theorem eliminateOnly (other: List Rule) (distinct: other.Distinct): (rounds: Nat) → (slots: List Slot) → Agrees other slots →
    (order: List Rule) → eliminate rounds slots = Some order → other = order
  | rounds, slots, agrees, order, found =>
    match done: allSettled slots with
      | Some settled =>
        rewrite <- Option.someInjective found in settledSame other settled slots agrees (And.left (allSettledFields slots settled done))
      | None =>
        match rounds with
          | Zero => Void.exfalso (Option.noneNotSome order found)
          | Succ more =>
            match step: settle (settledFields slots) slots with
              | Some next =>
                eliminateOnly other distinct more next
                  (settleAgrees (settledFields slots) other slots next step agrees (freshOf [] other slots agrees distinct (field none => Void.exfalso none)))
                  order found
              | None => Void.exfalso (Option.noneNotSome order found)

theorem narrowAgrees: (other: List Rule) → (candidates: List (List Rule)) → (values: List Nat) →
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

theorem foldAgrees (other: List Rule): (tickets: List Ticket) → (candidates: List (List Rule)) →
    List.All2 (rule fields => rule ∈ fields) other candidates →
    ((ticket: Ticket) → ticket ∈ tickets → List.All2 (rule value => rule.allows value = True) other ticket.values) →
    List.All2 (rule fields => rule ∈ fields) other (tickets.foldLeft candidates narrow)
  | [], candidates, members, allows => members
  | [ticket, ..tickets], candidates, members, allows =>
    foldAgrees other tickets (narrow candidates ticket) (narrowAgrees other candidates ticket.values members (allows ticket (Inl rfl)))
      (later member => allows later (Inr member))

theorem replicateAgrees (rules: List Rule): (other: List Rule) → (count: Nat) → other.length = count → ((rule: Rule) → rule ∈ other → rule ∈ rules) →
    List.All2 (rule fields => rule ∈ fields) other (List.replicate count rules)
  | [], Zero, same, members => Trivial
  | [], Succ count, same, members => Void.exfalso (Nat.zeroNotSucc _ same)
  | [rule, ..other], Zero, same, members => Void.exfalso (Nat.succNotZero _ same)
  | [rule, ..other], Succ count, same, members =>
    Both (members rule (Inl rfl)) (replicateAgrees rules other count (Nat.succInjective _ _ same) (later member => members later (Inr member)))

theorem agreesOpen: (other: List Rule) → (candidates: List (List Rule)) → List.All2 (rule fields => rule ∈ fields) other candidates →
    Agrees other (candidates.map openSlot)
  | [], [], members => Trivial
  | [rule, ..other], [fields, ..candidates], members =>
    Both (Both (And.left members) (field none => Void.exfalso (Option.noneNotSome field none))) (agreesOpen other candidates (And.right members))
  | [], [fields, ..candidates], members => Void.exfalso members
  | [rule, ..other], [], members => Void.exfalso members

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
          eliminateOnly other distinct notes.rules.length (notes.candidates.map openSlot) (agreesOpen other notes.candidates inCandidates) order found
    | False => Void.exfalso (Option.noneNotSome order found)
