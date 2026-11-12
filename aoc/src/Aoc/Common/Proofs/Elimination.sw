--| What `assign` finds: a candidate at each position and no value twice
--| (`assignFinds`), and, since a position is only settled with the one
--| candidate left once the values settled elsewhere are out, no other
--| assignment of candidates without a repeat exists (`assignOnly`).

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

--| A settled position's pick is one of its candidates.
def SlotSound (slot: Slot a): Prop := ∀ (item: a) => slot.choice = Some item → item ∈ slot.candidates

--| The slots stand for the positions with `candidates`, soundly settled.
def Keeps (slots: List (Slot a)) (candidates: List (List a)): Prop :=
  List.All2 (slot items => slot.candidates = items ∧ SlotSound slot) slots candidates

--| No pick is settled at two positions.
def ChosenOnce [auto eq: DecEq a] (slots: List (Slot a)): Prop := ∀ (item: a) => (chosen slots).count (pick => pick == item) ≤ 1

--| One round changes no position's candidates, and settles a position only
--| with one of them.
def SlotStep (after: Slot a) (before: Slot a): Prop := after.candidates = before.candidates ∧ (SlotSound before → SlotSound after)

theorem stepRefl (slot: Slot a): SlotStep slot slot := Both rfl (sound => sound)

theorem stepsRefl (slots: List (Slot a)): List.All2 SlotStep slots slots :=
  match slots with
    | [] => Trivial
    | [slot, ..slots] => Both (stepRefl slot) (stepsRefl slots)

theorem keepsStep (next: List (Slot a)) (slots: List (Slot a)) (candidates: List (List a)) (steps: List.All2 SlotStep next slots) (keeps: Keeps slots candidates):
    Keeps next candidates :=
  List.all2Compose (after before items step kept => Both (Eq.trans (And.left step) (And.left kept)) (And.right step (And.right kept))) next slots candidates steps keeps

theorem settledCons [auto eq: DecEq a] (slot: Slot a) (slots: List (Slot a)): chosen [slot, ..slots] = chosen [slot] ++ chosen slots :=
  match pick: slot.choice with
    | Some item => rfl
    | None => rfl

--| A position that `settle` passes over.
theorem passSteps [auto eq: DecEq a] (settled: List a) (slot: Slot a) (slots: List (Slot a)) (next: List (Slot a)) (found: (settle settled slots).map (Cons slot) = Some next)
    (rest: ∀ (after: List (Slot a)) => settle settled slots = Some after → List.All2 SlotStep after slots): List.All2 SlotStep next [slot, ..slots] :=
  match later: settle settled slots with
    | Some after => rewrite <- Option.someInjective found in Both (stepRefl slot) (rest after rfl)

theorem settleSteps [auto eq: DecEq a] (settled: List a) (slots next: List (Slot a)) (found: settle settled slots = Some next): List.All2 SlotStep next slots :=
  match slots with
    | [slot, ..slots] =>
      match pick: slot.choice with
        | Some existing => passSteps settled slot slots next found (settleSteps settled slots)
        | None =>
          match left: slot.remaining settled with
            | [] => passSteps settled slot slots next found (settleSteps settled slots)
            | [only] =>
              rewrite <- Option.someInjective found in
                Both (Both rfl (sound item same =>
                  rewrite <- Option.someInjective same in And.left (List.memFilter slot.candidates (item => not (settled.contains item)) (rewrite left in Inl rfl))))
                  (stepsRefl slots)
            | [first, second, ..more] => passSteps settled slot slots next found (settleSteps settled slots)

--| What one round adds to the settled items: one pick, not settled before.
def Adds [auto eq: DecEq a] (settled: List a) (next: List (Slot a)) (slots: List (Slot a)): Prop :=
  ∃ (item: a) => settled.contains item = False
    ∧ (∀ (other: a) => (chosen next).count (pick => pick == other) = (chosen slots).count (pick => pick == other) + Bool.toNat (item == other))

theorem passAdds [auto eq: DecEq a] (settled: List a) (slot: Slot a) (slots: List (Slot a)) (next: List (Slot a)) (found: (settle settled slots).map (Cons slot) = Some next)
    (rest: ∀ (after: List (Slot a)) => settle settled slots = Some after → Adds settled after slots): Adds settled next [slot, ..slots] :=
  match later: settle settled slots with
    | Some after =>
      match rest after rfl with
        | Witness item (Both fresh counts) =>
          Witness item (Both fresh (other =>
            rewrite <- Option.someInjective found, settledCons slot after, settledCons slot slots, List.countAppend, List.countAppend, counts other in omega))

theorem settleAdds [auto eq: DecEq a] (settled: List a) (slots next: List (Slot a)) (found: settle settled slots = Some next): Adds settled next slots :=
  match slots with
    | [slot, ..slots] =>
      match pick: slot.choice with
        | Some existing =>
          passAdds settled slot slots next found (settleAdds settled slots)
        | None =>
          match left: slot.remaining settled with
            | [] =>
              passAdds settled slot slots next found (settleAdds settled slots)
            | [only] =>
              let kept := And.right (List.memFilter slot.candidates (item => not (settled.contains item)) (rewrite left in Inl rfl))
              rewrite <- Option.someInjective found in
                Witness only (Both (Bool.notTrue _ kept) (other =>
                  Eq.trans (List.countCons (chosen slots) only (pick => pick == other)) (Nat.addComm _ _)))
            | [first, second, ..more] =>
              passAdds settled slot slots next found (settleAdds settled slots)

theorem settleOnce [auto eq: DecEq a] (slots: List (Slot a)) (next: List (Slot a)) (found: settle (chosen slots) slots = Some next) (once: ChosenOnce slots): ChosenOnce next :=
  match settleAdds (chosen slots) slots next found with
    | Witness item (Both fresh counts) =>
      other =>
        rewrite counts other in
          match same: item == other with
            | True =>
              let none := List.countZeroOfNotContains (chosen slots) item fresh
              rewrite <- DecEq.sound same in omega
            | False =>
              let before := once other
              omega

theorem allSettledFields (slots: List (Slot a)) (order: List a) (found: allSettled slots = Some order):
    List.All2 (item slot => slot.choice = Some item) order slots ∧ order = chosen slots :=
  match slots with
    | [] => rewrite <- Option.someInjective found in Both Trivial rfl
    | [slot, ..slots] =>
      match pick: slot.choice with
        | Some item =>
          match rest: allSettled slots with
            | Some tail =>
              match allSettledFields slots tail rest with
                | Both items same => rewrite <- Option.someInjective found in Both (Both pick items) (rewrite same in rfl)

theorem eliminateFinds [auto eq: DecEq a] (candidates: List (List a)): ∀ (rounds: Nat) (slots: List (Slot a)) => Keeps slots candidates → ChosenOnce slots →
    ∀ (order: List a) => eliminate rounds slots = Some order →
    List.All2 (item items => item ∈ items) order candidates ∧ (∀ (item: a) => order.count (pick => pick == item) ≤ 1)
  | rounds, slots, keeps, once, order, found =>
    match done: allSettled slots with
      | Some settled =>
        match allSettledFields slots settled done with
          | Both items same =>
            rewrite <- Option.someInjective found in
              Both (List.all2Compose (item slot items isField kept => rewrite <- And.left kept in And.right kept item isField) settled slots candidates items keeps)
                (item => rewrite same in once item)
      | None =>
        match rounds with
          | Succ more =>
            match step: settle (chosen slots) slots with
              | Some next =>
                eliminateFinds candidates more next (keepsStep next slots candidates (settleSteps _ slots next step) keeps) (settleOnce slots next step once) order found

--| `other` gives each position a pick among its candidates, and the
--| pick settled there, if any.
def Agrees [auto eq: DecEq a] (other: List a) (slots: List (Slot a)): Prop :=
  List.All2 (item slot => item ∈ slot.candidates ∧ (∀ (pick: a) => slot.choice = Some pick → item = pick)) other slots

--| A pick settled somewhere is `other`'s pick there.
theorem settledIn [auto eq: DecEq a] (pick: a) (other: List a) (slots: List (Slot a)) (agrees: Agrees other slots) (member: pick ∈ chosen slots): pick ∈ other :=
  match other, slots with
    | [item, ..other], [slot, ..slots] =>
      match List.memAppend pick (chosen [slot]) (chosen slots) (rewrite <- settledCons slot slots in member) with
        | Inl here =>
          match settledField: slot.choice with
            | Some settledHere =>
              let same: pick = settledHere := match here with
                | Inl same => Eq.sym same
                | Inr none => Void.exfalso none
              Inl (rewrite same in And.right (And.left agrees) settledHere rfl)
        | Inr later => Inr (settledIn pick other slots (And.right agrees) later)
    | [], [slot, ..slots] => Void.exfalso agrees

--| An order of distinct items gives a position not yet settled a pick
--| settled nowhere, and none of `outside`.
theorem freshOf [auto eq: DecEq a] (outside: List a) (other: List a) (slots: List (Slot a)) (h: Agrees other slots) (h1: other.Distinct)
    (apart: (∀ (pick: a) => pick ∈ outside → pick ∉ other)):
    List.All2 (item slot => slot.choice = None → item ∉ outside ++ chosen slots) other slots :=
  match other, slots, h, h1 with
    | [], [], agrees, distinct => Trivial
    | [item, ..other], [slot, ..slots], Both (Both candidate settledHere) agrees, Both fresh distinct =>
      let restApart: ∀ (pick: a) => pick ∈ outside ++ chosen [slot] → pick ∉ other := pick member =>
        match List.memAppend pick outside (chosen [slot]) member with
          | Inl outer => inOther => apart pick outer (Inr inOther)
          | Inr here =>
            match settledField: slot.choice with
              | Some settledThere =>
                let same: pick = settledThere := match here with
                  | Inl same => Eq.sym same
                  | Inr none => Void.exfalso none
                rewrite same, <- settledHere settledThere rfl in fresh
      Both
        (isOpen member =>
          match List.memAppend item outside (chosen [slot, ..slots]) member with
            | Inl outer => apart item outer (Inl rfl)
            | Inr settled =>
              match List.memAppend item (chosen [slot]) (chosen slots) (rewrite <- settledCons slot slots in settled) with
                | Inl here => rewrite isOpen at here in Void.exfalso here
                | Inr later => fresh (settledIn item other slots agrees later))
        (List.all2Weaken (laterRule laterSlot unsettled isOpen => rewrite settledCons slot slots, <- List.appendAssoc outside (chosen [slot]) (chosen slots) in unsettled isOpen) other slots
          (freshOf (outside ++ chosen [slot]) other slots agrees distinct restApart))
    | [], [slot, ..slots], agrees, distinct => Void.exfalso agrees
    | [item, ..other], [], agrees, distinct => Void.exfalso agrees

theorem passAgrees [auto eq: DecEq a] (settled: List a) (item: a) (other: List a) (slot: Slot a) (slots: List (Slot a)) (next: List (Slot a))
    (found: (settle settled slots).map (Cons slot) = Some next) (agrees: Agrees [item, ..other] [slot, ..slots])
    (rest: ∀ (after: List (Slot a)) => settle settled slots = Some after → Agrees other after): Agrees [item, ..other] next :=
  match later: settle settled slots with
    | Some after => rewrite <- Option.someInjective found in Both (And.left agrees) (rest after rfl)

--| A round keeps an order that agrees, when no position yet to be settled
--| has a settled pick in it.
theorem settleAgrees [auto eq: DecEq a] (settled: List a) (other: List a) (slots next: List (Slot a)) (found: settle settled slots = Some next)
    (agrees: Agrees other slots) (fresh: List.All2 (item slot => slot.choice = None → item ∉ settled) other slots): Agrees other next :=
  match other, slots with
    | [], [slot, ..slots] => Void.exfalso agrees
    | [item, ..other], [slot, ..slots] =>
      let rest := (after: List (Slot a)) (later: settle settled slots = Some after) => settleAgrees settled other slots after later (And.right agrees) (And.right fresh)
      let pass := (passed: (settle settled slots).map (Cons slot) = Some next) => passAgrees settled item other slot slots next passed agrees rest
      match pick: slot.choice with
        | Some existing =>
          pass found
        | None =>
          match left: slot.remaining settled with
            | [] =>
              pass found
            | [only] =>
              let notSettled: (settled.contains item) = False := match contained: settled.contains item with
                | True => Void.exfalso (And.left fresh rfl ((List.memContains settled item).forward contained))
                | False => rfl
              let remains: item ∈ slot.remaining settled :=
                List.memFilterIntro slot.candidates (pick => not (settled.contains pick)) (And.left (And.left agrees)) (rewrite notSettled in rfl)
              let forced: item = only := match (rewrite left at remains in remains) with
                | Inl same => Eq.sym same
                | Inr none => Void.exfalso none
              rewrite <- Option.someInjective found in
                Both (Both (And.left (And.left agrees)) (pick same => rewrite forced in Option.someInjective same)) (And.right agrees)
            | [first, second, ..more] =>
              pass found

theorem settledSame [auto eq: DecEq a] (other order: List a) (slots: List (Slot a)) (agrees: Agrees other slots)
    (items: List.All2 (item slot => slot.choice = Some item) order slots): other = order :=
  match other, order, slots with
    | [], [], [] => rfl
    | [item, ..other], [pick, ..order], [slot, ..slots] =>
      rewrite And.right (And.left agrees) pick (And.left items), settledSame other order slots (And.right agrees) (And.right items) in rfl
    | [], [pick, ..order], [] => Void.exfalso items
    | [item, ..other], [], [] => Void.exfalso agrees

theorem eliminateOnly [auto eq: DecEq a] (other: List a) (distinct: other.Distinct): ∀ (rounds: Nat) (slots: List (Slot a)) => Agrees other slots →
    ∀ (order: List a) => eliminate rounds slots = Some order → other = order
  | rounds, slots, agrees, order, found =>
    match done: allSettled slots with
      | Some settled =>
        rewrite <- Option.someInjective found in settledSame other settled slots agrees (And.left (allSettledFields slots settled done))
      | None =>
        match rounds with
          | Succ more =>
            match step: settle (chosen slots) slots with
              | Some next =>
                eliminateOnly other distinct more next
                  (settleAgrees (chosen slots) other slots next step agrees (freshOf [] other slots agrees distinct (pick none => Void.exfalso none)))
                  order found

theorem keepsOpen (candidates: List (List a)): Keeps (candidates.map Slot.open) candidates :=
  match candidates with
    | [] => Trivial
    | [items, ..candidates] => Both (Both rfl (item none => Void.exfalso (Option.noneNotSome item none))) (keepsOpen candidates)

theorem chosenOpen [auto eq: DecEq a] (candidates: List (List a)): chosen (candidates.map Slot.open) = [] :=
  match candidates with
    | [] => rfl
    | [items, ..candidates] => chosenOpen candidates

theorem onceOpen [auto eq: DecEq a] (candidates: List (List a)): ChosenOnce (candidates.map Slot.open) :=
  item => rewrite chosenOpen candidates in Nat.zeroLe 1

theorem agreesOpen [auto eq: DecEq a] (other: List a) (candidates: List (List a)) (members: List.All2 (item items => item ∈ items) other candidates):
    Agrees other (candidates.map Slot.open) :=
  match other, candidates with
    | [], [] => Trivial
    | [item, ..other], [items, ..candidates] =>
      Both (Both (And.left members) (pick none => Void.exfalso (Option.noneNotSome pick none))) (agreesOpen other candidates (And.right members))

--| If `assign` settles every position, it takes a candidate at each, and no
--| value at two positions.
theorem assignFinds [auto eq: DecEq a] (candidates: List (List a)) (picks: List a) (found: assign candidates = Some picks):
    List.All2 (item items => item ∈ items) picks candidates ∧ picks.Distinct :=
  match eliminateFinds candidates candidates.length (candidates.map Slot.open) (keepsOpen candidates) (onceOpen candidates) picks found with
    | Both members counts => Both members (List.distinctOfCounts picks counts)

--| If `assign` settles every position, every assignment of a candidate to
--| each position without a repeat is the one it found.
theorem assignOnly [auto eq: DecEq a] (candidates: List (List a)) (picks: List a) (found: assign candidates = Some picks) (other: List a)
    (members: List.All2 (item items => item ∈ items) other candidates) (distinct: other.Distinct): other = picks :=
  eliminateOnly other distinct candidates.length (candidates.map Slot.open) (agreesOpen other candidates members) picks found
