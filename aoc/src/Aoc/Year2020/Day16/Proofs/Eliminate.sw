--| What the elimination finds: at each position a field from its
--| candidates, and no field at two positions.

namespace Aoc.Year2020.Day16.Proofs
import Aoc.Year2020.Day16 (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

--| A settled position's field is one of its candidates.
def Sound (slot: Slot): Prop := (rule: Rule) → slot.field = Some rule → rule ∈ slot.candidates

--| The slots stand for the positions with `candidates`, soundly settled.
def Keeps (slots: List Slot) (candidates: List (List Rule)): Prop :=
  List.All2 (slot fields => slot.candidates = fields ∧ Sound slot) slots candidates

--| No field is settled at two positions.
def Once (slots: List Slot): Prop := (rule: Rule) → (settledFields slots).count (field => field == rule) ≤ 1

--| One round changes no position's candidates, and settles a position only
--| with one of them.
def Step (after: Slot) (before: Slot): Prop := after.candidates = before.candidates ∧ (Sound before → Sound after)

theorem stepRefl (slot: Slot): Step slot slot := Both rfl (sound => sound)

theorem stepsRefl: (slots: List Slot) → List.All2 Step slots slots
  | [] => Trivial
  | [slot, ..slots] => Both (stepRefl slot) (stepsRefl slots)

theorem keepsStep (next: List Slot) (slots: List Slot) (candidates: List (List Rule)) (steps: List.All2 Step next slots) (keeps: Keeps slots candidates):
    Keeps next candidates :=
  all2Compose (after before fields step kept => Both (Eq.trans (And.left step) (And.left kept)) (And.right step (And.right kept))) next slots candidates steps keeps

theorem settledCons (slot: Slot) (slots: List Slot): settledFields [slot, ..slots] = settledFields [slot] ++ settledFields slots :=
  match field: slot.field with
    | Some rule => rfl
    | None => rfl

--| A position that `settle` passes over.
theorem passSteps (settled: List Rule) (slot: Slot) (slots: List Slot) (next: List Slot) (found: (settle settled slots).map (Cons slot) = Some next)
    (rest: (after: List Slot) → settle settled slots = Some after → List.All2 Step after slots): List.All2 Step next [slot, ..slots] :=
  match later: settle settled slots with
    | Some after => rewrite <- Option.someInjective found in Both (stepRefl slot) (rest after rfl)
    | None => Void.exfalso (Option.noneNotSome next found)

theorem settleSteps (settled: List Rule): (slots: List Slot) → (next: List Slot) → settle settled slots = Some next → List.All2 Step next slots
  | [], next, found => Void.exfalso (Option.noneNotSome next found)
  | [slot, ..slots], next, found =>
    match field: slot.field with
      | Some existing => passSteps settled slot slots next found (settleSteps settled slots)
      | None =>
        match left: slot.remaining settled with
          | [] => passSteps settled slot slots next found (settleSteps settled slots)
          | [only] =>
            rewrite <- Option.someInjective found in
              Both (Both rfl (sound rule same =>
                rewrite <- Option.someInjective same in And.left (List.memFilter slot.candidates (rule => not (settled.contains rule)) (rewrite left in Inl rfl))))
                (stepsRefl slots)
          | [first, second, ..more] => passSteps settled slot slots next found (settleSteps settled slots)

theorem notContainedCount (rule: Rule) (fields: List Rule) (absent: fields.contains rule = False): fields.count (field => field == rule) = 0 :=
  List.countNone fields (field => field == rule) (field member =>
    match same: field == rule with
      | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym absent) ((List.memContains fields rule).backward (rewrite <- DecEq.sound same in member))))
      | False => rfl)

--| What one round adds to the settled fields: one field, not settled before.
def Adds (settled: List Rule) (next: List Slot) (slots: List Slot): Prop :=
  ∃ (rule: Rule) => settled.contains rule = False
    ∧ ((other: Rule) → (settledFields next).count (field => field == other) = (settledFields slots).count (field => field == other) + Bool.toNat (rule == other))

theorem passAdds (settled: List Rule) (slot: Slot) (slots: List Slot) (next: List Slot) (found: (settle settled slots).map (Cons slot) = Some next)
    (rest: (after: List Slot) → settle settled slots = Some after → Adds settled after slots): Adds settled next [slot, ..slots] :=
  match later: settle settled slots with
    | Some after =>
      match rest after rfl with
        | Witness rule (Both fresh counts) =>
          Witness rule (Both fresh (other =>
            rewrite <- Option.someInjective found, settledCons slot after, settledCons slot slots, List.countAppend, List.countAppend, counts other in omega))
    | None => Void.exfalso (Option.noneNotSome next found)

theorem settleAdds (settled: List Rule): (slots: List Slot) → (next: List Slot) → settle settled slots = Some next → Adds settled next slots
  | [], next, found => Void.exfalso (Option.noneNotSome next found)
  | [slot, ..slots], next, found =>
    match field: slot.field with
      | Some existing =>
        let passed := passAdds settled slot slots next found (settleAdds settled slots)
        rewrite field at passed in passed
      | None =>
        match left: slot.remaining settled with
          | [] =>
            let passed := passAdds settled slot slots next found (settleAdds settled slots)
            rewrite field at passed in passed
          | [only] =>
            let kept := And.right (List.memFilter slot.candidates (rule => not (settled.contains rule)) (rewrite left in Inl rfl))
            rewrite <- Option.someInjective found in
              Witness only (Both (Bool.notTrue _ kept) (other =>
                Eq.trans (List.countCons (settledFields slots) only (field => field == other)) (Nat.addComm _ _)))
          | [first, second, ..more] =>
            let passed := passAdds settled slot slots next found (settleAdds settled slots)
            rewrite field at passed in passed

theorem settleOnce (slots: List Slot) (next: List Slot) (found: settle (settledFields slots) slots = Some next) (once: Once slots): Once next :=
  match settleAdds (settledFields slots) slots next found with
    | Witness rule (Both fresh counts) =>
      other =>
        rewrite counts other in
          match same: rule == other with
            | True =>
              let none := notContainedCount rule (settledFields slots) fresh
              rewrite <- DecEq.sound same in omega
            | False =>
              let before := once other
              omega

theorem allSettledFields: (slots: List Slot) → (order: List Rule) → allSettled slots = Some order →
    List.All2 (rule slot => slot.field = Some rule) order slots ∧ order = settledFields slots
  | [], order, found => rewrite <- Option.someInjective found in Both Trivial rfl
  | [slot, ..slots], order, found =>
    match field: slot.field with
      | Some rule =>
        match rest: allSettled slots with
          | Some tail =>
            match allSettledFields slots tail rest with
              | Both fields same => rewrite <- Option.someInjective found in Both (Both field fields) (rewrite same in rfl)
          | None => Void.exfalso (Option.noneNotSome order found)
      | None => Void.exfalso (Option.noneNotSome order found)

theorem eliminateFinds (candidates: List (List Rule)): (rounds: Nat) → (slots: List Slot) → Keeps slots candidates → Once slots →
    (order: List Rule) → eliminate rounds slots = Some order →
    List.All2 (rule fields => rule ∈ fields) order candidates ∧ ((rule: Rule) → order.count (field => field == rule) ≤ 1)
  | rounds, slots, keeps, once, order, found =>
    match done: allSettled slots with
      | Some settled =>
        match allSettledFields slots settled done with
          | Both fields same =>
            rewrite <- Option.someInjective found in
              Both (all2Compose (rule slot fields isField kept => rewrite <- And.left kept in And.right kept rule isField) settled slots candidates fields keeps)
                (rule => rewrite same in once rule)
      | None =>
        match rounds with
          | Zero => Void.exfalso (Option.noneNotSome order found)
          | Succ more =>
            match step: settle (settledFields slots) slots with
              | Some next =>
                eliminateFinds candidates more next (keepsStep next slots candidates (settleSteps _ slots next step) keeps) (settleOnce slots next step once) order found
              | None => Void.exfalso (Option.noneNotSome order found)
