--| Part 2: the buses the program reads off the schedule all depart at their
--| offsets exactly when the schedule lines up as the spec says, so the
--| sieve's earliest time is the spec's, and when the sieve finds none, no
--| time lines up.

namespace Aoc.Year2020.Day13.Proofs
import Aoc.Year2020.Day13 (..)
import Aoc.Year2020.Day13 (Spec)
import Std (Eq, Iff, List, Nat, Option, Void)

--| Every bus in service has an ID of at least 1: what the parser checks.
def IdsPositive (notes: Notes): Prop := ∀ (id: Nat) => Listed id ∈ notes.schedule → id ≠ 0

theorem departsAfterSpec (bus: Bus) (t: Nat): bus.departsAfter t = True ↔ Spec.Departs bus.id (t + bus.offset) := Nat.dividesIff bus.id (t + bus.offset)

def busesFrom (start: Nat) (schedule: List Slot): List Bus := List.filterMap (List.withIndexFrom start schedule) (((offset, slot)) => slot.bus offset)

theorem linedUpFrom (t: Nat) (start: Nat) (schedule: List Slot): AllDepart (busesFrom start schedule) t ↔ Spec.LinedUp schedule (t + start) :=
  match schedule with
    | [] => { forward = h => (), backward = h => () }
    | [Listed id, ..rest] =>
      let next := linedUpFrom t (Succ start) rest
      let later := rewrite Nat.addSucc t start, <- Nat.addOne (t + start) at next in next
      {
        forward = (Both departs all) => Both (Iff.forward (departsAfterSpec { id, offset = start } t) departs) (Iff.forward later all),
        backward = (Both departs lined) => Both (Iff.backward (departsAfterSpec { id, offset = start } t) departs) (Iff.backward later lined)
      }
    | [OutOfService, ..rest] =>
      let next := linedUpFrom t (Succ start) rest
      rewrite Nat.addSucc t start, <- Nat.addOne (t + start) at next in next

theorem positiveFrom (start: Nat) (schedule: List Slot) (h: ∀ (id: Nat) => Listed id ∈ schedule → id ≠ 0): Positive (busesFrom start schedule) :=
  match schedule with
    | [] => ()
    | [Listed id, ..rest] => Both (h id (Inl rfl)) (positiveFrom (Succ start) rest (other member => h other (Inr member)))
    | [OutOfService, ..rest] => positiveFrom (Succ start) rest (other member => h other (Inr member))

theorem busesLinedUp (notes: Notes) (t: Nat): AllDepart notes.buses t ↔ Spec.LinedUp notes.schedule t :=
  let from := linedUpFrom t 0 notes.schedule
  rewrite Nat.addZero t at from in from

theorem finalDescribes (notes: Notes) (final: Alignment) (positive: IdsPositive notes) (added: Alignment.start.addAll notes.buses = Some final):
    Describes (Spec.LinedUp notes.schedule) final :=
  describesIff [fits := t => Unit ∧ AllDepart notes.buses t] (t => Iff.trans { forward = h => And.right h, backward = h => Both () h } (busesLinedUp notes t))
    (addAllDescribes notes.buses (positiveFrom 0 notes.schedule positive) Alignment.start startDescribes final added)

--| When the sieve finds a time, it is the spec's answer.
theorem part2Rules (notes: Notes) (answer: Nat) (positive: IdsPositive notes) (found: notes.earliestLineUp = Some answer): Spec.Part2 notes answer :=
  match e: Alignment.start.addAll notes.buses with
    | Some final =>
      rewrite <- Option.someInjective found in describesEarliest (finalDescribes notes final positive e)

--| When it finds none, no time lines up.
theorem part2Never (notes: Notes) (positive: IdsPositive notes) (none: notes.earliestLineUp = None) (t: Nat) (lined: Spec.LinedUp notes.schedule t): Void :=
  match e: Alignment.start.addAll notes.buses with
    | None =>
      addAllNone notes.buses (positiveFrom 0 notes.schedule positive) Alignment.start startDescribes e t () (Iff.backward (busesLinedUp notes t) lined)
