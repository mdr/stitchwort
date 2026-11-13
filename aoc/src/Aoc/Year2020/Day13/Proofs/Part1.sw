--| Part 1: each bus's next departure is the first time at or after yours
--| that it departs, and the bus the program picks leaves no later than any
--| other in service, so its answer is the spec's.

namespace Aoc.Year2020.Day13.Proofs
import Aoc.Year2020.Day13 (..)
import Aoc.Year2020.Day13 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

def idOf: Slot → Nat
  | Listed id => id
  | OutOfService => 0

def isListed: Slot → Bool
  | Listed _ => True
  | OutOfService => False

theorem memBusesFrom (start: Nat) (schedule: List Slot) (bus: Bus) (h: bus ∈ busesFrom start schedule): Listed bus.id ∈ schedule :=
  match schedule, h with
    | [], member => Void.exfalso member
    | [Listed id, ..rest], Inl same => Inl (rewrite <- same in rfl)
    | [Listed id, ..rest], Inr member => Inr (memBusesFrom (Succ start) rest bus member)
    | [OutOfService, ..rest], member => Inr (memBusesFrom (Succ start) rest bus member)

theorem busesFromHas (start: Nat) (schedule: List Slot) (id: Nat) (h: Listed id ∈ schedule): ∃ (bus: Bus) => bus ∈ busesFrom start schedule ∧ bus.id = id :=
  match schedule, h with
    | [], member => Void.exfalso member
    | [Listed other, ..rest], Inl same => Witness ({ id = other, offset = start }) (Both (Inl rfl) (Eq.cong idOf same))
    | [Listed other, ..rest], Inr member =>
      match busesFromHas (Succ start) rest id member with
        | Witness bus (Both inRest same) => Witness bus (Both (Inr inRest) same)
    | [OutOfService, ..rest], Inl same => cases
    | [OutOfService, ..rest], Inr member => busesFromHas (Succ start) rest id member

theorem nextDepartureIs (bus: Bus) (from: Nat): bus.nextDeparture from = Nat.ceilDiv from bus.id * bus.id := rfl

--| The next departure is a departure, at or after `from`, and no departure
--| at or after `from` is earlier.
theorem nextDepartureFirst (bus: Bus) [auto ok: bus.id ≠ 0] (from: Nat):
    Spec.Departs bus.id (bus.nextDeparture from) ∧ from ≤ bus.nextDeparture from
      ∧ (∀ (time: Nat) => Spec.Departs bus.id time → from ≤ time → bus.nextDeparture from ≤ time) :=
  rewrite nextDepartureIs bus from in
    Both (Witness (Nat.ceilDiv from bus.id) rfl)
      (Both (Nat.leCeilDivMul from bus.id)
        (time (Witness trips same) after =>
          rewrite same in Nat.leMulRight (Nat.ceilDiv from bus.id) trips bus.id (Nat.ceilDivLe from trips bus.id (rewrite <- same in after))))

--| When the program answers, the answer is the spec's.
theorem part1Rules (notes: Notes) (answer: Nat) (positive: IdsPositive notes) (found: notes.earliestBus = Some answer): Spec.Part1 notes answer :=
  match m: notes.buses.minimumOf (bus => bus.nextDeparture notes.earliest) with
    | Some first =>
      match f: notes.buses.find (bus => bus.nextDeparture notes.earliest == first) with
        | Some bus =>
          match List.findSome notes.buses (bus => bus.nextDeparture notes.earliest == first) bus f with
            | Both isFirst busMember =>
              let listed := memBusesFrom 0 notes.schedule bus busMember
              let ok: bus.id ≠ 0 := positive bus.id listed
              let least := And.right (List.minimumSome (notes.buses.map (bus => bus.nextDeparture notes.earliest)) first m)
              match nextDepartureFirst bus notes.earliest with
                | Both departs (Both after _) =>
                  Witness bus.id (Witness (bus.nextDeparture notes.earliest)
                    (Both listed (Both departs (Both after
                      (Both
                        (other time otherListed otherDeparts otherAfter =>
                          match busesFromHas 0 notes.schedule other otherListed with
                            | Witness otherBus (Both otherMember same) =>
                              let otherOk: otherBus.id ≠ 0 := rewrite same in positive other otherListed
                              let otherFirst := And.right (And.right (nextDepartureFirst otherBus notes.earliest))
                                time (rewrite same in otherDeparts) otherAfter
                              let atMost := least (otherBus.nextDeparture notes.earliest) (List.memMap notes.buses otherBus otherMember (bus => bus.nextDeparture notes.earliest))
                              omega [isFirst.read])
                        (Eq.sym (Option.someInjective found)))))))

--| The program answers whenever a bus is in service.
theorem part1Answers (notes: Notes) (id: Nat) (listed: Listed id ∈ notes.schedule) (none: notes.earliestBus = None): Void :=
  match busesFromHas 0 notes.schedule id listed with
    | Witness bus (Both member same) =>
      let departure := (bus: Bus) => bus.nextDeparture notes.earliest
      match m: notes.buses.minimumOf (bus => bus.nextDeparture notes.earliest) with
        | None => List.minimumNone (notes.buses.map departure) m (departure bus) (List.memMap notes.buses bus member departure)
        | Some first =>
          match List.memMapElim departure first notes.buses (And.left (List.minimumSome (notes.buses.map departure) first m)) with
            | Witness earliestBus (Both earliestMember leaves) =>
              match f: notes.buses.find (bus => bus.nextDeparture notes.earliest == first) with
                | None =>
                  List.findNoneNotMem notes.buses (bus => bus.nextDeparture notes.earliest == first) earliestBus
                    (rewrite leaves in DecEq.refl first) earliestMember f
