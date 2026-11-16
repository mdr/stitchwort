--| The sieve is right: if an alignment describes the times that suit some
--| buses (`Describes`), adding a bus gives one describing the times that
--| also suit that bus, or none when no time does. No hypothesis on the IDs
--| beyond their being positive: the period is measured, not assumed to be
--| the product of coprime IDs.

namespace Aoc.Year2020.Day13.Proofs
import Aoc.Year2020.Day13 (..)
import Std (Bool, DecEq, Decidable, Eq, Iff, List, Nat, Option, Void)

--| The times that pass `fits` are `alignment.time` and every
--| `alignment.period` minutes after, and no others.
def Describes (fits: Nat → Prop) (alignment: Alignment): Prop :=
  alignment.period ≠ 0 ∧ (∀ (t: Nat) => fits t ↔ ∃ (periods: Nat) => t = alignment.time + periods * alignment.period)

theorem describesIff ∀ [fits other: Nat → Prop] [alignment: Alignment]
    (same: ∀ (t: Nat) => fits t ↔ other t)
    (described: Describes fits alignment):
    Describes other alignment :=
  Both described.left (t => Iff.trans (Iff.symm (same t)) (And.right described t))

theorem startDescribes: Describes (t => Unit) Alignment.start :=
  Both (arithmetic) (t => { forward = u => Witness t (arithmetic), backward = h => () })

--| The earliest time described is the alignment's.
theorem describesEarliest ∀ [fits: Nat → Prop] [alignment: Alignment]
    (described: Describes fits alignment):
    fits alignment.time ∧ (∀ (t: Nat) => fits t → alignment.time ≤ t) :=
  Both (Iff.backward (And.right described alignment.time) (Witness 0 (arithmetic))) (t h =>
    match Iff.forward (And.right described t) h with | Witness periods same => arithmetic)

--| How the sieve sees one bus: whether it departs `periods` periods on.
def suits (alignment: Alignment) (bus: Bus) (periods: Nat): Bool :=
  bus.departsAfter (alignment.time + periods * alignment.period)

theorem suitsMod ∀ (alignment: Alignment) (bus: Bus) (periods: Nat):
    suits alignment bus periods = ((alignment.time + periods * alignment.period + bus.offset) % bus.id == 0) :=
  Nat.dividesMod bus.id _

--| Suiting comes round every `id` periods.
theorem suitsRound ∀ (alignment: Alignment) (bus: Bus) (periods: Nat):
    suits alignment bus periods = suits alignment bus (periods % bus.id) :=
  let split := Nat.divModEq periods bus.id
  let moved: alignment.time + periods * alignment.period + bus.offset
    = (alignment.time + periods % bus.id * alignment.period + bus.offset)
      + (periods / bus.id * alignment.period) * bus.id :=
    algebra [alignment.period * split]
  rewrite suitsMod alignment bus periods,
      suitsMod alignment bus (periods % bus.id),
      moved,
      Nat.modAddMul
        (alignment.time + periods % bus.id * alignment.period + bus.offset)
        (periods / bus.id * alignment.period)
        bus.id then
    byComputing

theorem suitsTrue ∀ (alignment: Alignment) (bus: Bus) (periods: Nat)
    (h: suits alignment bus periods = True):
    (alignment.time + periods * alignment.period + bus.offset) % bus.id = 0 :=
  DecEq.sound (rewrite <- suitsMod alignment bus periods then h)

--| Once both `p` and `p + d` periods suit the bus, `d` periods are a
--| multiple of its ID.
theorem periodDivides ∀ (alignment: Alignment) (bus: Bus) (p d: Nat)
    (now: suits alignment bus p = True)
    (later: suits alignment bus (p + d) = True):
    (d * alignment.period) % bus.id = 0 :=
  let x := alignment.time + p * alignment.period + bus.offset
  let moved: alignment.time + (p + d) * alignment.period + bus.offset = x + d * alignment.period := algebra
  calc (d * alignment.period) % bus.id
    _ = (0 + d * alignment.period) % bus.id := byComputing
    _ = (x % bus.id + d * alignment.period) % bus.id := rewrite suitsTrue alignment bus p now then byComputing
    _ = (x + d * alignment.period) % bus.id := Nat.modAddMod x (d * alignment.period) bus.id
    _ = 0 := rewrite <- moved then suitsTrue alignment bus (p + d) later

--| Stepping on by a multiple of the ID's worth of periods changes nothing.
theorem suitsMultiple ∀ (alignment: Alignment) (bus: Bus) (p q d: Nat)
    (h: (d * alignment.period) % bus.id = 0):
    suits alignment bus (p + q * d) = suits alignment bus p :=
  let x := alignment.time + p * alignment.period + bus.offset
  let moved: alignment.time + (p + q * d) * alignment.period + bus.offset = x + q * (d * alignment.period) := algebra
  rewrite suitsMod alignment bus (p + q * d),
      suitsMod alignment bus p,
      moved,
      Nat.modAddOfModZero x
        (q * (d * alignment.period))
        bus.id
        (Nat.modMulOfModZero q (d * alignment.period) bus.id h) then
    byComputing

theorem stepDescribes ∀ [fits: Nat → Prop] [alignment: Alignment] (bus: Bus)
    (described: Describes fits alignment) (first: Nat)
    (firstSuits: suits alignment bus first = True)
    (firstLeast: ∀ (e: Nat) => e < first → suits alignment bus e = False) (again: Nat)
    (againSuits: suits alignment bus (first + 1 + again) = True)
    (againLeast: ∀ (e: Nat) => e < again → suits alignment bus (first + 1 + e) = False):
    Describes (t => fits t ∧ bus.departsAfter t = True) {
      time = alignment.time + first * alignment.period,
      period = (again + 1) * alignment.period
    } :=
  let period := alignment.period
  let nonZero: period ≠ 0 := described.left
  let step: ((again + 1) * period) % bus.id = 0 := periodDivides alignment bus first (again + 1) firstSuits againSuits
  Both
    (zero =>
      match Nat.mulEqZero (again + 1) period zero with
        | Inl none => arithmetic
        | Inr none => nonZero none)
    (t =>
      {
        forward = (Both fitsT departsT) =>
          match Iff.forward (And.right described t) fitsT with
            | Witness j tIs =>
              let jSuits: suits alignment bus j = True := rewrite tIs at departsT then departsT
              if early: j < first then
                Void.impossible (Bool.falseNotTrue (rewrite firstLeast j early at jSuits then jSuits))
              else
                let k := j - first
                let split := Nat.divModEq k (again + 1)
                let r := k % (again + 1)
                let q := k / (again + 1)
                let rBelow := Nat.modLess k (again + 1) (arithmetic)
                let jIs: j = first + r + q * (again + 1) := arithmetic [split]
                let rSuits: suits alignment bus (first + r) = True :=
                  rewrite <- suitsMultiple alignment bus (first + r) q (again + 1) step, <- jIs then jSuits
                match r with
                  | Zero => Witness q (algebra [tIs, alignment.period * jIs])
                  | Succ s =>
                    Void.impossible (Bool.falseNotTrue (rewrite againLeast s (arithmetic) at rSuits then rSuits)),
        backward = (Witness q tIs) =>
          let tAs: t = alignment.time + (first + q * (again + 1)) * period := rewrite tIs then algebra
          Both
            (Iff.backward (And.right described t) (Witness (first + q * (again + 1)) tAs))
            (rewrite tAs then
              (rewrite suitsMultiple alignment bus first q (again + 1) step then firstSuits: suits alignment bus
                (first + q * (again + 1))
                = True))
      })

theorem suitsRoundOnce ∀ (alignment: Alignment) (bus: Bus)
    [auto ok: bus.id ≠ 0] (p: Nat):
    suits alignment bus (p + 1 + (bus.id - 1)) = suits alignment bus p :=
  let multiple: (bus.id * alignment.period) % bus.id = 0 :=
    rewrite Nat.mulComm bus.id alignment.period then Nat.modAddMul 0 alignment.period bus.id
  Eq.trans
    (Eq.cong (n => suits alignment bus n) (arithmetic: p + 1 + (bus.id - 1) = p + 1 * bus.id))
    (suitsMultiple alignment bus p 1 bus.id multiple)

theorem addDescribes ∀ [fits: Nat → Prop] [alignment: Alignment] (bus: Bus)
    (described: Describes fits alignment) (next: Alignment)
    (added: alignment.add bus = Some next):
    Describes (t => fits t ∧ bus.departsAfter t = True) next :=
  match found: (0 ..< bus.id).find (suits alignment bus) with
    | None => Void.impossible (Option.noneNotSome next (rewrite found at added then added))
    | Some first =>
      match List.findRangeSome (suits alignment bus) bus.id first found with
        | Both firstSuits (Both firstBelow firstLeast) =>
          match foundAgain: (0 ..< bus.id).find (more => suits alignment bus (first + 1 + more)) with
            | None =>
              let never :=
                List.findRangeNone
                  (more => suits alignment bus (first + 1 + more))
                  bus.id
                  foundAgain
                  (bus.id - 1)
                  (arithmetic)
              Void.impossible
                (Bool.trueNotFalse (rewrite suitsRoundOnce alignment bus first, firstSuits at never then never))
            | Some again =>
              match List.findRangeSome (more => suits alignment bus (first + 1 + more)) bus.id again foundAgain with
                | Both againSuits (Both againBelow againLeast) =>
                  rewrite <- Option.someInjective (rewrite found, foundAgain at added then added) then
                    stepDescribes bus described first firstSuits firstLeast again againSuits againLeast

theorem addNone ∀ [fits: Nat → Prop] [alignment: Alignment] (bus: Bus)
    [auto ok: bus.id ≠ 0]
    (described: Describes fits alignment)
    (added: alignment.add bus = None)
    (t: Nat) (fitsT: fits t)
    (departsT: bus.departsAfter t = True):
    Void :=
  match found: (0 ..< bus.id).find (suits alignment bus) with
    | Some first => Option.someNotNone _ (rewrite found at added then added)
    | None =>
      match Iff.forward (And.right described t) fitsT with
        | Witness j tIs =>
          let jSuits: suits alignment bus j = True := rewrite tIs at departsT then departsT
          let never := List.findRangeNone (suits alignment bus) bus.id found (j % bus.id) (Nat.modLess j bus.id ok)
          Bool.trueNotFalse (rewrite <- suitsRound alignment bus j, jSuits at never then never)

--| Each bus departs its offset after `t`.
def AllDepart (buses: List Bus) (t: Nat): Prop := List.All (bus => bus.departsAfter t = True) buses

def Positive (buses: List Bus): Prop := List.All (bus => bus.id ≠ 0) buses

theorem addAllDescribes ∀ [fits: Nat → Prop] (buses: List Bus)
    (positive: Positive buses) (alignment: Alignment)
    (described: Describes fits alignment) (final: Alignment)
    (added: alignment.addAll buses = Some final):
    Describes (t => fits t ∧ AllDepart buses t) final :=
  match buses with
    | [] =>
      describesIff
        (t => { forward = h => Both h (), backward = h => h.left })
        (rewrite <- Option.someInjective added then described)
    | [bus, ..rest] =>
      match positive with
        | Both ok restPositive =>
          match e: alignment.add bus with
            | Some next =>
              let later := addAllDescribes rest restPositive next (addDescribes bus described next e) final added
              describesIff
                (t =>
                  {
                    forward = (Both (Both f d) all) => Both f (Both d all),
                    backward = (Both f (Both d all)) => Both (Both f d) all
                  })
                later

theorem addAllNone ∀ [fits: Nat → Prop] (buses: List Bus)
    (positive: Positive buses) (alignment: Alignment)
    (described: Describes fits alignment)
    (added: alignment.addAll buses = None)
    (t: Nat) (fitsT: fits t)
    (all: AllDepart buses t):
    Void :=
  match buses with
    | [bus, ..rest] =>
      match positive with
        | Both ok restPositive =>
          match all with
            | Both departs restDepart =>
              match e: alignment.add bus with
                | None => addNone bus described e t fitsT departs
                | Some next =>
                  addAllNone rest restPositive next
                    (addDescribes bus described next e)
                    added
                    t
                    (Both fitsT departs)
                    restDepart
