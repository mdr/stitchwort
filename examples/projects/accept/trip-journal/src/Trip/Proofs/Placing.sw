-- Placing stops, albums and pins in the merged legs.
namespace Trip.Proofs

import Std (Float, List, Option, Eq, Void, Bool, Decidable, DecEq)
import Trip.Model (..)
import Trip.Merge (..)

theorem findLegMem ∀ (legs: List Leg) (id: Nat) (leg: Leg) (h: findLeg legs id = Some leg): leg ∈ legs :=
  And.right (List.findSome legs (l => l.id == id) leg h)

theorem legOfMem ∀ (legs: List Leg) (pos: Position) (leg: Leg) (h: legOf legs pos = Some leg): leg ∈ legs :=
  match e: pos.leg with
    | Some id => findLegMem legs id leg h
    | None => Void.exfalso (Option.noneNotSome leg h)

theorem firstCoveringMem ∀ (legs: List Leg) (t: Float) (leg: Leg)
    (h: firstCovering legs t = Some leg):
    (leg.covers t = True) ∧ (leg ∈ legs) :=
  List.findSome legs (l => l.covers t) leg h

-- An item in a leg that didn't move gets back exactly its old time.
theorem placeUnmoved ∀ (leg: Leg) (pos: Position) (same: leg.start = pos.legStart): placeIn leg pos = pos.time :=
  rewrite same, DecEq.refl pos.legStart in rfl

-- Stops and albums

-- Wherever a position was, it settles within the trip.
theorem settleWithin ∀ (legs: List Leg)
    (c: ContiguousFrom 0.0 legs)
    (oks: List.All LegOk legs) (pos: Position):
    within legs (settle legs pos) = True :=
  match e: legOf legs pos with
    | Some leg =>
      let inLegs: leg ∈ legs := legOfMem legs pos leg e
      match List.memOfAll LegOk legs oks leg inLegs with
        | Both pts (Both nonNeg fin) =>
          let ok: Float.leq leg.start leg.end = True := startLeEnd leg nonNeg
          match legBounds 0.0 legs c oks leg inLegs with
            | Both low high =>
              Bool.andIntro
                (floatLeTrans 0.0 leg.start
                  (clamp leg.start leg.end (placeIn leg pos))
                  low
                  (clampLow leg.start leg.end (placeIn leg pos) ok))
                (floatLeTrans
                  (clamp leg.start leg.end (placeIn leg pos))
                  leg.end
                  (lastEnd legs)
                  (clampHigh leg.start leg.end (placeIn leg pos) ok)
                  high)
    | None =>
      let ok: Float.leq 0.0 (lastEnd legs) = True := zeroLeLastEnd legs c oks
      Bool.andIntro (clampLow 0.0 (lastEnd legs) pos.time ok) (clampHigh 0.0 (lastEnd legs) pos.time ok)

-- In a well-formed trip's own legs, a time that is within the trip settles
-- where it was.
theorem settleSelf ∀ (legs: List Leg)
    (ids: List.Distinct (List.map legs (leg => leg.id))) (t: Float)
    (w: within legs t = True):
    settle legs (locate legs t) = t :=
  match e: firstCovering legs t with
    | Some leg =>
      match firstCoveringMem legs t leg e with
        | Both covers inLegs =>
          rewrite List.findKeyDistinct (l => l.id) legs ids leg inLegs, DecEq.refl leg.start in
            clampInside leg.start leg.end t (Bool.andLeft covers) (floatLessLe t leg.end (Bool.andRight covers))
    | None => clampInside 0.0 (lastEnd legs) t (Bool.andLeft w) (Bool.andRight w)

-- Pins

theorem keepsFits ∀ (legs: List Leg) (id: Nat) (pin: Pin) (h: keepsIn legs id pin = True): pinFits legs pin = True :=
  match e: firstCovering legs pin.start with
    | Some leg => Bool.andRight h
    | None => cases

-- A pin the merge keeps lies wholly inside the first leg covering its start.
theorem placePinFits ∀ (legs: List Leg) (pin: Pin) (pos: Position) (kept: Pin)
    (h: placePin legs pin pos = Some kept):
    pinFits legs kept = True :=
  match e: legOf legs pos with
    | Some leg =>
      match k: keepsIn legs leg.id (pin.startAt (placeIn leg pos)) with
        | True => rewrite <- Option.someInjective h in keepsFits legs leg.id (pin.startAt (placeIn leg pos)) k
        | False => Void.exfalso (Option.noneNotSome kept h)
    | None => Void.exfalso (Option.noneNotSome kept h)

theorem placePinId ∀ (legs: List Leg) (pin: Pin) (pos: Position) (kept: Pin)
    (h: placePin legs pin pos = Some kept):
    kept.id = pin.id :=
  match e: legOf legs pos with
    | Some leg =>
      match k: keepsIn legs leg.id (pin.startAt (placeIn leg pos)) with
        | True => rewrite <- Option.someInjective h in rfl
        | False => Void.exfalso (Option.noneNotSome kept h)
    | None => Void.exfalso (Option.noneNotSome kept h)

theorem pinStartAtSame ∀ (pin: Pin): pin.startAt pin.start = pin := match pin with | { id, start, duration } => rfl

-- In a well-formed trip's own legs, a pin that fits is kept where it was.
theorem placePinSelf ∀ (legs: List Leg)
    (ids: List.Distinct (List.map legs (leg => leg.id))) (pin: Pin)
    (fits: pinFits legs pin = True):
    placePin legs pin (locate legs pin.start) = Some pin :=
  match e: firstCovering legs pin.start with
    | Some leg =>
      rewrite List.findKeyDistinct (l => l.id) legs ids leg (And.right (firstCoveringMem legs pin.start leg e)),
          DecEq.refl leg.start,
          pinStartAtSame pin,
          e,
          DecEq.refl leg.id in
        rewrite fits in rfl
    | None => cases
