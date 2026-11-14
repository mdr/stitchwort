-- A trip journal, kept on two devices: GPS legs laid end to end, the stops,
-- photo pins and albums pinned to times in them, a planned itinerary and an
-- auto-generated summary. Times are `Float` seconds from the start of the
-- trip.
namespace Trip.Model

import Std (Decidable, Float, List, Option, Text)

-- A GPS fix of a leg's track, at an absolute time.
type Point = { id: Nat, time: Float }

-- A line of a leg's route notes (a transcript), at an absolute time.
type Note = { time: Float, text: Text }

-- A GPS track. Moving a leg moves its points and notes with it.
type Leg = { id: Nat, start: Float, duration: Float, points: List Point, notes: Option (List Note) }

def Leg.end (leg: Leg): Float := leg.start + leg.duration

type StopKind = | Free | Planned (index: Nat)

-- A place visited, either free or one of the planned places (by its index
-- in the itinerary).
type Stop = { id: Nat, start: Float, name: Text, kind: StopKind }

-- A burst of photos, covering `duration` seconds from `start`.
type Pin = { id: Nat, start: Float, duration: Float }

type Photo = | Plain (photoId: Nat) | Panorama (photoId: Nat) (degrees: Nat)

def Photo.id: Photo → Nat
  | Plain photoId => photoId
  | Panorama photoId _ => photoId

type Album = { id: Nat, start: Float, label: Text, photos: List Photo }

type Place = { id: Nat, name: Text }

-- The plan, as a file the devices share: a file id and its places.
type Itinerary = { fileId: Nat, places: List Place }

-- Made from the legs, by `summarize`.
type Summary = { legCount: Nat, pointCount: Nat, length: Float }

type Units = | Metric | Imperial

type Settings = { units: Units, showNotes: Bool }

type Trip = {
  name: Text,
  settings: Settings,
  legs: List Leg,
  stops: List Stop,
  pins: List Pin,
  albums: List Album,
  itinerary: Option Itinerary,
  summary: Option Summary
}

-- Where the trip ends: the end of its last leg, 0 with none.
def lastEnd: List Leg → Float
  | [] => 0.0
  | [leg] => leg.end
  | [_, ..rest] => lastEnd rest

def summarize (legs: List Leg): Summary :=
  { legCount = legs.length, pointCount = (legs.map (leg => leg.points.length)).sum, length = lastEnd legs }

-- A leg covers the times from its start up to, not including, its end, so
-- a time at the boundary of two legs is in the second.
def Leg.covers (leg: Leg) (t: Float): Bool := Float.leq leg.start t ∧ Float.less t leg.end

def firstCovering (legs: List Leg) (t: Float): Option Leg := legs.find (leg => leg.covers t)

def findLeg (legs: List Leg) (id: Nat): Option Leg := legs.find (leg => leg.id == id)

-- The pin's span, from its start to its start plus its duration, lies in
-- the leg.
def Pin.fitsIn (pin: Pin) (leg: Leg): Bool :=
  Float.leq leg.start pin.start ∧ Float.leq 0.0 pin.duration ∧ Float.leq (pin.start + pin.duration) leg.end

-- The pin lies in the first leg covering its start.
def pinFits (legs: List Leg) (pin: Pin): Bool := match firstCovering legs pin.start with
  | Some leg => pin.fitsIn leg
  | None => False

-- From 0 to the end of the trip.
def within (legs: List Leg) (t: Float): Bool := Float.leq 0.0 t ∧ Float.leq t (lastEnd legs)

def photoIds (albums: List Album): List Nat := albums.flatMap (album => album.photos.map Photo.id)

-- The well-formedness of a trip

-- Each leg starts where the one before it ends, the first at `at`.
def ContiguousFrom: Float → List Leg → Prop
  | at, [] => Unit
  | at, [leg, ..rest] => (leg.start = at) ∧ (ContiguousFrom (at + leg.duration) rest)

-- A duration is not negative in the total order, which rules out `-0.0`
-- (below `0.0` there), and finite, which rules out the NaN and the
-- infinities (`0.0 <= Float.nan` holds in the total order).
def GoodDuration (leg: Leg): Prop := (0.0 <= leg.duration) ∧ (Float.isFinite leg.duration = True)

-- What each leg needs on its own: distinct track point ids, and a good
-- duration.
def LegOk (leg: Leg): Prop := (List.Distinct (leg.points.map (point => point.id))) ∧ (GoodDuration leg)

def PlaceIdsDistinct: Option Itinerary → Prop
  | None => Unit
  | Some plan => List.Distinct (plan.places.map (place => place.id))

-- Decisions for the parts of `WellFormed` defined by recursion on a list,
-- which nothing in std decides for a list not yet known. With them,
-- `WellFormed` gets a derived decision (SW-1015), so the counterexample
-- search can try the theorems that assume it.

def decAll (p: a → Prop) (dec: (x: a) → Decidable (p x)): (xs: List a) → Decidable (List.All p xs)
  | [] => Decidable.yes Trivial
  | [x, ..xs] => Decidable.and (dec x) (decAll p dec xs)

def decSorted (le: a → a → Bool): (xs: List a) → Decidable (List.Sorted le xs)
  | [] => Decidable.yes Trivial
  | [x] => Decidable.and (Decidable.yes Trivial) (Decidable.yes Trivial)
  | [x, y, ..ys] =>
    Decidable.and (if h: le x y = True then Decidable.yes h else Decidable.no h) (decSorted le [y, ..ys])

instance decContiguousFrom: (start: Float) → (legs: List Leg) → Decidable (ContiguousFrom start legs)
  | start, [] => Decidable.yes Trivial
  | start, [leg, ..rest] =>
    Decidable.and
      (if h: leg.start = start then Decidable.yes h else Decidable.no h)
      (decContiguousFrom (start + leg.duration) rest)

instance decLegsOk (legs: List Leg): Decidable (List.All LegOk legs) :=
  decAll LegOk (leg => if h: LegOk leg then Decidable.yes h else Decidable.no h) legs

instance decPinsFit (legs: List Leg) (pins: List Pin): Decidable (List.All (pin => pinFits legs pin = True) pins) :=
  decAll
    (pin => pinFits legs pin = True)
    (pin => if h: pinFits legs pin = True then Decidable.yes h else Decidable.no h)
    pins

instance decPinsSorted (pins: List Pin): Decidable (List.Sorted (a b => Float.leq a.start b.start) pins) :=
  decSorted (a b => Float.leq a.start b.start) pins

instance decStopsWithin (legs: List Leg) (stops: List Stop):
    Decidable (List.All (stop => within legs stop.start = True) stops) :=
  decAll
    (stop => within legs stop.start = True)
    (stop => if h: within legs stop.start = True then Decidable.yes h else Decidable.no h)
    stops

instance decAlbumsWithin (legs: List Leg) (albums: List Album):
    Decidable (List.All (album => within legs album.start = True) albums) :=
  decAll
    (album => within legs album.start = True)
    (album => if h: within legs album.start = True then Decidable.yes h else Decidable.no h)
    albums

instance decPlaceIds: (plan: Option Itinerary) → Decidable (PlaceIdsDistinct plan)
  | None => Decidable.yes Trivial
  | Some plan => if h: List.Distinct (plan.places.map (place => place.id)) then Decidable.yes h else Decidable.no h

type WellFormed (trip: Trip): Prop = {
  contiguous: ContiguousFrom 0.0 trip.legs,
  legIds: List.Distinct (trip.legs.map (leg => leg.id)),
  legsOk: List.All LegOk trip.legs,
  pinIds: List.Distinct (trip.pins.map (pin => pin.id)),
  pinsFit: List.All (pin => pinFits trip.legs pin = True) trip.pins,
  pinsSorted: List.Sorted (a b => Float.leq a.start b.start) trip.pins,
  stopIds: List.Distinct (trip.stops.map (stop => stop.id)),
  albumIds: List.Distinct (trip.albums.map (album => album.id)),
  photoIdsDistinct: List.Distinct (photoIds trip.albums),
  stopsWithin: List.All (stop => within trip.legs stop.start = True) trip.stops,
  albumsWithin: List.All (album => within trip.legs album.start = True) trip.albums,
  placeIds: PlaceIdsDistinct trip.itinerary
}
