-- Worked scenarios: a base trip, edited on one device or both, then merged.
namespace Trip.Tests

import Std (Float, List, Option, Text)
import Trip.Model (..)
import Trip.Merge (..)
import Trip.Proofs (mergeSelf, remotePinsKept)
import Std (byDecision)

def walk: Leg := {
  id = 1,
  start = 0.0,
  duration = 600.0,
  points = [{ id = 1, time = 0.0 }, { id = 2, time = 300.0 }],
  notes = Some [{ time = 10.0, text = "leaving the hostel" }]
}

def ferry: Leg := {
  id = 2,
  start = 600.0,
  duration = 900.0,
  points = [{ id = 3, time = 600.0 }, { id = 4, time = 1200.0 }],
  notes = None
}

def base: Trip := {
  name = "Lakes",
  settings = { units = Metric, showNotes = True },
  legs = [walk, ferry],
  stops = [
    { id = 1, start = 100.0, name = "cafe", kind = Free },
    { id = 2, start = 700.0, name = "museum", kind = Planned 0 }
  ],
  pins = [{ id = 1, start = 50.0, duration = 30.0 }, { id = 2, start = 1300.0, duration = 100.0 }],
  albums = [
    { id = 1, start = 0.0, label = "morning", photos = [Plain 1, Panorama 2 180] },
    { id = 2, start = 600.0, label = "crossing", photos = [Plain 3] }
  ],
  itinerary = Some { fileId = 7, places = [{ id = 1, name = "museum" }, { id = 2, name = "park" }] },
  summary = Some (summarize [walk, ferry])
}

def startsOf (trip: Trip): List Float := trip.legs.map (leg => leg.start)

test "merging a trip with itself changes nothing" := merge base base == base

-- A leg extended on one device: the remote walk went on for 300 s more, with
-- another fix, and that device laid the ferry after it.

def longWalk: Leg := { walk | duration = 900.0, points = walk.points ++ [{ id = 5, time = 800.0 }] }

def extended: Trip := { base |
  legs = [longWalk, moveLeg 900.0 ferry],
  pins = [{ id = 1, start = 50.0, duration = 30.0 }, { id = 2, start = 1600.0, duration = 100.0 }],
  summary = Some (summarize [longWalk, moveLeg 900.0 ferry])
}

-- The local copy added a pin late in the ferry.
def localPin: Trip := { base | pins = base.pins ++ [{ id = 3, start = 1250.0, duration = 50.0 }] }

-- The local stop and album in the ferry, and the local pin, keep their
-- offsets into it (650 s for the pin); the remote pins are where the remote
-- copy put them.
test "an extended leg moves the legs after it, and what is pinned in them" :=
  let merged := merge localPin extended
  startsOf merged == [0.0, 900.0]
    ∧ (merged.legs.map (leg => leg.points.length)) == [3, 2]
    ∧ (merged.stops.map (stop => stop.start)) == [100.0, 1000.0]
    ∧ (merged.pins.map (pin => (pin.id, pin.start))) == [(1, 50.0), (3, 1550.0), (2, 1600.0)]
    ∧ (merged.albums.map (album => album.start)) == [0.0, 900.0]

test "the ferry's points and notes move with it" :=
  ((merge base extended).legs.flatMap (leg => leg.points.map (point => point.time)))
    == [0.0, 300.0, 800.0, 900.0, 1500.0]

-- The remote copy laid the legs out as the merge does, so the merged legs are
-- the remote legs, and the remote summary is kept.
test "a summary made from the merged legs is kept" :=
  (merge base extended).summary == Some (summarize [longWalk, moveLeg 900.0 ferry])

-- The walk's notes come from the remote copy, which has them.
test "route notes come from the remote copy" := (merge base extended).legs.map (leg => leg.notes) == [walk.notes, None]

-- A leg shortened on one device: crash recovery cut the remote ferry to
-- 500 s (same number of fixes, so it wins the tie). The local copy had added
-- a pin late in the ferry. Both late pins no longer fit and are dropped.

def shortFerry: Leg := { ferry | duration = 500.0, points = [{ id = 3, time = 600.0 }, { id = 4, time = 1000.0 }] }

def shortened: Trip := { base | legs = [walk, shortFerry] }

test "a shortened leg drops the pins that no longer fit" :=
  let merged := merge localPin shortened
  (merged.pins.map (pin => pin.id)) == [1] ∧ lastEnd merged.legs == 1100.0

-- A stop past the new end is clamped to the leg's nearer end.
def lateStop: Trip := { base | stops = [{ id = 3, start = 1400.0, name = "pier", kind = Free }] }

test "a stop past its shortened leg is clamped to the leg's end" :=
  ((merge lateStop shortened).stops.map (stop => (stop.id, stop.start))) == [(3, 1100.0), (1, 100.0), (2, 700.0)]

-- A local pin in the ferry that the remote copy doesn't have, while the
-- remote copy moved pin 1: the remote position wins, and the pins are
-- sorted by start.
def movedPin: Trip :=
  { base | pins = [{ id = 2, start = 1300.0, duration = 100.0 }, { id = 1, start = 400.0, duration = 30.0 }] }

def extraPin: Trip := { base | pins = base.pins ++ [{ id = 4, start = 20.0, duration = 5.0 }] }

test "pins take the remote position and are sorted by start" :=
  ((merge extraPin movedPin).pins.map (pin => (pin.id, pin.start))) == [(4, 20.0), (1, 400.0), (2, 1300.0)]

-- Concurrent edits to the same album: each device added a photo to album 1.

def withPhoto (trip: Trip) (photo: Photo): Trip := { trip |
  albums = trip.albums.map (album => if album.id == 1 then { album | photos = album.photos ++ [photo] } else album)
}

test "an album edited on both devices has the remote photos, then the new local ones" :=
  ((merge (withPhoto base (Plain 10)) (withPhoto base (Plain 11))).albums.map (album => album.photos))
    == [[Plain 1, Panorama 2 180, Plain 11, Plain 10], [Plain 3]]

-- A photo moved between albums on one device.

def movedLocally: Trip := { base |
  albums = [
    { id = 1, start = 0.0, label = "morning", photos = [Plain 1, Panorama 2 180, Plain 3] },
    { id = 2, start = 600.0, label = "crossing", photos = [] }
  ]
}

test "a photo moved locally stays where the local copy put it" :=
  ((merge movedLocally base).albums.map (album => album.photos)) == [[Plain 1, Panorama 2 180, Plain 3], []]

-- Moved on the remote device instead, the local copy's album still holds it
-- after the merge, so it stays there: the rule prefers the local album.
test "a photo moved remotely stays in the local album" :=
  ((merge base movedLocally).albums.map (album => album.photos)) == [[Plain 1, Panorama 2 180], [Plain 3]]

-- A replaced itinerary: the remote copy loaded another plan.

def newPlan: Trip := { base | itinerary = Some { fileId = 8, places = [{ id = 1, name = "harbour" }] } }

test "a replaced plan frees the local stops linked to the old one" :=
  let merged := merge base newPlan
  (merged.stops.map (stop => stop.kind)) == [Free, Free] ∧ merged.itinerary == newPlan.itinerary

-- The same plan, with a place added on each device.

def withPlace (trip: Trip) (place: Place): Trip :=
  { trip | itinerary = trip.itinerary.map (plan => { plan | places = plan.places ++ [place] }) }

test "the same plan merges its places" :=
  ((merge (withPlace base { id = 3, name = "fort" }) (withPlace base { id = 4, name = "mill" })).itinerary.map (plan =>
    plan.places.map (place => place.id)))
    == Some [1, 2, 4, 3]

-- A summary is dropped when the merged legs are neither copy's: each device
-- extended another leg.

def longFerry: Leg := { ferry | duration = 1000.0, points = ferry.points ++ [{ id = 6, time = 1550.0 }] }

def ferryExtended: Trip := { base | legs = [walk, longFerry], summary = Some (summarize [walk, longFerry]) }

test "a summary not made from the merged legs is dropped" :=
  let merged := merge ferryExtended extended
  merged.summary == None ∧ (merged.legs.map (leg => leg.points.length)) == [3, 3]

-- The local walk has more points and the ferry is laid after it, so the
-- merged legs are the local ones.
test "the local summary is kept when the merged legs are the local ones" :=
  (merge extended { base | summary = None }).summary == extended.summary

-- The remote legs are the merged ones too, and the remote copy is asked
-- first.
test "the remote copy's lack of a summary wins when its legs are the merged ones" :=
  (merge extended { extended | summary = None }).summary == None

-- The name: the remote one, unless it's blank.
test "a blank remote name keeps the local one" :=
  (merge base { base | name = "  " }).name == "Lakes" ∧ (merge base { base | name = "Lakes 2025" }).name == "Lakes 2025"

-- Why a position keeps the old time: the start plus the offset isn't always
-- the time it came from.
test "an unmoved leg gives back the exact time" :=
  let leg := { walk | start = 0.2 }
  let pos := locate [leg] 0.9
  placeIn leg pos == 0.9 ∧ leg.start + pos.offset == 0.8999999999999999

-- Nor is the offset into a moved leg kept exactly: 0.3 is 0.2 into a leg at
-- 0.1, but its new time is 0.19999999999999996 into the leg moved to 0.5.
test "a moved leg can round the offset" :=
  let pos := locate [{ walk | start = 0.1 }] 0.3
  let moved := placeIn { walk | start = 0.5 } pos
  pos.offset == 0.19999999999999998 ∧ moved == 0.7 ∧ moved - 0.5 == 0.19999999999999996

-- The base trip is well-formed, so `WellFormed` holds of something, and
-- `mergeSelf` applies to it.
theorem baseWellFormed: WellFormed base := byDecision

theorem baseMergedWithItself: merge base base = base := mergeSelf base baseWellFormed

-- `remotePinsKept`'s hypotheses hold: the extended copy's pin 2 still fits
-- its leg after the merge.
def latePin: Pin := { id = 2, start = 1600.0, duration = 100.0 }

theorem extendedPinKept: latePin ∈ (merge localPin extended).pins :=
  remotePinsKept localPin extended latePin (Inr (Inl rfl)) latePin rfl
