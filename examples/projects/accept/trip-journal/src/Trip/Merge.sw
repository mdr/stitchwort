-- Merging two copies of a trip edited offline, `merge local remote`.
namespace Trip.Merge

import Std (Float, List, Nat, Option, Text)
import Trip.Model (..)

-- Legs

-- Times moved from a leg that started at `from` to one that starts at `to`.
-- Nothing moves when the start is the same, so no time is rounded.
def shiftNotes (from: Float) (to: Float) (notes: List Note): List Note :=
  if from == to then notes else notes.map (note => { note | time = to + (note.time - from) })

def shiftPoints (from: Float) (to: Float) (points: List Point): List Point :=
  if from == to then points else points.map (point => { point | time = to + (point.time - from) })

-- `leg` moved to start at `at`, its points and notes with it.
def moveLeg (at: Float) (leg: Leg): Leg :=
  { leg | start = at, points = shiftPoints leg.start at leg.points, notes = leg.notes.map (notes => shiftNotes leg.start at notes) }

-- The route notes for the kept leg: the remote copy's if it has them, else
-- the local copy's, each moved to line up with the kept leg's start.
def notesFor (kept: Leg) (local: Leg) (remote: Leg): Option (List Note) := match remote.notes with
  | Some notes => Some (shiftNotes remote.start kept.start notes)
  | None => local.notes.map (notes => shiftNotes local.start kept.start notes)

-- A leg in both copies: the one with more track points (the remote one on a
-- tie), with the notes above.
def resolveLeg (local: Leg) (remote: Leg): Leg :=
  let kept := if Nat.leq (remote.points.length + 1) local.points.length then local else remote
  { kept | id = remote.id, notes = notesFor kept local remote }

def resolveAgainst (local: List Leg) (remote: Leg): Leg := match findLeg local remote.id with
  | Some leg => resolveLeg leg remote
  | None => remote

-- The legs laid end to end from `at`.
def layout (at: Float): List Leg → List Leg
  | [] => []
  | [leg, ..rest] => [moveLeg at leg, ..layout (at + leg.duration) rest]

-- The remote legs, each resolved against the local one with its id, then
-- the local legs the remote copy doesn't have, laid end to end from 0.
def mergeLegs (local: List Leg) (remote: List Leg): List Leg :=
  layout 0.0 (List.appendNewBy (remote.map (leg => resolveAgainst local leg)) local (leg => leg.id))

-- Positions

-- Where a time was, relative to the leg it was in: the leg's id, the offset
-- into it, and the leg's start and the time itself, so that a leg that
-- doesn't move gives back the time exactly. A time in no leg keeps its
-- absolute value.
type Position = { leg: Option Nat, offset: Float, legStart: Float, time: Float }

def locate (legs: List Leg) (t: Float): Position := match firstCovering legs t with
  | Some leg => { leg = Some leg.id, offset = t - leg.start, legStart = leg.start, time = t }
  | None => { leg = None, offset = t, legStart = 0.0, time = t }

def legOf (legs: List Leg) (pos: Position): Option Leg := match pos.leg with
  | Some id => findLeg legs id
  | None => None

-- The time in `leg` as it is now: the old time if the leg hasn't moved, else
-- the new start plus the offset.
def placeIn (leg: Leg) (pos: Position): Float := if leg.start == pos.legStart then pos.time else leg.start + pos.offset

-- `t`, or the nearer end of `lo` .. `hi` if it's outside.
def clamp (lo: Float) (hi: Float) (t: Float): Float := if Float.less t lo then lo else if Float.less hi t then hi else t

-- Where a stop or an album goes: in its leg, clamped to it; with no leg,
-- clamped to the whole trip.
def settle (legs: List Leg) (pos: Position): Float := match legOf legs pos with
  | Some leg => clamp leg.start leg.end (placeIn leg pos)
  | None => clamp 0.0 (lastEnd legs) pos.time

def Stop.startAt (stop: Stop) (t: Float): Stop := { stop | start = t }

def Pin.startAt (pin: Pin) (t: Float): Pin := { pin | start = t }

def Album.startAt (album: Album) (t: Float): Album := { album | start = t }

-- Stops

-- Whether the remote copy has a plan that isn't the local one.
def planReplaced: Option Itinerary → Option Itinerary → Bool
  | Some old, Some new => not (old.fileId == new.fileId)
  | None, Some new => True
  | _, None => False

def unlink (stop: Stop): Stop := match stop.kind with
  | Planned _ => { stop | kind = Free }
  | Free => stop

-- The local stops, then the remote stops the local copy doesn't have, each
-- placed from where it was in its own copy.
def mergeStops (local: Trip) (remote: Trip) (legs: List Leg): List Stop :=
  let replaced := planReplaced local.itinerary remote.itinerary
  let fromLocal := local.stops.map (stop => ((if replaced then unlink stop else stop), locate local.legs stop.start))
  let fromRemote := remote.stops.map (stop => (stop, locate remote.legs stop.start))
  (List.appendNewBy fromLocal fromRemote (entry => entry.fst.id)).map (entry => entry.fst.startAt (settle legs entry.snd))

-- Pins

-- Whether the first leg covering the pin's start is the leg `id`, and the
-- pin lies wholly inside it.
def keepsIn (legs: List Leg) (id: Nat) (pin: Pin): Bool := match firstCovering legs pin.start with
  | Some leg => leg.id == id ∧ pin.fitsIn leg
  | None => False

-- The pin moved with its leg, if it still lies wholly inside it.
def placePin (legs: List Leg) (pin: Pin) (pos: Position): Option Pin := match legOf legs pos with
  | Some leg =>
    let moved := pin.startAt (placeIn leg pos)
    if keepsIn legs leg.id moved then Some moved else None
  | None => None

def byStart (a: Pin) (b: Pin): Bool := Float.leq a.start b.start

-- The remote pins, then the local ones the remote copy doesn't have, those
-- that still fit, sorted by start.
def mergePins (local: Trip) (remote: Trip) (legs: List Leg): List Pin :=
  let fromRemote := remote.pins.map (pin => (pin, locate remote.legs pin.start))
  let fromLocal := local.pins.map (pin => (pin, locate local.legs pin.start))
  let placed := (List.appendNewBy fromRemote fromLocal (entry => entry.fst.id)).filterMap (entry => placePin legs entry.fst entry.snd)
  List.sortWith placed byStart

-- Albums

def holds (album: Album) (id: Nat): Bool := id ∈ album.photos.map Photo.id

-- The first album holding the photo.
def holder (albums: List Album) (id: Nat): Option Nat := (albums.find (album => holds album id)).map (album => album.id)

def stillHolds (albums: List Album) (id: Nat): Option Nat → Bool
  | Some albumId =>
    match albums.find (album => album.id == albumId) with
      | Some album => holds album id
      | None => False
  | None => False

-- The album a photo stays in: the one that held it in the local copy, if
-- the merged albums still have it there; else the remote copy's; else the
-- first merged album holding it.
def owner (local: List Album) (remote: List Album) (merged: List Album) (id: Nat): Option Nat :=
  if stillHolds merged id (holder local id) then holder local id
  else if stillHolds merged id (holder remote id) then holder remote id
  else holder merged id

def keepOwned (own: Nat → Option Nat) (album: Album): Album :=
  { album | photos = album.photos.filter (photo => own photo.id == Some album.id) }

-- An album in both copies: the remote copy's photos, then the local ones
-- with new ids.
def withPhotosOf (remote: List Album) (album: Album): Album := match remote.find (other => other.id == album.id) with
  | Some other => { album | photos = List.appendNewBy other.photos album.photos Photo.id }
  | None => album

-- The local albums (with the remote photos), then the remote albums the
-- local copy doesn't have, each placed from where it was in its own copy,
-- and each photo kept in one album.
def mergeAlbums (local: Trip) (remote: Trip) (legs: List Leg): List Album :=
  let fromLocal := local.albums.map (album => (withPhotosOf remote.albums album, locate local.legs album.start))
  let fromRemote := remote.albums.map (album => (album, locate remote.legs album.start))
  let entries := List.appendNewBy fromLocal fromRemote (entry => entry.fst.id)
  let own := owner local.albums remote.albums (entries.map (entry => entry.fst))
  entries.map (entry => keepOwned own (entry.fst.startAt (settle legs entry.snd)))

-- The plan, the summary and the name

-- The same plan merges its places (the remote ones, then the new local
-- ones); otherwise the remote plan wins, if there is one.
def mergeItinerary: Option Itinerary → Option Itinerary → Option Itinerary
  | Some old, Some new =>
    if old.fileId == new.fileId then Some { new | places = List.appendNewBy new.places old.places (place => place.id) }
    else Some new
  | None, Some new => Some new
  | old, None => old

-- A summary is kept only with the legs it was made from.
def mergeSummary (local: Trip) (remote: Trip) (legs: List Leg): Option Summary :=
  if remote.legs == legs then remote.summary else if local.legs == legs then local.summary else None

def isBlank (text: Text): Bool := Text.isEmpty (Text.trim text)

def merge (local: Trip) (remote: Trip): Trip :=
  let legs := mergeLegs local.legs remote.legs
  {
    name = if isBlank remote.name then local.name else remote.name,
    settings = remote.settings,
    legs = legs,
    stops = mergeStops local remote legs,
    pins = mergePins local remote legs,
    albums = mergeAlbums local remote legs,
    itinerary = mergeItinerary local.itinerary remote.itinerary,
    summary = mergeSummary local remote legs
  }
