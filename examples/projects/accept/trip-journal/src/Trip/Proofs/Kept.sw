-- Nothing important is lost by the merge.
namespace Trip.Proofs

import Std (Float, List, Option, Eq, Void, Bool, Decidable, DecEq)
import Trip.Model (..)
import Trip.Merge (..)

-- Every remote leg's id is in the merge.
theorem remoteLegsKept ∀ (local: Trip) (remote: Trip) (leg: Leg) (m: leg ∈ remote.legs):
    leg.id ∈ (merge local remote).legs.map (l => l.id) :=
  remoteLegKept local.legs remote.legs leg m

-- Every remote pin that still fits its leg, placed in the merged legs from
-- where it was in the remote copy, is kept.
theorem remotePinsKept ∀ (local: Trip) (remote: Trip) (pin: Pin) (m: pin ∈ remote.pins) (placed: Pin)
    (fits: placePin (merge local remote).legs pin (locate remote.legs pin.start) = Some placed): placed ∈ (merge local remote).pins :=
  let legs := mergeLegs local.legs remote.legs
  let entry := (pin, locate remote.legs pin.start)
  let inEntries: entry ∈ pinEntries local remote :=
    List.memAppendLeft entry (remote.pins.map (p => (p, locate remote.legs p.start)))
      (List.differenceBy (local.pins.map (p => (p, locate local.legs p.start))) (remote.pins.map (p => (p, locate remote.legs p.start))) (e => e.fst.id))
      (List.memMap remote.pins pin m (p => (p, locate remote.legs p.start)))
  List.memPerm (placedPins local remote legs) (mergePins local remote legs)
    (List.permSym (mergePins local remote legs) (placedPins local remote legs) (List.sortWithPerm (placedPins local remote legs) byStart)) placed
    (List.memFilterMapIntro (e => placePin legs e.fst e.snd) entry placed (pinEntries local remote) inEntries fits)

-- When the merged legs are the remote legs (the local copy changed no
-- leg), every pin of a well-formed remote copy is kept as it was.
theorem remotePinsKeptAsTheyWere ∀ (local: Trip) (remote: Trip) (wr: WellFormed remote) (same: (merge local remote).legs = remote.legs)
    (pin: Pin) (m: pin ∈ remote.pins): pin ∈ (merge local remote).pins :=
  remotePinsKept local remote pin m pin
    (rewrite same in placePinSelf remote.legs wr.legIds pin (List.memOfAll (p => pinFits remote.legs p = True) remote.pins wr.pinsFit pin m))

-- Every stop id and album id of either copy is in the merge.
theorem stopIdsKept ∀ (local: Trip) (remote: Trip) (id: Nat)
    (m: (id ∈ local.stops.map (stop => stop.id)) ∨ (id ∈ remote.stops.map (stop => stop.id))):
    id ∈ (merge local remote).stops.map (stop => stop.id) :=
  let legs := mergeLegs local.legs remote.legs
  let replaced := planReplaced local.itinerary remote.itinerary
  let fromLocal := local.stops.map (stop => ((if replaced then unlink stop else stop), locate local.legs stop.start))
  let fromRemote := remote.stops.map (stop => (stop, locate remote.legs stop.start))
  rewrite stopIdsOf local remote legs in
  match m with
    | Inl inLocal =>
      List.anyElim (stop => stop.id = id) (id ∈ List.map (stopEntries local remote) (entry => entry.fst.id)) local.stops
        (List.memMapAny local.stops (stop => stop.id) id inLocal)
        (stop inStops e =>
          rewrite <- e, <- localStopId replaced stop in
          List.keyMemAppendNewByLeft (entry => entry.fst.id) fromLocal fromRemote ((if replaced then unlink stop else stop), locate local.legs stop.start)
            (List.memMap local.stops stop inStops (s => ((if replaced then unlink s else s), locate local.legs s.start))))
    | Inr inRemote =>
      List.anyElim (stop => stop.id = id) (id ∈ List.map (stopEntries local remote) (entry => entry.fst.id)) remote.stops
        (List.memMapAny remote.stops (stop => stop.id) id inRemote)
        (stop inStops e =>
          rewrite <- e in
          List.keyMemAppendNewByRight (entry => entry.fst.id) fromLocal fromRemote (stop, locate remote.legs stop.start)
            (List.memMap remote.stops stop inStops (s => (s, locate remote.legs s.start))))

theorem albumIdsKept ∀ (local: Trip) (remote: Trip) (id: Nat)
    (m: (id ∈ local.albums.map (album => album.id)) ∨ (id ∈ remote.albums.map (album => album.id))):
    id ∈ (merge local remote).albums.map (album => album.id) :=
  let legs := mergeLegs local.legs remote.legs
  let fromLocal := local.albums.map (album => (withPhotosOf remote.albums album, locate local.legs album.start))
  let fromRemote := remote.albums.map (album => (album, locate remote.legs album.start))
  rewrite List.mapMap (albumEntries local remote) (album => album.id)
    (entry => keepOwned (ownerIn local remote) (entry.fst.startAt (settle legs entry.snd))) in
  match m with
    | Inl inLocal =>
      List.anyElim (album => album.id = id) (id ∈ List.map (albumEntries local remote) (entry => entry.fst.id)) local.albums
        (List.memMapAny local.albums (album => album.id) id inLocal)
        (album inAlbums e =>
          rewrite <- e, <- withPhotosOfId remote.albums album in
          List.keyMemAppendNewByLeft (entry => entry.fst.id) fromLocal fromRemote (withPhotosOf remote.albums album, locate local.legs album.start)
            (List.memMap local.albums album inAlbums (a => (withPhotosOf remote.albums a, locate local.legs a.start))))
    | Inr inRemote =>
      List.anyElim (album => album.id = id) (id ∈ List.map (albumEntries local remote) (entry => entry.fst.id)) remote.albums
        (List.memMapAny remote.albums (album => album.id) id inRemote)
        (album inAlbums e =>
          rewrite <- e in
          List.keyMemAppendNewByRight (entry => entry.fst.id) fromLocal fromRemote (album, locate remote.legs album.start)
            (List.memMap remote.albums album inAlbums (a => (a, locate remote.legs a.start))))

-- The summary, if there is one, is a copy's summary whose legs are exactly
-- the merged legs.
theorem summaryMatches ∀ (local: Trip) (remote: Trip) (summary: Summary) (h: (merge local remote).summary = Some summary):
    ((remote.summary = Some summary) ∧ (remote.legs = (merge local remote).legs)) ∨ ((local.summary = Some summary) ∧ (local.legs = (merge local remote).legs)) :=
  let legs := mergeLegs local.legs remote.legs
  match c: remote.legs == legs with
    | True => Inl (Both h (DecEq.sound c))
    | False =>
      match d: local.legs == legs with
        | True => Inr (Both h (DecEq.sound d))
        | False => Void.exfalso (Option.noneNotSome summary h)

-- So if each copy's summary was made from its legs, the merged one is made
-- from the merged legs.
def SummaryFresh (trip: Trip): Prop := ∀ (summary: Summary) => trip.summary = Some summary → summary = summarize trip.legs

theorem mergeSummaryFresh ∀ (local: Trip) (remote: Trip) (fl: SummaryFresh local) (fr: SummaryFresh remote): SummaryFresh (merge local remote) :=
  summary h =>
    match summaryMatches local remote summary h with
      | Inl (Both s e) => rewrite <- e in fr summary s
      | Inr (Both s e) => rewrite <- e in fl summary s
