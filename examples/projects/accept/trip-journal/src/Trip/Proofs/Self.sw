-- A well-formed trip merged with itself is unchanged, to the bit: no time
-- is rounded, because every leg stays where it is and every position gives
-- back its old time.
namespace Trip.Proofs

import Std (Float, List, Nat, Option, Eq, Void, Bool, Decidable, DecEq, Exists)
import Trip.Model (..)
import Trip.Merge (..)

-- Rebuilding a record from its own fields gives it back (there is no eta
-- rule for records, so these are proved by taking the record apart).

def Album.rebuilt (album: Album): Album := { id = album.id, start = album.start, label = album.label, photos = album.photos }

theorem albumEta ∀ (album: Album): album.rebuilt = album := match album with
  | { id, start, label, photos } => rfl

theorem stopStartAtSame ∀ (stop: Stop): stop.startAt stop.start = stop := match stop with
  | { id, start, name, kind } => rfl

theorem albumStartAtSame ∀ (album: Album): album.startAt album.start = album := match album with
  | { id, start, label, photos } => rfl

def rebuildTrip (trip: Trip): Trip := {
  name = trip.name,
  settings = trip.settings,
  legs = trip.legs,
  stops = trip.stops,
  pins = trip.pins,
  albums = trip.albums,
  itinerary = trip.itinerary,
  summary = trip.summary
}

theorem tripEta ∀ (trip: Trip): rebuildTrip trip = trip := match trip with
  | { name, settings, legs, stops, pins, albums, itinerary, summary } => rfl

-- Legs

theorem resolveSelf ∀ (leg: Leg): resolveLeg leg leg = leg := match leg with
  | { id, start, duration, points, notes = None } =>
    match c: Nat.leq (List.length points + 1) (List.length points) with
      | True => rfl
      | False => rfl
  | { id, start, duration, points, notes = Some notes } =>
    match c: Nat.leq (List.length points + 1) (List.length points) with
      | True => rewrite DecEq.refl start in rfl
      | False => rewrite DecEq.refl start in rfl

theorem resolveAgainstSelf ∀ (legs: List Leg) (ids: List.Distinct (List.map legs (leg => leg.id))) (leg: Leg) (m: leg ∈ legs):
    resolveAgainst legs leg = leg :=
  rewrite List.findKeyDistinct (l => l.id) legs ids leg m in resolveSelf leg

theorem resolvedSelf ∀ (legs: List Leg) (ids: List.Distinct (List.map legs (leg => leg.id))): resolvedLegs legs legs = legs :=
  Eq.trans (List.mapCongMem legs (leg => resolveAgainst legs leg) (leg => leg) (leg m => resolveAgainstSelf legs ids leg m)) (List.mapId legs)

theorem mergeLegsSelf ∀ (legs: List Leg) (ids: List.Distinct (List.map legs (leg => leg.id))) (c: ContiguousFrom 0.0 legs):
    mergeLegs legs legs = legs :=
  calc mergeLegs legs legs
    _ = layout 0.0 (List.appendNewBy (resolvedLegs legs legs) legs (leg => leg.id))
    _ = layout 0.0 (List.appendNewBy legs legs (leg => leg.id)) := rewrite resolvedSelf legs ids in rfl
    _ = layout 0.0 legs := rewrite List.appendNewBySelf legs (leg => leg.id) in rfl
    _ = legs := layoutSame 0.0 legs c

-- Stops

theorem planReplacedSelf ∀ (plan: Option Itinerary): planReplaced plan plan = False := match plan with
  | Some plan => rewrite DecEq.refl plan.fileId in rfl
  | None => rfl

theorem mergeStopsSelf ∀ (trip: Trip) (ids: List.Distinct (List.map trip.legs (leg => leg.id)))
    (w: List.All (stop => within trip.legs stop.start = True) trip.stops): mergeStops trip trip trip.legs = trip.stops :=
  let entries := trip.stops.map (stop => (stop, locate trip.legs stop.start))
  calc mergeStops trip trip trip.legs
    _ = (List.appendNewBy entries entries (entry => entry.fst.id)).map (entry => entry.fst.startAt (settle trip.legs entry.snd)) :=
      rewrite planReplacedSelf trip.itinerary in rfl
    _ = entries.map (entry => entry.fst.startAt (settle trip.legs entry.snd)) :=
      rewrite List.appendNewBySelf entries (entry => entry.fst.id) in rfl
    _ = trip.stops.map (stop => stop.startAt (settle trip.legs (locate trip.legs stop.start))) :=
      List.mapMap trip.stops (entry => entry.fst.startAt (settle trip.legs entry.snd)) (stop => (stop, locate trip.legs stop.start))
    _ = trip.stops.map (stop => stop) :=
      List.mapCongMem trip.stops (stop => stop.startAt (settle trip.legs (locate trip.legs stop.start))) (stop => stop) (stop m =>
        rewrite settleSelf trip.legs ids stop.start (List.memOfAll (s => within trip.legs s.start = True) trip.stops w stop m) in
        stopStartAtSame stop)
    _ = trip.stops := List.mapId trip.stops

-- Pins

theorem mergePinsSelf ∀ (trip: Trip) (ids: List.Distinct (List.map trip.legs (leg => leg.id)))
    (fit: List.All (pin => pinFits trip.legs pin = True) trip.pins) (sorted: List.Sorted (a b => Float.leq a.start b.start) trip.pins):
    mergePins trip trip trip.legs = trip.pins :=
  let entries := trip.pins.map (pin => (pin, locate trip.legs pin.start))
  calc mergePins trip trip trip.legs
    _ = List.sortWith ((List.appendNewBy entries entries (entry => entry.fst.id)).filterMap (entry => placePin trip.legs entry.fst entry.snd)) byStart
    _ = List.sortWith (entries.filterMap (entry => placePin trip.legs entry.fst entry.snd)) byStart :=
      rewrite List.appendNewBySelf entries (entry => entry.fst.id) in rfl
    _ = List.sortWith trip.pins byStart :=
      rewrite List.filterMapMapSelf (pin => (pin, locate trip.legs pin.start)) (entry => placePin trip.legs entry.fst entry.snd) trip.pins
        (pin m => placePinSelf trip.legs ids pin (List.memOfAll (p => pinFits trip.legs p = True) trip.pins fit pin m)) in
      rfl
    _ = trip.pins := List.sortWithOfSorted byStart byStartTrans trip.pins sorted

-- Albums

theorem holdsOf ∀ (album: Album) (photo: Photo) (m: photo ∈ album.photos): holds album photo.id = True :=
  (List.decMem photo.id (album.photos.map Photo.id)).complete (List.memMap album.photos photo m Photo.id)

-- With photo ids distinct across the albums, the first album holding a
-- photo is the album it is in.
theorem holderOf: ∀ (albums: List Album) => List.Distinct (photoIds albums) → ∀ (album: Album) => album ∈ albums → ∀ (photo: Photo)
    => photo ∈ album.photos → holder albums photo.id = Some album.id
  | [], d, album, m, photo, p => Void.exfalso m
  | [first, ..rest], d, album, Inl e, photo, p => rewrite e, holdsOf album photo p in rfl
  | [first, ..rest], d, album, Inr m, photo, p =>
    let inRest: photo.id ∈ photoIds rest :=
      List.memFlatMapIntro (a => a.photos.map Photo.id) album photo.id rest m (List.memMap album.photos photo p Photo.id)
    let notHere: holds first photo.id = False :=
      Decidable.toBoolOfNot (List.decMem photo.id (first.photos.map Photo.id))
        (h => List.distinctAppendApart (first.photos.map Photo.id) (photoIds rest) d photo.id h inRest)
    rewrite notHere in holderOf rest (List.distinctAppendRight (first.photos.map Photo.id) (photoIds rest) d) album m photo p

theorem ownerSelf ∀ (albums: List Album) (ids: List.Distinct (List.map albums (album => album.id))) (pd: List.Distinct (photoIds albums))
    (album: Album) (m: album ∈ albums) (photo: Photo) (p: photo ∈ album.photos): owner albums albums albums photo.id = Some album.id :=
  rewrite holderOf albums pd album m photo p, List.findKeyDistinct (a => a.id) albums ids album m, holdsOf album photo p in rfl

theorem keepOwnedSelf ∀ (own: Nat → Option Nat) (album: Album) (h: ∀ (photo: Photo) => photo ∈ album.photos → own photo.id = Some album.id):
    keepOwned own album = album :=
  rewrite List.filterAll (p => own p.id == Some album.id) album.photos (photo m => rewrite h photo m in DecEq.refl (Some album.id)) in
  albumEta album

theorem withPhotosOfSelf ∀ (albums: List Album) (ids: List.Distinct (List.map albums (album => album.id))) (album: Album) (m: album ∈ albums):
    withPhotosOf albums album = album :=
  rewrite List.findKeyDistinct (a => a.id) albums ids album m, List.appendNewBySelf album.photos Photo.id in albumEta album

theorem albumEntriesSelf ∀ (trip: Trip) (ids: List.Distinct (List.map trip.albums (album => album.id))):
    albumEntries trip trip = trip.albums.map (album => (album, locate trip.legs album.start)) :=
  let entries := trip.albums.map (album => (album, locate trip.legs album.start))
  calc albumEntries trip trip
    _ = List.appendNewBy (trip.albums.map (album => (withPhotosOf trip.albums album, locate trip.legs album.start))) entries (entry => entry.fst.id)
    _ = List.appendNewBy entries entries (entry => entry.fst.id) :=
      rewrite List.mapCongMem trip.albums (album => (withPhotosOf trip.albums album, locate trip.legs album.start))
        (album => (album, locate trip.legs album.start)) (album m => rewrite withPhotosOfSelf trip.albums ids album m in rfl) in
      rfl
    _ = entries := List.appendNewBySelf entries (entry => entry.fst.id)

theorem combinedSelf ∀ (trip: Trip) (ids: List.Distinct (List.map trip.albums (album => album.id))):
    List.map (albumEntries trip trip) (entry => entry.fst) = trip.albums :=
  rewrite albumEntriesSelf trip ids,
    List.mapMap trip.albums (entry => entry.fst) (album => (album, locate trip.legs album.start)) in
  List.mapId trip.albums

theorem mergeAlbumsSelf ∀ (trip: Trip) (lids: List.Distinct (List.map trip.legs (leg => leg.id)))
    (ids: List.Distinct (List.map trip.albums (album => album.id))) (pd: List.Distinct (photoIds trip.albums))
    (w: List.All (album => within trip.legs album.start = True) trip.albums): mergeAlbums trip trip trip.legs = trip.albums :=
  calc mergeAlbums trip trip trip.legs
    _ = (settledAlbums trip trip trip.legs).map (album => keepOwned (ownerIn trip trip) album) := mergeAlbumsIs trip trip trip.legs
    _ = (trip.albums.map (album => album.startAt (settle trip.legs (locate trip.legs album.start)))).map (album => keepOwned (ownerIn trip trip) album) :=
      rewrite albumEntriesSelf trip ids,
        List.mapMap trip.albums (entry => entry.fst.startAt (settle trip.legs entry.snd)) (album => (album, locate trip.legs album.start)) in
      rfl
    _ = trip.albums.map (album => keepOwned (ownerIn trip trip) album) :=
      rewrite List.mapCongMem trip.albums (album => album.startAt (settle trip.legs (locate trip.legs album.start))) (album => album) (album m =>
        rewrite settleSelf trip.legs lids album.start (List.memOfAll (a => within trip.legs a.start = True) trip.albums w album m) in
        albumStartAtSame album), List.mapId trip.albums in
      rfl
    _ = trip.albums.map (album => album) :=
      List.mapCongMem trip.albums (album => keepOwned (ownerIn trip trip) album) (album => album) (album m =>
        keepOwnedSelf (ownerIn trip trip) album (photo p => rewrite combinedSelf trip ids in ownerSelf trip.albums ids pd album m photo p))
    _ = trip.albums := List.mapId trip.albums

-- The plan and the summary

theorem mergeItinerarySelf ∀ (plan: Option Itinerary): mergeItinerary plan plan = plan := match plan with
  | None => rfl
  | Some { fileId, places } => rewrite DecEq.refl fileId, List.appendNewBySelf places (place => place.id) in rfl

theorem mergeSummarySelf ∀ (trip: Trip): mergeSummary trip trip trip.legs = trip.summary := rewrite DecEq.refl trip.legs in rfl

-- The theorem

-- A well-formed trip merged with itself is unchanged.
theorem mergeSelf ∀ (trip: Trip) (wf: WellFormed trip): merge trip trip = trip :=
  calc merge trip trip
    _ = {
      name = if isBlank trip.name then trip.name else trip.name,
      settings = trip.settings,
      legs = mergeLegs trip.legs trip.legs,
      stops = mergeStops trip trip (mergeLegs trip.legs trip.legs),
      pins = mergePins trip trip (mergeLegs trip.legs trip.legs),
      albums = mergeAlbums trip trip (mergeLegs trip.legs trip.legs),
      itinerary = mergeItinerary trip.itinerary trip.itinerary,
      summary = mergeSummary trip trip (mergeLegs trip.legs trip.legs)
    }
    _ = rebuildTrip trip :=
      rewrite mergeLegsSelf trip.legs wf.legIds wf.contiguous, ifSame (isBlank trip.name) trip.name,
        mergeStopsSelf trip wf.legIds wf.stopsWithin, mergePinsSelf trip wf.legIds wf.pinsFit wf.pinsSorted,
        mergeAlbumsSelf trip wf.legIds wf.albumIds wf.photoIdsDistinct wf.albumsWithin, mergeItinerarySelf trip.itinerary,
        mergeSummarySelf trip in
      rfl
    _ = trip := tripEta trip
