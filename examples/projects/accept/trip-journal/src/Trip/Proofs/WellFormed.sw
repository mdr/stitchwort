-- The merge of two well-formed trips is well-formed.
namespace Trip.Proofs

import Std (Float, List, Option, Eq, Void, Bool, Decidable, DecEq, Exists)
import Trip.Model (..)
import Trip.Merge (..)

-- Stops

theorem unlinkId (stop: Stop): (unlink stop).id = stop.id := match e: stop.kind with
  | Planned index => rfl
  | Free => rfl

theorem localStopId (replaced: Bool) (stop: Stop): (if replaced then unlink stop else stop).id = stop.id :=
  match replaced with
    | True => unlinkId stop
    | False => rfl

def stopEntries (local: Trip) (remote: Trip): List (Stop, Position) :=
  List.appendNewBy
    (local.stops.map (stop => ((if planReplaced local.itinerary remote.itinerary then unlink stop else stop), locate local.legs stop.start)))
    (remote.stops.map (stop => (stop, locate remote.legs stop.start)))
    (entry => entry.fst.id)

theorem mergeStopsIs (local: Trip) (remote: Trip) (legs: List Leg):
    mergeStops local remote legs = (stopEntries local remote).map (entry => entry.fst.startAt (settle legs entry.snd)) :=
  rfl

theorem stopIdsOf (local: Trip) (remote: Trip) (legs: List Leg):
    List.map (mergeStops local remote legs) (stop => stop.id) = List.map (stopEntries local remote) (entry => entry.fst.id) :=
  List.mapMap (stopEntries local remote) (stop => stop.id) (entry => entry.fst.startAt (settle legs entry.snd))

theorem mergeStopIds (local: Trip) (remote: Trip) (legs: List Leg) (dl: List.Distinct (List.map local.stops (stop => stop.id)))
    (dr: List.Distinct (List.map remote.stops (stop => stop.id))): List.Distinct (List.map (mergeStops local remote legs) (stop => stop.id)) :=
  let replaced := planReplaced local.itinerary remote.itinerary
  rewrite stopIdsOf local remote legs in
  List.distinctKeysAppendNewBy
    (local.stops.map (stop => ((if replaced then unlink stop else stop), locate local.legs stop.start)))
    (remote.stops.map (stop => (stop, locate remote.legs stop.start)))
    (entry => entry.fst.id)
    (rewrite List.mapMap local.stops (entry => entry.fst.id) (stop => ((if replaced then unlink stop else stop), locate local.legs stop.start)),
      List.mapCong local.stops (stop => (if replaced then unlink stop else stop).id) (stop => stop.id) (stop => localStopId replaced stop) in dl)
    (rewrite List.mapMap remote.stops (entry => entry.fst.id) (stop => (stop, locate remote.legs stop.start)) in dr)

theorem mergeStopsWithin (local: Trip) (remote: Trip) (legs: List Leg) (c: ContiguousFrom 0.0 legs) (oks: List.All LegOk legs):
    List.All (stop => within legs stop.start = True) (mergeStops local remote legs) :=
  List.allOfMem (stop => within legs stop.start = True) (mergeStops local remote legs) (stop m =>
    List.anyElim (entry => entry.fst.startAt (settle legs entry.snd) = stop) (within legs stop.start = True) (stopEntries local remote)
      (List.memMapAny (stopEntries local remote) (entry => entry.fst.startAt (settle legs entry.snd)) stop m)
      (entry inEntries e => rewrite <- e in settleWithin legs c oks entry.snd))

-- Pins

def pinEntries (local: Trip) (remote: Trip): List (Pin, Position) :=
  List.appendNewBy (remote.pins.map (pin => (pin, locate remote.legs pin.start))) (local.pins.map (pin => (pin, locate local.legs pin.start)))
    (entry => entry.fst.id)

def placedPins (local: Trip) (remote: Trip) (legs: List Leg): List Pin :=
  (pinEntries local remote).filterMap (entry => placePin legs entry.fst entry.snd)

theorem mergePinsIs (local: Trip) (remote: Trip) (legs: List Leg): mergePins local remote legs = List.sortWith (placedPins local remote legs) byStart :=
  rfl

theorem byStartTotal (a: Pin) (b: Pin) (h: byStart a b = False): byStart b a = True := Float.leTotal a.start b.start h

theorem byStartTrans (a: Pin) (b: Pin) (c: Pin) (h1: byStart a b = True) (h2: byStart b c = True): byStart a c = True :=
  floatLeTrans a.start b.start c.start h1 h2

theorem mergePinsSorted (local: Trip) (remote: Trip) (legs: List Leg):
    List.Sorted (a b => Float.leq a.start b.start) (mergePins local remote legs) :=
  List.sortWithSorted byStart byStartTotal (placedPins local remote legs)

theorem mergePinIds (local: Trip) (remote: Trip) (legs: List Leg) (dl: List.Distinct (List.map local.pins (pin => pin.id)))
    (dr: List.Distinct (List.map remote.pins (pin => pin.id))): List.Distinct (List.map (mergePins local remote legs) (pin => pin.id)) :=
  List.distinctMapPerm (mergePins local remote legs) (pin => pin.id) (placedPins local remote legs)
    (List.sortWithPerm (placedPins local remote legs) byStart)
    (List.distinctMapFilterMap (entry => placePin legs entry.fst entry.snd) (entry => entry.fst.id) (pin => pin.id)
      (entry pin h => placePinId legs entry.fst entry.snd pin h)
      (pinEntries local remote)
      (List.distinctKeysAppendNewBy (remote.pins.map (pin => (pin, locate remote.legs pin.start)))
        (local.pins.map (pin => (pin, locate local.legs pin.start))) (entry => entry.fst.id)
        (rewrite List.mapMap remote.pins (entry => entry.fst.id) (pin => (pin, locate remote.legs pin.start)) in dr)
        (rewrite List.mapMap local.pins (entry => entry.fst.id) (pin => (pin, locate local.legs pin.start)) in dl)))

theorem mergePinsFit (local: Trip) (remote: Trip) (legs: List Leg): List.All (pin => pinFits legs pin = True) (mergePins local remote legs) :=
  List.allOfMem (pin => pinFits legs pin = True) (mergePins local remote legs) (pin m =>
    List.anyElim (entry => placePin legs entry.fst entry.snd = Some pin) (pinFits legs pin = True) (pinEntries local remote)
      (List.memFilterMapElim (entry => placePin legs entry.fst entry.snd) pin (pinEntries local remote)
        (List.memPerm (mergePins local remote legs) (placedPins local remote legs) (List.sortWithPerm (placedPins local remote legs) byStart) pin m))
      (entry inEntries h => placePinFits legs entry.fst entry.snd pin h))

-- Albums

def AlbumOk (album: Album): Prop := List.Distinct (album.photos.map Photo.id)

-- Each album of a trip whose photo ids are distinct has distinct photo ids.
theorem albumsOk: ∀ (albums: List Album) => List.Distinct (photoIds albums) → List.All AlbumOk albums
  | [], d => Trivial
  | [album, ..rest], d =>
    Both (List.distinctAppendLeft (album.photos.map Photo.id) (photoIds rest) d)
      (albumsOk rest (List.distinctAppendRight (album.photos.map Photo.id) (photoIds rest) d))

theorem withPhotosOfOk (remote: List Album) (okr: List.All AlbumOk remote) (album: Album) (ok: AlbumOk album):
    AlbumOk (withPhotosOf remote album) := match e: remote.find (other => other.id == album.id) with
      | Some other =>
        List.distinctKeysAppendNewBy other.photos album.photos Photo.id
          (List.memOfAll AlbumOk remote okr other (And.right (List.findSome remote (o => o.id == album.id) other e))) ok
      | None => ok

theorem withPhotosOfId (remote: List Album) (album: Album): (withPhotosOf remote album).id = album.id :=
  match e: remote.find (other => other.id == album.id) with
    | Some other => rfl
    | None => rfl

def albumEntries (local: Trip) (remote: Trip): List (Album, Position) :=
  List.appendNewBy
    (local.albums.map (album => (withPhotosOf remote.albums album, locate local.legs album.start)))
    (remote.albums.map (album => (album, locate remote.legs album.start)))
    (entry => entry.fst.id)

def ownerIn (local: Trip) (remote: Trip): Nat → Option Nat :=
  owner local.albums remote.albums ((albumEntries local remote).map (entry => entry.fst))

def settledAlbums (local: Trip) (remote: Trip) (legs: List Leg): List Album :=
  (albumEntries local remote).map (entry => entry.fst.startAt (settle legs entry.snd))

theorem mergeAlbumsIs (local: Trip) (remote: Trip) (legs: List Leg):
    mergeAlbums local remote legs = (settledAlbums local remote legs).map (album => keepOwned (ownerIn local remote) album) :=
  Eq.sym (List.mapMap (albumEntries local remote) (album => keepOwned (ownerIn local remote) album) (entry => entry.fst.startAt (settle legs entry.snd)))

theorem albumEntryIds (local: Trip) (remote: Trip) (dl: List.Distinct (List.map local.albums (album => album.id)))
    (dr: List.Distinct (List.map remote.albums (album => album.id))): List.Distinct (List.map (albumEntries local remote) (entry => entry.fst.id)) :=
  List.distinctKeysAppendNewBy
    (local.albums.map (album => (withPhotosOf remote.albums album, locate local.legs album.start)))
    (remote.albums.map (album => (album, locate remote.legs album.start)))
    (entry => entry.fst.id)
    (rewrite List.mapMap local.albums (entry => entry.fst.id) (album => (withPhotosOf remote.albums album, locate local.legs album.start)),
      List.mapCong local.albums (album => (withPhotosOf remote.albums album).id) (album => album.id) (album => withPhotosOfId remote.albums album) in dl)
    (rewrite List.mapMap remote.albums (entry => entry.fst.id) (album => (album, locate remote.legs album.start)) in dr)

theorem mergeAlbumIds (local: Trip) (remote: Trip) (legs: List Leg) (dl: List.Distinct (List.map local.albums (album => album.id)))
    (dr: List.Distinct (List.map remote.albums (album => album.id))): List.Distinct (List.map (mergeAlbums local remote legs) (album => album.id)) :=
  rewrite List.mapMap (albumEntries local remote) (album => album.id)
    (entry => keepOwned (ownerIn local remote) (entry.fst.startAt (settle legs entry.snd))) in
  albumEntryIds local remote dl dr

theorem settledAlbumsIds (local: Trip) (remote: Trip) (legs: List Leg) (dl: List.Distinct (List.map local.albums (album => album.id)))
    (dr: List.Distinct (List.map remote.albums (album => album.id))): List.Distinct (List.map (settledAlbums local remote legs) (album => album.id)) :=
  rewrite List.mapMap (albumEntries local remote) (album => album.id) (entry => entry.fst.startAt (settle legs entry.snd)) in
  albumEntryIds local remote dl dr

theorem settledAlbumsOk (local: Trip) (remote: Trip) (legs: List Leg) (okl: List.All AlbumOk local.albums) (okr: List.All AlbumOk remote.albums):
    List.All AlbumOk (settledAlbums local remote legs) :=
  List.allOfMem AlbumOk (settledAlbums local remote legs) (album m =>
    List.anyElim (entry => entry.fst.startAt (settle legs entry.snd) = album) (AlbumOk album) (albumEntries local remote)
      (List.memMapAny (albumEntries local remote) (entry => entry.fst.startAt (settle legs entry.snd)) album m)
      (entry inEntries e =>
        rewrite <- e in
        match (List.memAppendNewBy entry
            (local.albums.map (a => (withPhotosOf remote.albums a, locate local.legs a.start)))
            (remote.albums.map (a => (a, locate remote.legs a.start))) (entry => entry.fst.id)).forward inEntries with
          | Inl fromLocal =>
            List.anyElim (a => (withPhotosOf remote.albums a, locate local.legs a.start) = entry) (AlbumOk entry.fst) local.albums
              (List.memMapAny local.albums (a => (withPhotosOf remote.albums a, locate local.legs a.start)) entry fromLocal)
              (a inLocal ea => rewrite <- ea in withPhotosOfOk remote.albums okr a (List.memOfAll AlbumOk local.albums okl a inLocal))
          | Inr (Both fromRemote fresh) =>
            List.anyElim (a => (a, locate remote.legs a.start) = entry) (AlbumOk entry.fst) remote.albums
              (List.memMapAny remote.albums (a => (a, locate remote.legs a.start)) entry fromRemote)
              (a inRemote ea => rewrite <- ea in List.memOfAll AlbumOk remote.albums okr a inRemote)))

-- A photo kept in an album is one its owner gives to that album.
theorem ownedOf (own: Nat → Option Nat) (album: Album) (x: Nat) (m: x ∈ List.map (keepOwned own album).photos Photo.id):
    own x = Some album.id :=
  Exists.elim (List.memMapElim Photo.id x (keepOwned own album).photos m) (photo both =>
    match List.memFilter album.photos (p => own p.id == Some album.id) (And.left both) with
      | Both inPhotos keep => rewrite <- And.right both in DecEq.sound keep)

theorem ownedIn (own: Nat → Option Nat): ∀ (albums: List Album) (x: Nat) => x ∈ photoIds (albums.map (album => keepOwned own album))
    → List.Any (album => own x = Some album.id) albums
  | [], x, m => m
  | [album, ..rest], x, m =>
    match List.memAppend x (List.map (keepOwned own album).photos Photo.id) (photoIds (rest.map (a => keepOwned own a))) m with
      | Inl here => Inl (ownedOf own album x here)
      | Inr there => Inr (ownedIn own rest x there)

-- Albums with distinct ids, each keeping only the photos its owner gives
-- it, have distinct photo ids.
theorem ownedDistinct (own: Nat → Option Nat): ∀ (albums: List Album) => List.Distinct (List.map albums (album => album.id))
    → List.All AlbumOk albums → List.Distinct (photoIds (albums.map (album => keepOwned own album)))
  | [], ids, oks => Trivial
  | [album, ..rest], Both out ids, Both ok oks =>
    List.distinctAppend (List.map (keepOwned own album).photos Photo.id) (photoIds (rest.map (a => keepOwned own a)))
      (List.distinctMapFilter album.photos Photo.id (p => own p.id == Some album.id) ok)
      (ownedDistinct own rest ids oks)
      (List.allOfMem (x => x ∉ photoIds (rest.map (a => keepOwned own a))) (List.map (keepOwned own album).photos Photo.id) (x here there =>
        List.anyElim (b => own x = Some b.id) Void rest (ownedIn own rest x there) (b inRest e =>
          out (rewrite Option.someInjective (Eq.trans (Eq.sym (ownedOf own album x here)) e) in
            List.memMap rest b inRest (a => a.id)))))

theorem mergePhotoIds (local: Trip) (remote: Trip) (legs: List Leg) (dl: List.Distinct (List.map local.albums (album => album.id)))
    (dr: List.Distinct (List.map remote.albums (album => album.id))) (pl: List.Distinct (photoIds local.albums))
    (pr: List.Distinct (photoIds remote.albums)): List.Distinct (photoIds (mergeAlbums local remote legs)) :=
  rewrite mergeAlbumsIs local remote legs in
  ownedDistinct (ownerIn local remote) (settledAlbums local remote legs) (settledAlbumsIds local remote legs dl dr)
    (settledAlbumsOk local remote legs (albumsOk local.albums pl) (albumsOk remote.albums pr))

theorem mergeAlbumsWithin (local: Trip) (remote: Trip) (legs: List Leg) (c: ContiguousFrom 0.0 legs) (oks: List.All LegOk legs):
    List.All (album => within legs album.start = True) (mergeAlbums local remote legs) :=
  List.allOfMem (album => within legs album.start = True) (mergeAlbums local remote legs) (album m =>
    List.anyElim (entry => keepOwned (ownerIn local remote) (entry.fst.startAt (settle legs entry.snd)) = album) (within legs album.start = True)
      (albumEntries local remote)
      (List.memMapAny (albumEntries local remote) (entry => keepOwned (ownerIn local remote) (entry.fst.startAt (settle legs entry.snd))) album m)
      (entry inEntries e => rewrite <- e in settleWithin legs c oks entry.snd))

-- The plan

theorem mergePlaceIds: ∀ (local remote: Option Itinerary) => PlaceIdsDistinct local → PlaceIdsDistinct remote
    → PlaceIdsDistinct (mergeItinerary local remote)
  | Some old, Some new, dl, dr =>
    match e: old.fileId == new.fileId with
      | True => List.distinctKeysAppendNewBy new.places old.places (place => place.id) dr dl
      | False => dr
  | None, Some new, dl, dr => dr
  | Some old, None, dl, dr => dl
  | None, None, dl, dr => dl

-- The theorem

-- If both copies are well-formed, so is their merge.
theorem mergeWellFormed (local: Trip) (remote: Trip) (wl: WellFormed local) (wr: WellFormed remote): WellFormed (merge local remote) :=
  let legs := mergeLegs local.legs remote.legs
  let c: ContiguousFrom 0.0 legs := mergeLegsContiguous local.legs remote.legs
  let oks: List.All LegOk legs := mergeLegsOk local.legs remote.legs wl.legsOk wr.legsOk
  {
    contiguous = c,
    legIds = mergeLegsIds local.legs remote.legs wl.legIds wr.legIds,
    legsOk = oks,
    pinIds = mergePinIds local remote legs wl.pinIds wr.pinIds,
    pinsFit = mergePinsFit local remote legs,
    pinsSorted = mergePinsSorted local remote legs,
    stopIds = mergeStopIds local remote legs wl.stopIds wr.stopIds,
    albumIds = mergeAlbumIds local remote legs wl.albumIds wr.albumIds,
    photoIdsDistinct = mergePhotoIds local remote legs wl.albumIds wr.albumIds wl.photoIdsDistinct wr.photoIdsDistinct,
    stopsWithin = mergeStopsWithin local remote legs c oks,
    albumsWithin = mergeAlbumsWithin local remote legs c oks,
    placeIds = mergePlaceIds local.itinerary remote.itinerary wl.placeIds wr.placeIds
  }
