-- No photo is lost: every photo id of either copy is in a merged album
-- (and, by `mergeWellFormed`, in only one).
namespace Trip.Proofs

import Std (Float, List, Option, Eq, Void, Bool, Decidable, DecEq, Exists)
import Trip.Model (..)
import Trip.Merge (..)

theorem holdsMem (album: Album) (id: Nat) (h: holds album id = True): id ∈ album.photos.map Photo.id :=
  (List.decMem id (album.photos.map Photo.id)).sound h

-- Where `stillHolds` says yes, an album with that id holds the photo.
theorem stillHoldsGives (albums: List Album) (id: Nat):
    ∀ (o: Option Nat) => stillHolds albums id o = True → List.Any (album => (o = Some album.id) ∧ (holds album id = True)) albums
  | Some albumId, h =>
    match e: albums.find (album => album.id == albumId) with
      | Some album =>
        match List.findSome albums (a => a.id == albumId) album e with
          | Both same inAlbums =>
            List.anyIntro (a => (Some albumId = Some a.id) ∧ (holds a id = True)) album albums inAlbums
              (Both (rewrite DecEq.sound same in rfl) h)
      | None => cases
  | None, h => cases

-- Every photo of the merged albums has an owner among them that holds it.
theorem ownerGives (local: List Album) (remote: List Album) (merged: List Album) (id: Nat) (m: id ∈ photoIds merged):
    List.Any (album => (owner local remote merged id = Some album.id) ∧ (holds album id = True)) merged :=
  match c: stillHolds merged id (holder local id) with
    | True => stillHoldsGives merged id (holder local id) c
    | False =>
      match d: stillHolds merged id (holder remote id) with
        | True => stillHoldsGives merged id (holder remote id) d
        | False =>
          match f: merged.find (album => holds album id) with
            | Some album =>
              match List.findSome merged (a => holds a id) album f with
                | Both h inMerged => List.anyIntro (a => (Some album.id = Some a.id) ∧ (holds a id = True)) album merged inMerged (Both rfl h)
            | None =>
              List.anyElim (a => id ∈ a.photos.map Photo.id) (List.Any (a => (None = Some a.id) ∧ (holds a id = True)) merged) merged
                (List.memFlatMapElim (a => a.photos.map Photo.id) id merged m)
                (a inMerged inA =>
                  Void.exfalso (List.findNoneNotMem merged (b => holds b id) a
                    ((List.decMem id (a.photos.map Photo.id)).complete inA) inMerged f))

-- A photo of an album that owns it is kept there.
theorem keptWhereOwned (own: Nat → Option Nat) (album: Album) (id: Nat) (o: own id = Some album.id) (h: holds album id = True):
    id ∈ (keepOwned own album).photos.map Photo.id :=
  Exists.elim (List.memMapElim Photo.id id album.photos (holdsMem album id h)) (photo both =>
    match both with
      | Both inPhotos e =>
        rewrite <- e in
        List.memMap (keepOwned own album).photos photo
          (List.memFilterIntro album.photos (p => own p.id == Some album.id) inPhotos
            (rewrite e, o in DecEq.refl (Some album.id)))
          Photo.id)

theorem combinedIs (local: Trip) (remote: Trip): ownerIn local remote = owner local.albums remote.albums ((albumEntries local remote).map (entry => entry.fst)) :=
  rfl

-- A photo of the albums before ownership is decided is in a merged album.
theorem keptFromCombined (local: Trip) (remote: Trip) (legs: List Leg) (id: Nat)
    (m: id ∈ photoIds ((albumEntries local remote).map (entry => entry.fst))): id ∈ photoIds (mergeAlbums local remote legs) :=
  let combined := (albumEntries local remote).map (entry => entry.fst)
  let own := ownerIn local remote
  List.anyElim (album => (own id = Some album.id) ∧ (holds album id = True)) (id ∈ photoIds (mergeAlbums local remote legs)) combined
    (ownerGives local.albums remote.albums combined id m)
    (album inCombined both =>
      List.anyElim (entry => entry.fst = album) (id ∈ photoIds (mergeAlbums local remote legs)) (albumEntries local remote)
        (List.memMapAny (albumEntries local remote) (entry => entry.fst) album inCombined)
        (entry inEntries e =>
          match both with
            | Both o h =>
              List.memFlatMapIntro (a => a.photos.map Photo.id) (keepOwned own (entry.fst.startAt (settle legs entry.snd))) id
                (mergeAlbums local remote legs)
                (List.memMap (albumEntries local remote) entry inEntries (x => keepOwned own (x.fst.startAt (settle legs x.snd))))
                (rewrite e in keptWhereOwned own album id o h)))

theorem withPhotosOfKeeps (remote: List Album) (album: Album) (id: Nat) (m: id ∈ album.photos.map Photo.id):
    id ∈ (withPhotosOf remote album).photos.map Photo.id := match e: remote.find (other => other.id == album.id) with
      | Some other =>
        Exists.elim (List.memMapElim Photo.id id album.photos m) (photo both =>
          match both with
            | Both inPhotos same => rewrite <- same in List.keyMemAppendNewByRight Photo.id other.photos album.photos photo inPhotos)
      | None => m

-- Every photo id of either copy is in the albums before ownership is
-- decided (with the remote album ids distinct, as in a well-formed copy).
theorem inCombined (local: Trip) (remote: Trip) (dr: List.Distinct (List.map remote.albums (album => album.id))) (id: Nat)
    (m: (id ∈ photoIds local.albums) ∨ (id ∈ photoIds remote.albums)): id ∈ photoIds ((albumEntries local remote).map (entry => entry.fst)) :=
  let fromLocal := local.albums.map (album => (withPhotosOf remote.albums album, locate local.legs album.start))
  let fromRemote := remote.albums.map (album => (album, locate remote.legs album.start))
  let combined := (albumEntries local remote).map (entry => entry.fst)
  match m with
    | Inl inLocal =>
      List.anyElim (a => id ∈ a.photos.map Photo.id) (id ∈ photoIds combined) local.albums
        (List.memFlatMapElim (a => a.photos.map Photo.id) id local.albums inLocal)
        (album inAlbums inAlbum =>
          List.memFlatMapIntro (a => a.photos.map Photo.id) (withPhotosOf remote.albums album) id combined
            (List.memMap (albumEntries local remote) (withPhotosOf remote.albums album, locate local.legs album.start)
              (List.memAppendLeft (withPhotosOf remote.albums album, locate local.legs album.start) fromLocal
                (List.differenceBy fromRemote fromLocal (entry => entry.fst.id))
                (List.memMap local.albums album inAlbums (a => (withPhotosOf remote.albums a, locate local.legs a.start))))
              (entry => entry.fst))
            (withPhotosOfKeeps remote.albums album id inAlbum))
    | Inr inRemote =>
      List.anyElim (a => id ∈ a.photos.map Photo.id) (id ∈ photoIds combined) remote.albums
        (List.memFlatMapElim (a => a.photos.map Photo.id) id remote.albums inRemote)
        (album inAlbums inAlbum =>
          if shared: album.id ∈ List.map local.albums (a => a.id) then
            Exists.elim (List.memMapElim (a => a.id) album.id local.albums shared) (mine both =>
              match both with
                | Both inMine sameId =>
                  let found: remote.albums.find (other => other.id == mine.id) = Some album :=
                    rewrite sameId in List.findKeyDistinct (a => a.id) remote.albums dr album inAlbums
                  List.memFlatMapIntro (a => a.photos.map Photo.id) (withPhotosOf remote.albums mine) id combined
                    (List.memMap (albumEntries local remote) (withPhotosOf remote.albums mine, locate local.legs mine.start)
                      (List.memAppendLeft (withPhotosOf remote.albums mine, locate local.legs mine.start) fromLocal
                        (List.differenceBy fromRemote fromLocal (entry => entry.fst.id))
                        (List.memMap local.albums mine inMine (a => (withPhotosOf remote.albums a, locate local.legs a.start))))
                      (entry => entry.fst))
                    (rewrite found in
                      Exists.elim (List.memMapElim Photo.id id album.photos inAlbum) (photo pb =>
                        match pb with
                          | Both inPhotos same => rewrite <- same in List.keyMemAppendNewByLeft Photo.id album.photos mine.photos photo inPhotos)))
          else
            let freshKey: album.id ∉ List.map fromLocal (entry => entry.fst.id) :=
              rewrite List.mapMap local.albums (entry => entry.fst.id) (a => (withPhotosOf remote.albums a, locate local.legs a.start)),
                List.mapCong local.albums (a => (withPhotosOf remote.albums a).id) (a => a.id) (a => withPhotosOfId remote.albums a) in
              shared
            List.memFlatMapIntro (a => a.photos.map Photo.id) album id combined
              (List.memMap (albumEntries local remote) (album, locate remote.legs album.start)
                (List.memAppendRight (album, locate remote.legs album.start) fromLocal (List.differenceBy fromRemote fromLocal (entry => entry.fst.id))
                  ((List.memDifferenceBy (album, locate remote.legs album.start) fromRemote fromLocal (entry => entry.fst.id)).backward
                    (Both (List.memMap remote.albums album inAlbums (a => (a, locate remote.legs a.start))) freshKey)))
                (entry => entry.fst))
              inAlbum)

-- Every photo of either copy is in some merged album (and, by
-- `mergeWellFormed`, in only one).
theorem photoIdsKept (local: Trip) (remote: Trip) (wr: WellFormed remote) (id: Nat)
    (m: (id ∈ photoIds local.albums) ∨ (id ∈ photoIds remote.albums)): id ∈ photoIds (merge local remote).albums :=
  keptFromCombined local remote (mergeLegs local.legs remote.legs) id (inCombined local remote wr.albumIds id m)
