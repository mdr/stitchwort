--| The picture: `render` shows exactly the dots of the list it is given.

namespace Aoc.Year2021.Day13.Proofs
import Aoc.Common (Point)
import Aoc.Year2021.Day13 (..)
import Aoc.Year2021.Day13.Spec (..)
import Std (Eq, Exists, List, Nat, Option, Void)

--| Reading a list made by mapping over `List.range 0 n`: inside it, the
--| function's value...
theorem getMapRange ∀ [b: Type] (f: Nat → b) (n i: Nat)
    (inside: i < n):
    List.get (List.map (List.range 0 n) f) i = Some (f i) :=
  let long: i < List.length (List.map (List.range 0 n) f) :=
    rewrite List.lengthMap (List.range 0 n) f in rewrite List.lengthRangeFrom n 0 in inside
  rewrite List.getOfGetOr (List.map (List.range 0 n) f) i (f i) long in
    rewrite List.getOrMapRange f (f i) n 0 i inside in rewrite Nat.addZero i in rfl

--| ...and past it, nothing.
theorem getMapRangePast ∀ [b: Type] (f: Nat → b) (n i: Nat)
    (past: n ≤ i):
    List.get (List.map (List.range 0 n) f) i = None :=
  List.getPast
    (List.map (List.range 0 n) f)
    i
    (rewrite List.lengthMap (List.range 0 n) f in rewrite List.lengthRangeFrom n 0 in past)

--| Every dot of the list is inside the width and height `render` uses.
theorem widthCovers ∀ (dots: List Point) (spot: Point) (member: spot ∈ dots): spot.x < width dots :=
  match dots, member with
    | [], member => Void.exfalso member
    | [dot, ..rest], Inl same => rewrite <- same in omega [widthCons dot rest, Nat.leMaxLeft (dot.x + 1) (width rest)]
    | [dot, ..rest], Inr later => omega [widthCons dot rest, widthCovers rest spot later]

theorem heightCovers ∀ (dots: List Point) (spot: Point) (member: spot ∈ dots): spot.y < height dots :=
  match dots, member with
    | [], member => Void.exfalso member
    | [dot, ..rest], Inl same => rewrite <- same in omega [heightCons dot rest, Nat.leMaxLeft (dot.y + 1) (height rest)]
    | [dot, ..rest], Inr later =>
      omega [heightCons dot rest, heightCovers rest spot later, Nat.leMaxRight (dot.y + 1) (height rest)]

--| `foldRight` is a `foldLeft` over the reversed list, so these don't hold
--| by computing.
theorem widthCons ∀ (dot: Point) (rest: List Point): width [dot, ..rest] = Nat.max (dot.x + 1) (width rest) :=
  List.foldRightCons rest dot 0 (dot widest => Nat.max (dot.x + 1) widest)

theorem heightCons ∀ (dot: Point) (rest: List Point): height [dot, ..rest] = Nat.max (dot.y + 1) (height rest) :=
  List.foldRightCons rest dot 0 (dot lowest => Nat.max (dot.y + 1) lowest)

--| Inside the picture, a spot shows `#` if it is in the list and `.` if it
--| isn't...
theorem cellInside ∀ (dots: List Point) (spot: Point)
    (inY: spot.y < height dots)
    (inX: spot.x < width dots):
    cellAt (render dots) spot = Some (if dots.any (== spot) then '#' else '.') :=
  rewrite getMapRange _ (height dots) spot.y inY in rewrite getMapRange _ (width dots) spot.x inX in rfl

--| ...and outside it there is nothing.
theorem cellOutside ∀ (dots: List Point) (spot: Point)
    (out: height dots ≤ spot.y ∨ width dots ≤ spot.x):
    cellAt (render dots) spot = None :=
  match out with
    | Inl low => rewrite getMapRangePast _ (height dots) spot.y low in rfl
    | Inr wide =>
      if inY: spot.y < height dots then
        rewrite getMapRange _ (height dots) spot.y inY in rewrite getMapRangePast _ (width dots) spot.x wide in rfl
      else rewrite getMapRangePast _ (height dots) spot.y omega in rfl

--| So whatever the picture shows is inside it.
theorem cellSomeInside ∀ (dots: List Point) (spot: Point) (c: Char)
    (found: cellAt (render dots) spot = Some c):
    spot.y < height dots ∧ spot.x < width dots :=
  if inY: spot.y < height dots then
    if inX: spot.x < width dots then Both inY inX
    else Void.exfalso (Option.noneNotSome c (rewrite cellOutside dots spot (Inr omega) at found))
  else Void.exfalso (Option.noneNotSome c (rewrite cellOutside dots spot (Inl omega) at found))

--| A cell shows `#` or `.`, and `#` only for a dot.
theorem shownChar ∀ (b: Bool) (c: Char) (shown: Some (if b then '#' else '.') = Some c): c = '#' ∨ c = '.' :=
  match b with
    | True => Inl (Eq.sym (Option.someInjective shown))
    | False => Inr (Eq.sym (Option.someInjective shown))

theorem shownHash ∀ (b: Bool) (shown: Some (if b then '#' else '.') = Some '#'): b = True := cases

--| Every row is as wide as the dots need.
theorem rowWidth ∀ (dots: List Point) (row: List Char) (member: row ∈ render dots): row.length = width dots :=
  Exists.elim (List.memMapElim _ row (List.range 0 (height dots)) member) (y made =>
    rewrite <- made.right in
      rewrite List.lengthMap (List.range 0 (width dots)) _ in List.lengthRangeFrom (width dots) 0)

--| The picture shows every list it renders.
theorem renderShows ∀ (dots: List Point) (marked: Point → Prop)
    (holds: ∀ (spot: Point) => spot ∈ dots ↔ marked spot):
    Shows (render dots) marked :=
  Both
    (spot isMarked =>
      let member := (holds spot).backward isMarked
      rewrite cellInside dots spot (heightCovers dots spot member) (widthCovers dots spot member) in
        rewrite (List.anyEqIff spot dots).backward member in rfl)
    (Both
      (spot hash =>
        let inside := cellSomeInside dots spot '#' hash
        let shown := rewrite cellInside dots spot inside.left inside.right at hash
        (holds spot).forward ((List.anyEqIff spot dots).forward (shownHash _ shown)))
      (Both
        (spot c found =>
          let inside := cellSomeInside dots spot c found
          shownChar _ c (rewrite cellInside dots spot inside.left inside.right at found))
        (row inPicture other otherInPicture =>
          rewrite rowWidth dots row inPicture in rewrite rowWidth dots other otherInPicture in rfl)))
