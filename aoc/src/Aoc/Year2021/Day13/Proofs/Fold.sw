--| One fold: where the program moves a dot is where the puzzle says it
--| lands, and the dots after `foldOnce` are the image of the dots before.

namespace Aoc.Year2021.Day13.Proofs
import Aoc.Common (Point)
import Aoc.Year2021.Day13 (..)
import Aoc.Year2021.Day13.Spec (..)
import Std (Eq, Exists, List, Nat)

--| A dot clear of the fold lands where `foldDot` puts it...
theorem landsFoldDot ∀ (fold: Fold) (dot: Point) (clear: Clear fold dot): Lands fold dot (foldDot fold dot) :=
  match fold with
    | AlongY line => cases
    | AlongX line => cases

--| ...and nowhere else.
theorem landsOnly ∀ (fold: Fold) (dot: Point) (spot: Point) (lands: Lands fold dot spot): spot = foldDot fold dot :=
  match fold with
    | AlongY line =>
      match lands with
        | Both sameX (Inl (Both lt sameY)) => Point.ext spot (foldDot (AlongY line) dot) cases cases
        | Both sameX (Inr (Both gt sum)) => Point.ext spot (foldDot (AlongY line) dot) cases cases
    | AlongX line =>
      match lands with
        | Both sameY (Inl (Both lt sameX)) => Point.ext spot (foldDot (AlongX line) dot) cases cases
        | Both sameY (Inr (Both gt sum)) => Point.ext spot (foldDot (AlongX line) dot) cases cases

--| A list holds a set of dots when its members are exactly the set's dots.
def Holds (dots: List Point) (marked: Point → Prop): Prop := ∀ (spot: Point) => spot ∈ dots ↔ marked spot

--| If a list holds the dots before a fold, and every one of them is clear
--| of it, `foldOnce` holds the dots after it.
theorem foldOnceHolds ∀ (dots: List Point) (marked: Point → Prop) (fold: Fold) (holds: Holds dots marked) (clear: ∀ (dot: Point) => marked dot → Clear fold dot):
    Holds (foldOnce dots fold) (AfterFold fold marked) :=
  spot => {
    forward = member =>
      let mapped := (List.memUnique spot (dots.map (foldDot fold))).forward member
      Exists.elim (List.memMapElim (foldDot fold) spot dots mapped) (dot moved =>
        Witness dot (Both ((holds dot).forward moved.left) (rewrite <- moved.right in landsFoldDot fold dot (clear dot ((holds dot).forward moved.left))))),
    backward = after =>
      Exists.elim after (dot lands =>
        let mapped := List.memMap dots dot ((holds dot).backward lands.left) (foldDot fold)
        (List.memUnique spot (dots.map (foldDot fold))).backward (rewrite landsOnly fold dot spot lands.right in mapped))
  }
