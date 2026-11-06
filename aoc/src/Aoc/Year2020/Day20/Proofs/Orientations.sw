--| Facts about the eight orientations: there are eight, flipping twice
--| changes nothing, and a flipped tile's edges are its own, reversed or
--| swapped, so they fit what the original's fit (`Spec.Fit`).

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20 (Spec)
import Std (Eq, List, Nat, Option)

theorem orientationCount (image: Image): image.orientations.length = 8 := rfl

theorem lastReverseOnto: (xs: List a) → (acc: List a) → (y: a) → List.last (List.reverseOnto xs [y, ..acc]) = List.last [y, ..acc]
  | [], acc, y => rfl
  | [x, ..rest], acc, y => lastReverseOnto rest [y, ..acc] x

theorem lastReverse (fallback: a): (xs: List a) → xs.reverse.last.getOrElse fallback = xs.headOr fallback
  | [] => rfl
  | [x, ..rest] => rewrite lastReverseOnto rest [] x in rfl

theorem headReverse (fallback: a) (xs: List a): xs.reverse.headOr fallback = xs.last.getOrElse fallback :=
  rewrite <- lastReverse fallback xs.reverse, List.reverseReverse xs in rfl

theorem flipTwice (image: Image): image.flip.flip = image :=
  let rows: image.rows.map (.reverse) |> .map (.reverse) = image.rows :=
    rewrite List.mapMap image.rows (.reverse) (.reverse), List.mapCong image.rows (row => row.reverse.reverse) (row => row) List.reverseReverse in List.mapId image.rows
  Image.ext image.flip.flip image rows

--| Flipped, a tile's top and bottom edges are reversed, and its left and
--| right edges swap.
theorem flipEdges (image: Image):
    Spec.edges image.flip
      = [(image.rows.headOr []).reverse, image.rows.map (row => row.headOr Calm), (image.rows.last.getOrElse []).reverse, image.rows.map (row => row.last.getOrElse Calm)] :=
  let top: (image.rows.map (.reverse)).headOr [] = (image.rows.headOr []).reverse :=
    match image.rows with
      | [] => rfl
      | [row, ..rest] => rfl
  let bottom: (image.rows.map (.reverse)).last.getOrElse [] = (image.rows.last.getOrElse []).reverse :=
    rewrite List.lastMap image.rows (.reverse) in
      match image.rows.last with
        | None => rfl
        | Some row => rfl
  let right: (image.rows.map (.reverse)).map (row => row.last.getOrElse Calm) = image.rows.map (row => row.headOr Calm) :=
    rewrite List.mapMap image.rows (row => row.last.getOrElse Calm) (.reverse) in List.mapCong image.rows _ _ (lastReverse Calm)
  let left: (image.rows.map (.reverse)).map (row => row.headOr Calm) = image.rows.map (row => row.last.getOrElse Calm) :=
    rewrite List.mapMap image.rows (row => row.headOr Calm) (.reverse) in List.mapCong image.rows _ _ (headReverse Calm)
  rewrite <- top, <- bottom, <- right, <- left in rfl
