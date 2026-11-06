--| Facts about the eight orientations: there are eight, flipping twice
--| changes nothing, and a flipped tile's edges are its own, reversed or
--| swapped, so they fit what the original's fit (`Spec.Fit`).

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20 (Spec)
import Std (Eq, List, Nat, Option, Void)

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

-- Columns

theorem firstColumn (fallback: a): (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.filterMap rows (.get 0) = rows.map (row => row.headOr fallback)
  | [], k, sized => rfl
  | [[], ..rest], k, Both sized more => Void.exfalso (Nat.zeroNotSucc k sized)
  | [[x, ..xs], ..rest], k, Both sized more => Eq.cong (Cons x) (firstColumn fallback rest k more)

theorem lastDrop (fallback: a): (row: List a) → (k: Nat) → row.length = Succ (Succ k) → (row.drop 1).last.getOrElse fallback = row.last.getOrElse fallback
  | [], k, sized => Void.exfalso (Nat.zeroNotSucc _ sized)
  | [x], k, sized => Void.exfalso (Nat.zeroNotSucc _ (Nat.succInjective sized))
  | [x, y, ..rest], k, sized => rfl

theorem lastsDrop (fallback: a): (rows: List (List a)) → (k: Nat) → List.AllLength (Succ (Succ k)) rows →
    (rows.map (.drop 1)).map (row => row.last.getOrElse fallback) = rows.map (row => row.last.getOrElse fallback)
  | [], k, sized => rfl
  | [row, ..rest], k, Both sized more => rewrite lastDrop fallback row k sized, lastsDrop fallback rest k more in rfl

theorem lastColumnOne (fallback: a): (rows: List (List a)) → List.AllLength 1 rows →
    List.filterMap rows (.get 0) = rows.map (row => row.last.getOrElse fallback)
  | [], sized => rfl
  | [[], ..rest], Both sized more => Void.exfalso (Nat.zeroNotSucc _ sized)
  | [[x], ..rest], Both sized more => Eq.cong (Cons x) (lastColumnOne fallback rest more)
  | [[x, y, ..ys], ..rest], Both sized more => Void.exfalso (Nat.zeroNotSucc _ (Nat.succInjective (Eq.sym sized)))

--| The last column of rows all `Succ k` long is the last cell of each row.
theorem lastColumn (fallback: a): (k: Nat) → (rows: List (List a)) → List.AllLength (Succ k) rows →
    (List.transposeN (Succ k) rows).last.getOrElse [] = rows.map (row => row.last.getOrElse fallback)
  | Zero, rows, sized => lastColumnOne fallback rows sized
  | Succ k, rows, sized =>
    Eq.trans (lastColumn fallback k (rows.map (.drop 1)) (List.tailsAllLength rows (Succ k) sized)) (lastsDrop fallback rows k sized)

theorem allLengthMem [row: List a]: (rows: List (List a)) → (n: Nat) → List.AllLength n rows → row ∈ rows → row.length = n
  | [], n, sized, member => Void.exfalso member
  | [first, ..rest], n, Both sized more, Inl same => rewrite <- same in sized
  | [first, ..rest], n, Both sized more, Inr later => allLengthMem rest n more later

--| The first cell of each column is the first row.
theorem columnsFirst (fallback: a): (width: Nat) → (first: List a) → (rest: List (List a)) → List.AllLength width [first, ..rest] →
    (List.transposeN width [first, ..rest]).map (column => column.headOr fallback) = first
  | Zero, first, rest, Both sized more => Eq.sym (List.lengthZero first sized)
  | Succ k, [], rest, Both sized more => Void.exfalso (Nat.zeroNotSucc _ sized)
  | Succ k, [x, ..xs], rest, sized =>
    Eq.cong (Cons x) (columnsFirst fallback k xs (rest.map (.drop 1)) (List.tailsAllLength [[x, ..xs], ..rest] k sized))

theorem lastMemCons (first: a): (rest: List a) → ∃ (last: a) => List.last [first, ..rest] = Some last
  | [] => Witness first rfl
  | [second, ..more] => lastMemCons second more

theorem consHeadDrop (fallback: a): (row: List a) → (k: Nat) → row.length = Succ k → [row.headOr fallback, ..row.drop 1] = row
  | [], k, sized => Void.exfalso (Nat.zeroNotSucc _ sized)
  | [x, ..xs], k, sized => rfl

theorem columnsLastRow (fallback: a): (width: Nat) → (rows: List (List a)) → (row: List a) → List.AllLength width rows → List.last rows = Some row →
    (List.transposeN width rows).map (column => column.last.getOrElse fallback) = row
  | Zero, rows, row, sized, found => Eq.sym (List.lengthZero row (allLengthMem rows 0 sized (List.lastMem rows row found)))
  | Succ k, rows, row, sized, found =>
    let sizedRow := allLengthMem rows (Succ k) sized (List.lastMem rows row found)
    let foundTail: List.last (rows.map (.drop 1)) = Some (row.drop 1) := rewrite List.lastMap rows (.drop 1), found in rfl
    let later := columnsLastRow fallback k (rows.map (.drop 1)) (row.drop 1) (List.tailsAllLength rows k sized) foundTail
    let head: (List.filterMap rows (.get 0)).last.getOrElse fallback = row.headOr fallback :=
      rewrite firstColumn fallback rows k sized, List.lastMap rows (row => row.headOr fallback), found in rfl
    rewrite later, head in consHeadDrop fallback row k sizedRow

--| The last cell of each column is the last row.
theorem columnsLast (fallback: a) (width: Nat) (first: List a) (rest: List (List a)) (sized: List.AllLength width [first, ..rest]):
    (List.transposeN width [first, ..rest]).map (column => column.last.getOrElse fallback) = List.last [first, ..rest] |> .getOrElse [] :=
  match lastMemCons first rest with
    | Witness row found => rewrite found in columnsLastRow fallback width [first, ..rest] row sized found
