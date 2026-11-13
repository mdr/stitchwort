--| Facts about the eight orientations: there are eight, flipping twice
--| changes nothing, and a flipped tile's edges are its own, reversed or
--| swapped, so they fit what the original's fit (`Spec.Fit`).

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

theorem orientationCount (image: Image): image.orientations.length = 8 := rfl

theorem lastReverseOnto (xs acc: List a) (y: a): List.last (List.reverseOnto xs [y, ..acc]) = List.last [y, ..acc] :=
  match xs with
    | [] => rfl
    | [x, ..rest] => lastReverseOnto rest [y, ..acc] x

theorem lastReverse (fallback: a) (xs: List a): xs.reverse.last.getOrElse fallback = xs.headOr fallback := match xs with
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

theorem firstColumn (fallback: a) (rows: List (List a)) (k: Nat) (h: List.AllLength (Succ k) rows):
    List.filterMap rows (.get 0) = rows.map (row => row.headOr fallback) := match rows, h with
      | [], sized => rfl
      | [[], ..rest], Both sized more => Void.exfalso (Nat.zeroNotSucc k sized)
      | [[x, ..xs], ..rest], Both sized more => Eq.cong (Cons x) (firstColumn fallback rest k more)

theorem lastDrop (fallback: a) (row: List a) (k: Nat) (sized: row.length = Succ (Succ k)): (row.drop 1).last.getOrElse fallback = row.last.getOrElse fallback :=
  match row with
    | [] => Void.exfalso (Nat.zeroNotSucc _ sized)
    | [x] => Void.exfalso (Nat.zeroNotSucc _ (Nat.succInjective sized))
    | [x, y, ..rest] => rfl

theorem lastsDrop (fallback: a) (rows: List (List a)) (k: Nat) (h: List.AllLength (Succ (Succ k)) rows):
    (rows.map (.drop 1)).map (row => row.last.getOrElse fallback) = rows.map (row => row.last.getOrElse fallback) :=
  match rows, h with
    | [], sized => rfl
    | [row, ..rest], Both sized more => rewrite lastDrop fallback row k sized, lastsDrop fallback rest k more in rfl

theorem lastColumnOne (fallback: a) (rows: List (List a)) (h: List.AllLength 1 rows):
    List.filterMap rows (.get 0) = rows.map (row => row.last.getOrElse fallback) := match rows, h with
      | [], sized => rfl
      | [[], ..rest], Both sized more => Void.exfalso (Nat.zeroNotSucc _ sized)
      | [[x], ..rest], Both sized more => Eq.cong (Cons x) (lastColumnOne fallback rest more)
      | [[x, y, ..ys], ..rest], Both sized more => Void.exfalso (Nat.zeroNotSucc _ (Nat.succInjective (Eq.sym sized)))

--| The last column of rows all `Succ k` long is the last cell of each row.
theorem lastColumn (fallback: a) (k: Nat) (rows: List (List a)) (sized: List.AllLength (Succ k) rows):
    (List.transposeN (Succ k) rows).last.getOrElse [] = rows.map (row => row.last.getOrElse fallback) := match k with
      | Zero => lastColumnOne fallback rows sized
      | Succ k =>
        Eq.trans (lastColumn fallback k (rows.map (.drop 1)) (List.tailsAllLength rows (Succ k) sized)) (lastsDrop fallback rows k sized)

--| The first cell of each column is the first row.
theorem columnsFirst (fallback: a) (width: Nat) (first: List a) (rest: List (List a)) (h: List.AllLength width [first, ..rest]):
    (List.transposeN width [first, ..rest]).map (column => column.headOr fallback) = first := match width, first, h with
      | Zero, first, Both sized more => Eq.sym (List.lengthZero first sized)
      | Succ k, [], Both sized more => Void.exfalso (Nat.zeroNotSucc _ sized)
      | Succ k, [x, ..xs], sized =>
        Eq.cong (Cons x) (columnsFirst fallback k xs (rest.map (.drop 1)) (List.tailsAllLength [[x, ..xs], ..rest] k sized))

theorem lastMemCons (first: a) (rest: List a): ∃ (last: a) => List.last [first, ..rest] = Some last := match rest with
  | [] => Witness first rfl
  | [second, ..more] => lastMemCons second more

theorem consHeadDrop (fallback: a) (row: List a) (k: Nat) (sized: row.length = Succ k): [row.headOr fallback, ..row.drop 1] = row :=
  match row with
    | [] => Void.exfalso (Nat.zeroNotSucc _ sized)
    | [x, ..xs] => rfl

theorem columnsLastRow (fallback: a) (width: Nat) (rows: List (List a)) (row: List a) (sized: List.AllLength width rows) (found: List.last rows = Some row):
    (List.transposeN width rows).map (column => column.last.getOrElse fallback) = row := match width with
      | Zero => Eq.sym (List.lengthZero row (List.allLengthMem rows 0 sized (List.lastMem rows row found)))
      | Succ k =>
        let sizedRow := List.allLengthMem rows (Succ k) sized (List.lastMem rows row found)
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

theorem reverseNil (xs: List a) (empty: xs.reverse = []): xs = [] :=
  List.lengthZero xs (rewrite <- List.lengthReverse xs, empty in rfl)

--| Turned a quarter clockwise, a rectangle's left edge, reversed, is its
--| top; its top is its right; its right, reversed, its bottom; and its
--| bottom its left.
theorem rotateEdges (image: Image) (k: Nat) (sized: List.AllLength (Succ k) image.rows) (nonEmpty: image.rows ≠ []):
    Spec.edges image.rotate
      = [(image.rows.map (row => row.headOr Calm)).reverse, image.rows.headOr [], (image.rows.map (row => row.last.getOrElse Calm)).reverse, image.rows.last.getOrElse []] :=
  let reversedSized: List.AllLength (Succ k) image.rows.reverse := List.allLengthReverseOnto (Succ k) image.rows [] sized Trivial
  let left := (image.rows.map (row => row.headOr Calm)).reverse
  let right := (image.rows.map (row => row.last.getOrElse Calm)).reverse
  let shaped: ∀ (turned: List (List Pixel)) => turned = image.rows.reverse →
      Spec.edges { rows = turned.transpose } = [left, image.rows.headOr [], right, image.rows.last.getOrElse []] :=
    turned same =>
      match turned with
        | [] => Void.exfalso (nonEmpty (reverseNil image.rows (Eq.sym same)))
        | [first, ..rest] =>
          let turnedSized: List.AllLength (Succ k) [first, ..rest] := rewrite <- same at reversedSized in reversedSized
          let width: first.length = Succ k := turnedSized.left
          let top: List.filterMap [first, ..rest] (.get 0) = left :=
            Eq.trans (firstColumn Calm [first, ..rest] k turnedSized)
              (Eq.trans (Eq.cong (rows => rows.map (row => row.headOr Calm)) same) (List.mapReverse image.rows (row => row.headOr Calm)))
          let toRight: (List.transposeN (Succ k) [first, ..rest]).map (column => column.last.getOrElse Calm) = image.rows.headOr [] :=
            Eq.trans (columnsLast Calm (Succ k) first rest turnedSized)
              (Eq.trans (Eq.cong (rows => List.last rows |> .getOrElse []) same) (lastReverse [] image.rows))
          let bottom: (List.transposeN (Succ k) [first, ..rest]).last.getOrElse [] = right :=
            Eq.trans (lastColumn Calm k [first, ..rest] turnedSized)
              (Eq.trans (Eq.cong (rows => rows.map (row => row.last.getOrElse Calm)) same) (List.mapReverse image.rows (row => row.last.getOrElse Calm)))
          let toLeft: (List.transposeN (Succ k) [first, ..rest]).map (column => column.headOr Calm) = image.rows.last.getOrElse [] :=
            Eq.trans (columnsFirst Calm (Succ k) first rest turnedSized)
              (Eq.trans (Eq.cong (rows => rows.headOr []) same) (headReverse [] image.rows))
          rewrite width in rewrite <- top, <- toRight, <- bottom, <- toLeft in rfl
  shaped image.rows.reverse rfl

-- Every orientation's edges are the tile's, some reversed

--| Every row `width` long, and at least one row: what the tiles are, and
--| what turns and flips keep.
def Rectangle (image: Image): Prop := ∃ (k: Nat) => List.AllLength (Succ k) image.rows ∧ image.rows ≠ []

theorem allLengthFlip (n: Nat) (rows: List (List Pixel)) (h: List.AllLength n rows): List.AllLength n (rows.map (.reverse)) :=
  match rows, h with
    | [], sized => Trivial
    | [row, ..rest], Both sized more => Both (rewrite List.lengthReverse row in sized) (allLengthFlip n rest more)

theorem rectangleFlip (image: Image) (rectangle: Rectangle image): Rectangle image.flip := match rectangle with
  | Witness k (Both sized nonEmpty) =>
    Witness k (Both (allLengthFlip (Succ k) image.rows sized) (empty => nonEmpty (List.lengthZero image.rows (rewrite <- List.lengthMap image.rows (.reverse), empty in rfl))))

theorem rectangleRotate (image: Image) (rectangle: Rectangle image): Rectangle image.rotate := match rectangle with
  | Witness k (Both sized nonEmpty) =>
    let reversedSized: List.AllLength (Succ k) image.rows.reverse := List.allLengthReverseOnto (Succ k) image.rows [] sized Trivial
    let shaped: ∀ (turned: List (List Pixel)) => turned = image.rows.reverse → Rectangle { rows = turned.transpose } :=
      turned same =>
        match turned with
          | [] => Void.exfalso (nonEmpty (reverseNil image.rows (Eq.sym same)))
          | [first, ..rest] =>
            let turnedSized: List.AllLength (Succ k) [first, ..rest] := rewrite <- same at reversedSized in reversedSized
            let width: first.length = Succ k := turnedSized.left
            rewrite width in
              Witness rest.length (Both (List.columnsAllLength (Succ k) [first, ..rest] (Succ rest.length) rfl turnedSized) (List.consNotNil _ _))
    shaped image.rows.reverse rfl

--| Each edge of `other` fits an edge of `image`.
def Within (image: Image) (other: Image): Prop :=
  ∀ (edge: List Pixel) => edge ∈ Spec.edges other → ∃ (original: List Pixel) => original ∈ Spec.edges image ∧ Spec.Fit edge original

theorem fitTrans [edge: List Pixel] [middle: List Pixel] [original: List Pixel] (first: Spec.Fit edge middle) (second: Spec.Fit middle original): Spec.Fit edge original :=
  match first with
    | Inl same =>
      match second with
        | Inl again => Inl (rewrite same, again in rfl)
        | Inr reversed => Inr (rewrite same, reversed in rfl)
    | Inr reversed =>
      match second with
        | Inl again => Inr (rewrite reversed, again in rfl)
        | Inr twice => Inl (rewrite reversed, twice in List.reverseReverse original)

theorem withinTrans [a: Image] [b: Image] [c: Image] (first: Within a b) (second: Within b c): Within a c :=
  edge onC =>
    match second edge onC with
      | Witness middle (Both onB fitB) =>
        match first middle onB with
          | Witness original (Both onA fitA) => Witness original (Both onA (fitTrans fitB fitA))

theorem withinSelf (image: Image): Within image image := edge member => Witness edge (Both member (Inl rfl))

-- Still needed by `orientedFit`: its goal `edge ∈ Spec.edges turned` arrives with `turned` substituted, already
-- stepped to a disjunction, so `rewrite` has no `Spec.edges …` to find there; a variable `xs` keeps `∈` folded.
theorem memEq [x: a] [xs: List a] [ys: List a] (same: xs = ys) (member: x ∈ xs): x ∈ ys := rewrite same at member in member

theorem withinFlip (image: Image): Within image image.flip :=
  edge member =>
    match (rewrite flipEdges image at member) with
      | Inl same => Witness (image.rows.headOr []) (Both (Inl rfl) (Inr (Eq.sym same)))
      | Inr (Inl same) => Witness (image.rows.map (row => row.headOr Calm)) (Both (Inr (Inr (Inr (Inl rfl)))) (Inl (Eq.sym same)))
      | Inr (Inr (Inl same)) => Witness (image.rows.last.getOrElse []) (Both (Inr (Inr (Inl rfl))) (Inr (Eq.sym same)))
      | Inr (Inr (Inr (Inl same))) => Witness (image.rows.map (row => row.last.getOrElse Calm)) (Both (Inr (Inl rfl)) (Inl (Eq.sym same)))
      | Inr (Inr (Inr (Inr never))) => Void.exfalso never

theorem withinRotate (image: Image) (rectangle: Rectangle image): Within image image.rotate := match rectangle with
  | Witness k (Both sized nonEmpty) =>
    edge member =>
      match (rewrite rotateEdges image k sized nonEmpty at member) with
        | Inl same => Witness (image.rows.map (row => row.headOr Calm)) (Both (Inr (Inr (Inr (Inl rfl)))) (Inr (Eq.sym same)))
        | Inr (Inl same) => Witness (image.rows.headOr []) (Both (Inl rfl) (Inl (Eq.sym same)))
        | Inr (Inr (Inl same)) => Witness (image.rows.map (row => row.last.getOrElse Calm)) (Both (Inr (Inl rfl)) (Inr (Eq.sym same)))
        | Inr (Inr (Inr (Inl same))) => Witness (image.rows.last.getOrElse []) (Both (Inr (Inr (Inl rfl))) (Inl (Eq.sym same)))
        | Inr (Inr (Inr (Inr never))) => Void.exfalso never

--| Every edge of every orientation of a rectangle fits one of its own edges.
theorem withinOrientations (image: Image) (rectangle: Rectangle image) (turned: Image) (member: turned ∈ image.orientations): Within image turned :=
  let r1 := withinRotate image rectangle
  let rect1 := rectangleRotate image rectangle
  let r2 := withinTrans r1 (withinRotate image.rotate rect1)
  let rect2 := rectangleRotate image.rotate rect1
  let r3 := withinTrans r2 (withinRotate image.rotate.rotate rect2)
  let f0 := withinFlip image
  let flipped := rectangleFlip image rectangle
  let f1 := withinTrans f0 (withinRotate image.flip flipped)
  let flipped1 := rectangleRotate image.flip flipped
  let f2 := withinTrans f1 (withinRotate image.flip.rotate flipped1)
  let flipped2 := rectangleRotate image.flip.rotate flipped1
  let f3 := withinTrans f2 (withinRotate image.flip.rotate.rotate flipped2)
  match member with
    | Inl same => rewrite <- same in withinSelf image
    | Inr (Inl same) => rewrite <- same in r1
    | Inr (Inr (Inl same)) => rewrite <- same in r2
    | Inr (Inr (Inr (Inl same))) => rewrite <- same in r3
    | Inr (Inr (Inr (Inr (Inl same)))) => rewrite <- same in f0
    | Inr (Inr (Inr (Inr (Inr (Inl same))))) => rewrite <- same in f1
    | Inr (Inr (Inr (Inr (Inr (Inr (Inl same)))))) => rewrite <- same in f2
    | Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl same))))))) => rewrite <- same in f3
    | Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr never))))))) => Void.exfalso never

--| An edge that fits one of a rectangle's edges is an edge of one of its
--| orientations: itself, a quarter turn, or its mirror image.
theorem orientedFit (image: Image) (rectangle: Rectangle image) [edge: List Pixel] [original: List Pixel]
    (onImage: original ∈ Spec.edges image) (fit: Spec.Fit edge original): ∃ (turned: Image) => turned ∈ image.orientations ∧ edge ∈ Spec.edges turned :=
  let flipped: image.flip ∈ image.orientations := Inr (Inr (Inr (Inr (Inl rfl))))
  let rotated: image.rotate ∈ image.orientations := Inr (Inl rfl)
  match fit with
    | Inl same => Witness image (Both (Inl rfl) (rewrite same in onImage))
    | Inr reversed =>
      match rectangle with
        | Witness k (Both sized nonEmpty) =>
          let turnedEdges := rotateEdges image k sized nonEmpty
          match onImage with
            | Inl top => Witness image.flip (Both flipped (memEq (Eq.sym (flipEdges image)) (rewrite reversed, <- top in Inl rfl)))
            | Inr (Inl right) => Witness image.rotate (Both rotated (memEq (Eq.sym turnedEdges) (rewrite reversed, <- right in Inr (Inr (Inl rfl)))))
            | Inr (Inr (Inl bottom)) => Witness image.flip (Both flipped (memEq (Eq.sym (flipEdges image)) (rewrite reversed, <- bottom in Inr (Inr (Inl rfl)))))
            | Inr (Inr (Inr (Inl left))) => Witness image.rotate (Both rotated (memEq (Eq.sym turnedEdges) (rewrite reversed, <- left in Inl rfl)))
            | Inr (Inr (Inr (Inr never))) => Void.exfalso never

--| The puzzle's words: an edge matches another tile's when that tile, in
--| some orientation, has it as an edge. For rectangular tiles that is
--| `Spec.Matched`, whose edges fit forwards or reversed.
theorem matchedOriented (jigsaw: Jigsaw) (rectangles: ∀ (tile: Tile) => tile ∈ jigsaw.tiles → Rectangle tile.image) (tile: Tile) (edge: List Pixel):
    Spec.Matched jigsaw tile edge
      ↔ ∃ (other: Tile) => other ∈ jigsaw.tiles ∧ other.id ≠ tile.id ∧ ∃ (turned: Image) => turned ∈ other.image.orientations ∧ edge ∈ Spec.edges turned := {
  forward = matched =>
    match matched with
      | Witness other (Both member (Both different (Witness original (Both onOther fit)))) =>
        Witness other (Both member (Both different (orientedFit other.image (rectangles other member) onOther fit))),
  backward = oriented =>
    match oriented with
      | Witness other (Both member (Both different (Witness turned (Both isTurned onTurned)))) =>
        Witness other (Both member (Both different (withinOrientations other.image (rectangles other member) turned isTurned edge onTurned)))
}

theorem allLengthOfAll (n: Nat) (rows: List (List Pixel)) (all: rows.all (row => row.length == n) = True): List.AllLength n rows :=
  match rows with
    | [] => Trivial
    | [row, ..rest] => Both (DecEq.sound (Bool.andLeft all)) (allLengthOfAll n rest (Bool.andRight all))

theorem rowsRectangle (rows: List (List Pixel)) (checked: Image.isRectangle { rows } = True): Rectangle { rows } :=
  match rows with
    | [first, ..rest] =>
      match width: first.length with
        | Succ k => Witness k (Both (allLengthOfAll (Succ k) [first, ..rest] checked) (List.consNotNil first rest))

theorem isRectangleSound (image: Image) (checked: image.isRectangle = True): Rectangle image :=
  let eta: { rows = image.rows } = image := Image.ext _ _ rfl
  rowsRectangle image.rows (rewrite eta in checked)

theorem rectangularSound (jigsaw: Jigsaw) (checked: jigsaw.rectangular = True) (tile: Tile) (member: tile ∈ jigsaw.tiles): Rectangle tile.image := isRectangleSound tile.image (checked.read tile member)
