-- expect-error: E-TYPE-MISMATCH
-- The middle image solved from the first link's field, `image.rotate`, isn't
-- the second link's start, `image.flip`: solving an implicit record from a
-- field of it doesn't make the two links meet (SW-1998).

type Image = { rows: List Nat }

def Image.rotate (image: Image): Image := { rows = image.rows.reverse }

def Image.flip (image: Image): Image := { rows = image.rows.map (row => row + 1) }

def Within (image: Image) (other: Image): Prop := ∀ (x: Nat) => x ∈ other.rows → x ∈ image.rows

theorem withinTrans ∀ [a: Image] [b: Image] [c: Image] (first: Within a b) (second: Within b c): Within a c :=
  x on => first x (second x on)

theorem withinApart ∀ (image: Image) (once: Within image image.rotate) (again: Within image.flip image.flip.rotate):
    Within image image.flip.rotate :=
  withinTrans once again
