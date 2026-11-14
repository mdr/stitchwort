-- An implicit record is solved from a type whose unfolding takes one of its
-- fields: `withinTrans r1 r2` compares `Within ?a ?b` with `r1`'s type,
-- whose unfolding reads the field `?b.rows` of the unknown. That field is a
-- call stuck on `?b`, so `?b` is solved from the call's argument,
-- `image.rotate` (SW-1998).

type Image = { rows: List Nat }

def Image.rotate (image: Image): Image := { rows = image.rows.reverse }

def Within (image other: Image): Prop := ∀ (x: Nat) => x ∈ other.rows → x ∈ image.rows

theorem withinTrans ∀ [a b c: Image] (first: Within a b) (second: Within b c): Within a c := x on =>
  first x (second x on)

theorem withinTwice ∀ (image: Image)
    (once: Within image image.rotate)
    (again: Within image.rotate image.rotate.rotate):
    Within image image.rotate.rotate :=
  withinTrans once again
