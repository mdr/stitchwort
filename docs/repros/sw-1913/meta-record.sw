type Image = { rows: List Nat }

def Image.rotate (image: Image): Image := { rows = image.rows.reverse }

def Within (image: Image) (other: Image): Prop := (x: Nat) → x ∈ other.rows → x ∈ image.rows

theorem withinTrans [a: Image] [b: Image] [c: Image] (first: Within a b) (second: Within b c): Within a c :=
  x on => first x (second x on)

theorem probe (image: Image) (r1: Within image image.rotate) (r2: Within image.rotate image.rotate.rotate): Within image image.rotate.rotate :=
  let r := withinTrans r1 r2
  r
