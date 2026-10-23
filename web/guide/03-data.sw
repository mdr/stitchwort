-- A variant type: one of several shapes, each with its own fields.
type Shape =
  | Circle (radius: Nat)
  | Rect (width: Nat) (height: Nat)

def Shape.area: Shape -> Nat
  | Circle r => 3 * r * r
  | Rect w h => w * h

-- A record: named fields, read with `.` and updated with `{ x | field = ... }`.
type Book = { title: Text, pages: Nat }

def dune: Book := { title = "Dune", pages = 412 }

def Book.longer (b: Book): Book := { b | pages = b.pages + 100 }

def Book.label: Book -> Text
  | { title, pages } => "${title} (${pages} pages)"

test "area" := Shape.area (Rect 3 4) == 12
test "update" := dune.longer.pages == 512
test "label" := dune.label == "Dune (412 pages)"
