-- Build a constructor by its field names with `C { field = value }`.
-- Fields come in any order; a bare `id` means `id = id`.
type Shape =
  | Circle (id: Text) (radius: Nat)
  | Rect (id: Text) (width: Nat) (height: Nat)

def wheel (id: Text): Shape := Circle { radius = 3, id }

-- Match by name too; `..` ignores the other fields.
def Shape.size: Shape -> Nat
  | Circle { radius, .. } => radius
  | Rect { width, height, .. } => width * height

-- `id` is a field of every constructor, so any shape has an `.id`, and an
-- update changes it whichever shape it is.
def Shape.renamed (s: Shape) (id: Text): Shape := { s | id = id }

test "by name" := wheel "front" == Circle "front" 3
test "shared field" := (Rect { id = "r", width = 2, height = 5 }).id == "r"
test "shared update" := ((wheel "a").renamed "b").id == "b"
test "match by name" := (Rect { id = "r", width = 2, height = 5 }).size == 10
