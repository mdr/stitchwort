-- expect-error: E-DUPLICATE
-- `id` is shared, so `Shape.id` is generated; a written one clashes.

type Shape =
  | Dot (id: Text)
  | Circle (id: Text) (r: Nat)

def Shape.id: Shape → Text
  | Dot i => i
  | Circle i _ => i
