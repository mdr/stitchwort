-- expect-error: E-UNKNOWN-FIELD
-- `id` is in every constructor but at different types, so it isn't shared.

type Shape =
  | Dot (id: Text)
  | Polygon (id: Nat)

def idOf (a: Shape): Text := a.id
