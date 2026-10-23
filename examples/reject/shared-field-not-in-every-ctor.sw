-- expect-error: E-UNKNOWN-FIELD
-- `text` is only `Circle`'s, so `Shape` has no shared field `text`.

type Shape =
  | Dot (id: Text)
  | Circle (id: Text) (text: Text)

def textOf (a: Shape): Text := a.text
