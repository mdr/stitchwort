-- expect-error: E-ATTRIBUTE
type Box (@[js.name "T"] a: Type) =
  | MkBox (value: a)
