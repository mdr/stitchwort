-- expect-error: E-INTERFACE-SHAPE
-- An interface has one parameter, a type (docs/proposals/interfaces.md
-- §5.1, D174): interfaces relating two types aren't supported.

interface Convert (a: Type) (b: Type) =
  { convert: a -> b }
