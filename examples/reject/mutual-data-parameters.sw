-- expect-error: E-MUTUAL-PARAMETERS
-- Data types defined together share one list of parameters.
type Rose (a: Type): Type =
  | Bloom (value: a) (kids: Roses a)

type Roses (b: Type): Type =
  | NoRoses
  | MoreRoses (first: Rose b) (rest: Roses b)
