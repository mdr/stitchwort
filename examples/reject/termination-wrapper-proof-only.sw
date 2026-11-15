-- expect-error: E-TERMINATION
-- A wrapper whose one field is a proof, of a proposition that has a base
-- case: `MkWP q` isn't smaller than `MkWP (More q)`, as in
-- termination-wrapper-proof-irrelevance-07.sw, since comparison skips the
-- proof and so sees one value. Pairs with accept/termination-wrapper-
-- honest.sw, where the one field is data.
type Big: Prop = | Stop | More (b: Big)

type WP: Type = | MkWP (b: Big)

theorem down: WP → Big
  | MkWP (More q) => down (MkWP q)
  | MkWP Stop => Stop
