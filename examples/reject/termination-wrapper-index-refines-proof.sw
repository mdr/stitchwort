-- expect-error: E-TERMINATION
-- Agda #8699's own mechanism: matching `Step` refines the index to
-- `MkSq (More q)`, so `MkSq`'s field becomes `More q` without a match on
-- it. `MkSq`'s one field is a proof and the descent is in it, so
-- `f (MkSq q) …` isn't smaller (docs/reviews/SW-3412-text-rest-relanded.md, d3).
import Std (Unit)
type Big: Prop = | Stop | More (b: Big)
type Sq: Type = | MkSq (b: Big)
type T: Sq → Type = | Step [q: Big]: T (MkSq (More q))
theorem f: (s: Sq) → T s → Unit
  | MkSq b, Step [q := q] => f (MkSq q) (Step [q := q])
