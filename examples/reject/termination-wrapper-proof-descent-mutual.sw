-- expect-error: E-TERMINATION
-- proof-irrelevance-07 split over a mutual pair: `g` takes the proof
-- apart and `f` gets `MkBox n`, the same value as its argument to the
-- kernel. Size change sees `f → g` as `<` (a field) but `g → f` as
-- unknown, since `MkBox`'s one field is a proof
-- (docs/reviews/SW-3412-text-rest-relanded.md, c1).
import Std (Void)
type Loop: Prop = | MkLoop (next: Loop)
type Box (a: Prop): Type = | MkBox (h: a)
def f: Box Loop → Void
  | MkBox l => g l
def g: Loop → Void
  | MkLoop n => f (MkBox n)
