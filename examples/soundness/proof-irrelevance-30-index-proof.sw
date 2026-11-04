-- expect-error: E-NOT-EMPTY
-- Index unification deletes an equation that holds by comparison before
-- taking constructors apart, and comparison skips the box's proof field:
-- `T (MkBox (Inr ()))` may be `A`, so it isn't empty. Partner: `useA` in
-- accept/proof-irrelevance.sw.
import Std (Unit, Void)

type Box (a: Prop): Type =
  | MkBox (h: a)

type T: Box (Unit ∨ Unit) → Type =
  | A: T (MkBox (Inl ()))

theorem noA: T (MkBox (Inr ())) → Void
  | ()
