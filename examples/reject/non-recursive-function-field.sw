-- expect-error: E-TERMINATION
-- Applying a constructor's function field counts as smaller only when the
-- field is recursive (it returns the type being matched), as in Rocq. `f`
-- returns a `Nat` from a `Wrap`, so `f 0` isn't accepted, even though this
-- particular function does terminate.
type Wrap : Type =
  | MkWrap (f : Nat -> Nat)

Pick : Bool -> Type
Pick True  = Wrap
Pick False = Nat

h : (b : Bool) -> Pick b -> Nat
h True  (MkWrap f) = h False (f 0)
h False n          = n
