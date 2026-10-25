-- Lemmas about quotient types (docs/proposals/map-equality.md §8.6-§8.8):
-- function extensionality, for functions whose results are data
-- (`Quot.funext`) and for functions whose results are proofs
-- (`Quot.funextProp`), and `Quot.exactDec`, which gets the relation back from
-- an equation between two `Quot.mk`s when the relation can be decided. Each
-- is proved from the kernel's quotient rules; the only axiom any of them uses
-- is `Quot.sound` (`stitchwort axioms Std.Quot.funext` lists it).
--
-- They're stated at `Type 0` (a domain `a: Type`, and so on): without
-- universe polymorphism a theorem is at one level. A module that needs one at
-- `Type 1` restates the same proof under a level-suffixed name
-- (`Quot.funext1`), §8.8.

-- Two functions agree at every input.
def Quot.Pointwise (a: Type) (b: a → Type) (f: (x: a) → b x) (g: (x: a) → b x): Prop :=
  (x: a) → f x = g x

-- Functions, with two identified when they agree at every input.
def Quot.Functions (a: Type) (b: a → Type): Type := Quot ((x: a) → b x) (Quot.Pointwise a b)

-- The class of functions `q` at the input `x`: agreeing functions agree there.
def Quot.evalAt (a: Type) (b: a → Type) (q: Quot.Functions a b) (x: a): b x :=
  Quot.lift [b := b x] (f => f x) (f g same => same x) q

-- A function back from a class of functions. On `Quot.mk f` it computes to
-- `x => f x`, which is `f` (functions are equal to their eta-expansions).
def Quot.rebuild (a: Type) (b: a → Type) (q: Quot.Functions a b): (x: a) → b x :=
  x => Quot.evalAt a b q x

-- Functions that agree at every input are equal (§8.7). `Quot.sound` says the
-- classes of `f` and `g` are equal, and rebuilding a function from each class
-- gives back `f` and `g`.
theorem Quot.funext (a: Type) (b: a → Type) (f: (x: a) → b x) (g: (x: a) → b x)
    (h: (x: a) → f x = g x): f = g :=
  Eq.cong (Quot.rebuild a b) (Quot.sound [x := f] [y := g] h)

-- A proof stored as data: a record with one field, `proof`. A function whose
-- results are proofs is itself a proof, so it can't be put in a quotient (a
-- quotient's elements are data); a function whose results are `ProofBox`es
-- can.
type ProofBox (p: Prop) = { proof: p }

-- Functions whose results are proofs, and that agree at every input, are
-- equal (§8.7). Box each result, use `Quot.funext` on the boxed functions,
-- then take the proofs back out of the boxes.
theorem Quot.funextProp (a: Type) (p: a → Prop) (f: (x: a) → p x) (g: (x: a) → p x)
    (h: (x: a) → f x = g x): f = g :=
  let boxF: (x: a) → ProofBox (p x) := x => { proof = f x }
  let boxG: (x: a) → ProofBox (p x) := x => { proof = g x }
  let pointwise: (x: a) → boxF x = boxG x :=
    x => J (q e => boxF x = ({ proof = q }: ProofBox (p x))) rfl (h x)
  let boxes: boxF = boxG := Quot.funext a (x => ProofBox (p x)) boxF boxG pointwise
  J (k e => f = (x => (k x).proof)) rfl boxes

-- Booleans that are `True` together are equal.
theorem Quot.boolEq: (b: Bool) → (c: Bool) → (b = True → c = True) → (c = True → b = True) → b = c
  | False, False, toC, toB => rfl
  | False, True, toC, toB => toB rfl
  | True, False, toC, toB => Eq.sym (toC rfl)
  | True, True, toC, toB => rfl

-- If `r` decides `rel`, and `rel` is an equivalence, then `Quot.mk x` and
-- `Quot.mk y` are equal only when `x` and `y` are related (§8.6). Fix `x`;
-- `z => r x z` gives the same answer on related inputs, so it lifts to the
-- quotient; applied to both sides of the equation it gives `r x x = r x y`,
-- and `r x x` is `True`. It proves an equation between `Bool`s, never
-- between propositions, so it needs no more than the quotient rules.
theorem Quot.exactDec (a: Type) (rel: a → a → Prop) (r: a → a → Bool)
    (decides: (x: a) → (y: a) → Iff (r x y = True) (rel x y))
    (refl: (x: a) → rel x x)
    (symm: (x: a) → (y: a) → rel x y → rel y x)
    (trans: (x: a) → (y: a) → (z: a) → rel x y → rel y z → rel x z)
    (x: a) (y: a) (same: (Quot.mk x: Quot a rel) = Quot.mk y): rel x y :=
  let respects: (y: a) → (z: a) → rel y z → r x y = r x z :=
    y z related => Quot.boolEq (r x y) (r x z)
      (xy => (decides x z).backward (trans x y z ((decides x y).forward xy) related))
      (xz => (decides x y).backward (trans x z y ((decides x z).forward xz) (symm y z related)))
  let classify: Quot a rel → Bool := q => Quot.lift (z => r x z) respects q
  let computed: r x x = r x y := Eq.cong classify same
  (decides x y).forward (Eq.trans (Eq.sym computed) ((decides x x).backward (refl x)))
