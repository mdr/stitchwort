-- An opaque function is equal to its eta wrapper, written as a lambda or as
-- a visible definition, outside any `unfolding` set: eta is conversion, not
-- unfolding. Both directions, partial applications, and through unification.

opaque def f (n: Nat): Nat := n + 1
opaque def g2 (a b: Nat): Nat := a + b
def w (n: Nat): Nat := f n
def w2 (a b: Nat): Nat := g2 a b
type Holder (h: Nat → Nat) = | MkHolder

theorem etaLam: f = (x => f x) := byComputing
theorem etaDef: f = w := byComputing
theorem etaDefFlip: w = f := byComputing
theorem etaPartial ∀ (a: Nat): g2 a = (x => g2 a x) := byComputing
theorem etaPartialDef ∀ (a: Nat): g2 a = w2 a := byComputing
theorem etaPartialDef2: g2 = w2 := byComputing

def unified (x: Holder f): Holder w := x
def unified2 (x: Holder w): Holder (y => f y) := x
def viaVar (h: Nat → Nat) (e: h = f) (x: Holder h): Holder w := J (m _ => Holder m) x e

-- Inside the unfolding set the body is visible too.
theorem inLam: f = (x => f x) unfolding f := byComputing
theorem inDef: f = w unfolding f := byComputing
theorem inBody: f = (x => x + 1) unfolding f := byComputing
theorem inPartial ∀ (a: Nat): g2 a = (x => a + x) unfolding g2 := byComputing
