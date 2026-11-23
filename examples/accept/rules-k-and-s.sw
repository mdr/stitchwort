-- Rules K and S (docs/core.md, "The equality rule"; stage 4 of
-- docs/proposals/full-proof-irrelevance.md): which proof a cast or a
-- one-constructor match into data is given never decides what it computes.
-- Each declaration here was refused (E-REFL) before them.
import Std (Eq, Nat)

-- Rule K: a cast along a proof variable whose ends are the same.
def cast (a b: Type) (h: a = b) (x: a): b := J (y e => y) x h

theorem castAny ∀ (a: Type) (h: a = a) (x: a): cast a a h x = x := byComputing

-- Rule K for every `n`, along a lemma that is never looked inside: the ends
-- `n` and `n + 0` are equal for every `n`.
theorem addZero ∀ (n: Nat): n + 0 = n := match n with
  | Zero => byComputing
  | Succ m => Eq.cong Succ (addZero m)

def castNat (n x: Nat): Nat := J (y p => Nat) x (Eq.flipped (addZero n))

theorem castNatOpen ∀ (n: Nat): castNat n 5 = 5 := byComputing

-- Along a theorem's proof that `And.left` takes apart, on numbers
-- (docs/reviews/SW-4665-fable-review.md): the ends `0` and `0` are equal.
def pickLeft (a b n: Nat): Nat := if h: (a = b) ∧ (b = 0) then J (x e => Nat) n h.left else 0

theorem pickLeftConcrete: pickLeft 0 0 5 = 5 := byComputing

-- Two stuck casts along different proofs of one equation are equal: they
-- are compared by their ends, motive and base, never by their proofs.
def castAt (x y: Nat) (h: x = y) (d: Nat): Nat := J (w e => Nat) d h

theorem sameEnds ∀ (x y: Nat) (h1 h2: x = y): castAt x y h1 3 = castAt x y h2 3 := byComputing

-- Rule S: a match into data on an unknown proof of a proposition with one
-- constructor, whose fields are proofs, takes its branch.
type Both (a b: Prop): Prop = | MkBoth (l: a) (r: b)

def pick (a b: Prop) (h: Both a b) (n: Nat): Nat := match h with | MkBoth l r => n

theorem pickAny ∀ (a b: Prop) (h: Both a b): pick a b h 3 = 3 := byComputing

-- Rule S for an indexed proposition whose constructor has no fields (D3724,
-- as Lean does): the branch is taken once the constructor's result indices
-- equal the scrutinee's, here `x` and `x`.
type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x

def carry (x y: Nat) (h: Same Nat x y) (n: Nat): Nat := match h with | MkSame => n

theorem carryRefl ∀ (x: Nat): carry x x MkSame 4 = 4 := byComputing

theorem carryAny ∀ (x: Nat) (h: Same Nat x x): carry x x h 4 = 4 := byComputing

-- Rule S for an indexed proposition whose constructor has proof fields
-- (D3727): the same index test, each field bound to the proof's field.
type Le2: Nat → Prop = | MkLe2 (p: 0 = 0): Le2 0

def withField (n: Nat) (h: Le2 n) (k: Nat): Nat := match h with | MkLe2 p => k

theorem withFieldAny ∀ (h: Le2 0): withField 0 h 4 = 4 := byComputing

-- The fields may mention the parameters, and the indices the fields: the
-- constructor's index `h` is read as the proof's field, equal to the
-- scrutinee's index by rule I.
type AtThree (a: Nat): Nat → Prop =
  | MkAtThree (h: a = 3) (k: 3 = a): AtThree a 0

def three (a: Nat): AtThree a 0 → Nat
  | MkAtThree h k => 5

theorem threeAny ∀ (a: Nat) (s: AtThree a 0): three a s = 5 := byComputing

type ByProof: (0 = 0) → Prop = | MkByProof (h: 0 = 0): ByProof h

def byProof (h: 0 = 0): ByProof h → Nat
  | MkByProof k => 5

theorem byProofAny ∀ (h: 0 = 0) (s: ByProof h): byProof h s = 5 := byComputing
