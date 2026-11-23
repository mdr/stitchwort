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
