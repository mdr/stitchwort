import Std (Eq, Nat)

-- The programs of sealed.sw with the seals off: all check today.
opaque def seal: Nat := 0

theorem flippedS ∀ [a: Type] [x y: a] (p: x = y): y = x := J (y' p' => y' = x) byComputing p
theorem transS ∀ [a: Type] [x y z: a] (p: x = y) (q: y = z): x = z := J (z' q' => x = z') p q
theorem addZeroS ∀ (n: Nat): n + 0 = n := match n with
  | Zero => byComputing
  | Succ m => Eq.cong Succ (addZeroS m)
theorem bothS: 1 = 1 ∧ 2 = 2 := Both byComputing byComputing
theorem bothS2: 1 = 1 ∧ 2 = 2 := Both (Eq.flipped byComputing) byComputing
theorem leftS ∀ [p q: Prop] (h: p ∧ q): p := match h with | Both l r => l

-- 1. Proofs that rewrite with sealed lemmas, or chain them.
theorem useRewrite ∀ (n m: Nat) (h: m = n + 0): n = m := rewrite h then flippedS (addZeroS n)
theorem useRewriteBack ∀ (n m: Nat) (h: n + 0 = m): m = n := rewrite <- h then addZeroS n
theorem useTrans ∀ (n m: Nat) (h: n = m): n + 0 = m := transS (addZeroS n) h

-- 2. Data moved along a sealed proof, then computed with.
def castNat (n x: Nat): Nat := J (y p => Nat) x (flippedS (addZeroS n))
theorem castComputes: castNat 3 5 = 5 := byComputing

-- 3. A sealed conjunction taken apart inside a proof.
theorem useLeft: 1 = 1 := leftS bothS
theorem useMatch: 2 = 2 := match bothS with | Both l r => r

-- 4. A conjunction taken apart into data, then computed with.
def pick (h: 1 = 1 ∧ 2 = 2) (x: Nat): Nat := match h with | Both l r => x
theorem pickComputes: pick bothS 5 = 5 := byComputing

-- 5. Two sealed proofs compared where the function computes with its proof.
def through (h: 1 = 1) (x: Nat): Nat := J (y p => Nat) x h
theorem sameProofs: through (leftS bothS) 5 = through (leftS bothS2) 5 := byComputing

-- 6. Two sealed proofs compared at a proof position (a record's proof field).
type Small = { value: Nat, ok: 1 = 1 }
theorem sameRecords: ({ value = 3, ok = leftS bothS }: Small) = { value = 3, ok = leftS bothS2 } := byComputing

-- 7. A statement about proofs themselves.
theorem proofsEqual: leftS bothS = leftS bothS2 := byComputing

-- With a variable, the cast is stuck even today: the lemma's proof is by induction.
def castTo (n x: Nat): Nat := J (y p => Nat) x (Eq.flipped (Nat.addZero n))
theorem closedCast: castTo 3 5 = 5 := byComputing
-- theorem openCast ∀ (n: Nat): castTo n 5 = 5 := byComputing   -- E-REFL
