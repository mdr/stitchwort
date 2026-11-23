-- Probe for docs/proposals/full-proof-irrelevance.md: each declaration here is
-- refused today (the error is in the note's table) and would check under E2.
-- Checked one declaration at a time: an error in one doesn't hide the next.
import Std (Eq, Nat)

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

-- 1. Two bare proofs.
theorem bare ∀ (a: Prop) (p q: a): p = q := byComputing

-- 2. A proof passed to a local function.
theorem underLocal ∀ (a: Prop) (f: a → Nat) (p q: a): f p = f q := byComputing

-- 3. A cast along a proof variable whose ends are the same (rule K).
def cast (a b: Type) (h: a = b) (x: a): b := J (y e => y) x h

theorem castAny ∀ (a: Type) (h: a = a) (x: a): cast a a h x = x := byComputing

-- 4. A cast along a lemma, for every `n` (rule K; no look inside the lemma).
theorem addZero ∀ (n: Nat): n + 0 = n := match n with
  | Zero => byComputing
  | Succ m => Eq.cong Succ (addZero m)

def castNat (n x: Nat): Nat := J (y p => Nat) x (Eq.flipped (addZero n))

theorem castNatOpen ∀ (n: Nat): castNat n 5 = 5 := byComputing

-- 5. A match on an unknown one-shape proof producing data (rule S).
type Both (a b: Prop): Prop = | MkBoth (l: a) (r: b)

def pick (a b: Prop) (h: Both a b) (n: Nat): Nat := match h with | MkBoth l r => n

theorem pickAny ∀ (a b: Prop) (h: Both a b): pick a b h 3 = 3 := byComputing

-- 6. The subject-reduction gap of proof-irrelevance.md section 5.7: `castOk`
-- checks today at `f q` and computes to `x`, which is refused at `f q`.
def inlined (a: Prop) (p q: a) (f: a → Type) (x: f p): f q := x

-- 7. Two unboxed proofs.
theorem unboxBoth ∀ (a: Prop) (p q: a): Box.unbox (MkBox p) = Box.unbox (MkBox q) := byComputing

-- 8. Equal for every `n` today (`underStuck` in checks-today.sw), but not at
-- `n = 1`: there `depth` takes the box apart and `J` is stuck on two different
-- proof variables.
def depth (b: Box (0 = 0)) (n: Nat): Nat := match n with
  | Zero => 0
  | Succ m =>
    match b with
      | MkBox h => J (y e => Nat) m h

theorem atOne ∀ (p q: 0 = 0): depth (MkBox p) 1 = depth (MkBox q) 1 := byComputing

-- 9. A proof field under a call whose body is hidden: compared in today's
-- shortcut mode, which looks at proof fields.
opaque def secret (b: Box (0 = 0)): Nat := 0

theorem underHidden ∀ (p q: 0 = 0): secret (MkBox p) = secret (MkBox q) := byComputing
