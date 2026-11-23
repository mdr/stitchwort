-- The kernel's comparison skips proofs at proof positions: constructors'
-- proof fields, data types' proof parameters and the arguments a
-- definition never computes with (docs/proposals/proof-irrelevance.md).
-- These are the accepted partners of soundness/proof-irrelevance-*.sw,
-- whose comments name them.
import Std (Bool, Char, Fin, Int, Nat, Unit, Void)

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

-- The motivating programs: a divisor's proof, and a character's. `wrap` and
-- `remainder` take a proof that the divisor isn't 0 and never compute with it.
def wrap (x: Int) (d: Nat) [auto ok: d ≠ 0]: Nat := Int.modNat x d

def remainder (x d: Nat) [auto ok: d ≠ 0]: Nat := x % d

theorem sameMod ∀ (x: Int): wrap x 100 [ok := Nat.succNotZero 99] = wrap x 100 := byComputing

theorem charProof ∀ (p: Char.isScalar 97 = True): MkChar 97 p = 'a' := byComputing

theorem sameModLiteral ∀ (p q: 100 ≠ 0): wrap 7 100 [ok := p] = wrap 7 100 [ok := q] := byComputing

theorem sameModDivisor ∀ (x: Int) (d: Nat) (p q: d ≠ 0): wrap x d [ok := p] = wrap x d [ok := q] := byComputing

theorem sameNatMod ∀ (x: Nat) (p q: 100 ≠ 0): remainder x 100 [ok := p] = remainder x 100 [ok := q] := byComputing

-- Constructors' proof fields.
theorem boxEq ∀ (a: Prop) (p q: a): MkBox p = MkBox q := byComputing

theorem unitBoxes ∀ (p q: Unit): MkBox p = MkBox q := byComputing

theorem unboxComputes ∀ (a: Prop) (p: a): Box.unbox (MkBox p) = p := byComputing

type Checked: Type = | MkChecked (n: Nat) (ok: n = n)

theorem sortedLists ∀ (x: Nat) (p q: x = x): MkChecked x p = MkChecked x q := byComputing

type Exists (p: Nat → Prop): Prop = | MkEx (x: Nat) (h: p x)

def withProof (h: 1 = 1): Exists (n => n = n) := MkEx 1 h

theorem sameWitness ∀ (h1 h2: 1 = 1): withProof h1 = withProof h2 := byComputing

-- Data types' proof parameters, and proposition parameters.
type PBox (a: Prop) (h: a): Type = | MkPBox

theorem proofParameter ∀ (a: Prop) (p q: a): PBox a p = PBox a q := byComputing

type R (p: Prop): Type = | MkR

theorem sameProposition: R Unit = R Unit := byComputing

-- Proof irrelevance as a theorem, and the cast it allows.
theorem piViaBox ∀ (a: Prop) (p q: a): p = q := J (y e2 => p = Box.unbox y) byComputing (boxEq a p q)

def castViaBox (a: Prop) (p q: a) (f: a → Type) (x: f p) (e: MkBox p = MkBox q): f q := J (y e2 => f (Box.unbox y)) x e

def castOk (a: Prop) (p q: a) (f: a → Type) (x: f p): f q := castViaBox a p q f x byComputing

-- `J` computes on `byComputing`; into data, also on any proof whose equation's
-- two sides are equal (rule K, accept/proof-irrelevance-05-rule-k.sw).
def jAt (n: Nat) (h: n = n) (d: Nat): Nat := J (y e => Nat) d h

theorem jOnRfl ∀ (n d: Nat): jAt n byComputing d = d := byComputing

def cast (a b: Type) (h: a = b) (x: a): b := J (y e => y) x h

theorem castRflComputes ∀ (a: Type) (x: a): cast a a byComputing x = x := byComputing

-- A loop's proof exposed as a constructor: accepted, and computes. Here
-- `Prop.irrel` is a `def`, which unfolds; a theorem is sealed (D3722), so
-- `piViaBox` stays a call, and a `J` along it doesn't compute.
type Loop: Prop = | MkLoop (next: Loop)

def Loop.inv: Loop → Loop
  | MkLoop n => n

def Prop.irrel (a: Prop) (p q: a): p = q :=
  let e: MkBox p = MkBox q := byComputing
  J (y e2 => p = Box.unbox y) byComputing e

def Loop.expose (l: Loop): Loop := J (y e => Loop) (MkLoop (Loop.inv l)) (Prop.irrel Loop (MkLoop (Loop.inv l)) l)

theorem exposeComputes ∀ (l: Loop): Loop.expose l = MkLoop (Loop.inv l) := byComputing

-- Inert arguments: a proof only passed on, never computed with.
def fnEq (n: Nat) (h: Void → Void): (Nat → Nat) = (Nat → Nat) := match n with
  | Zero => byComputing
  | Succ m => byComputing

def applyAt (f: Nat → Nat) (x: Nat): Nat := f x

theorem afterJ ∀ (n: Nat) (u1 u2: Void → Void):
    applyAt (J (y e => y) (x => x) (fnEq n u1)) 3 = applyAt (J (y e => y) (x => x) (fnEq n u2)) 3 :=
  byComputing

def quietA (n: Nat) (h: 0 = 0): Nat := match n with
  | Zero => 0
  | Succ m => quietB m h

def quietB (n: Nat) (h: 0 = 0): Nat := match n with
  | Zero => 1
  | Succ m => quietA m h

theorem quietGroup ∀ (n: Nat) (p q: 0 = 0): quietB n p = quietB n q := byComputing

theorem finProofs ∀ (n i: Nat) (h1 h2: i < n): Fin.ofNatLt n i h1 = Fin.ofNatLt n i h2 := byComputing

def keep (d: Nat) (ok: d ≠ 0): Box (d ≠ 0) := MkBox ok

theorem keepBoth ∀ (d: Nat) (p q: d ≠ 0): keep d p = keep d q := byComputing

-- Past the arity: `g`'s proof is the computed function's argument.
def g (n: Nat): 0 = 0 → Bool := match n with
  | Zero => h => J (y e => Bool) True h
  | Succ m => g m

theorem gSteps ∀ (h: 0 = 0): g 1 h = g 0 h := byComputing

theorem gComputes: g 0 byComputing = True := byComputing

-- A hidden opaque call, its arguments the same.
opaque def ou [a: Prop] (b: Box a): a := Box.unbox b

theorem ouSame ∀ (a: Prop) (p: a): ou (MkBox p) = ou (MkBox p) := byComputing

-- `case`s with no possible branch are equal whatever their scrutinees, so
-- the comparison stays transitive.
def myAbsurd: Void → Nat
  | ()

theorem absurdProofs ∀ (p q: 0 ≠ 0): Void.absurd [a := Nat] (p byComputing) = Void.absurd [a := Nat] (q byComputing) :=
  byComputing

theorem absurdMine ∀ (q: 0 ≠ 0): Void.absurd [a := Nat] (q byComputing) = myAbsurd (q byComputing) := byComputing

theorem absurdTransitive ∀ (p q: 0 ≠ 0): Void.absurd [a := Nat] (p byComputing) = myAbsurd (q byComputing) :=
  byComputing

-- Index unification deletes modulo proof fields.
type T: Box (Unit ∨ Unit) → Type = | A: T (MkBox (Inl ()))

def useA: T (MkBox (Inr ())) → Nat
  | A => 0
