-- Rule S reads a parameter's type off the definition's type computed, not
-- as written (SW-4796; the SW-4793 review, finding 1): with `f`'s
-- signature behind a definition, `f 0 s` and `f 0 pf` compute to `5` as
-- `f 0 (MkQ2 byComputing)` does, and as example 39 has them for a signature
-- written out. The same holds through an opaque nickname the definitions
-- unfold, for a match on an enclosing match's field (example 42) whose
-- definition's type is a nickname, and for a field whose declared type is
-- one.
import Std (Eq, Nat)

type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0

def Reader: Type := (x: Nat) → Q2 x → Nat

def f: Reader
  | x, MkQ2 w => 5

def pf: Q2 0 := MkQ2 byComputing

theorem t3: f 0 (MkQ2 byComputing) = 5 := byComputing

theorem t4 ∀ (s: Q2 0): f 0 s = 5 := byComputing

theorem n1: f 0 pf = 5 := byComputing

opaque def Hidden: Type := (x: Nat) → Q2 x → Nat

opaque def h: Hidden unfolding Hidden
  | x, MkQ2 w => 5

opaque def useH (s: Q2 0): Nat unfolding h, Hidden := h 0 s

theorem u1: useH pf = 5 unfolding useH, h, Hidden := byComputing

theorem u2 ∀ (s: Q2 0): useH s = 5 unfolding useH, h, Hidden := byComputing

type Outer: Prop = | MkOuter (q: Q2 0)

def G: Type := Outer → Nat

def g: G
  | MkOuter q =>
    match q with
      | MkQ2 w => 5

theorem a3 ∀ (o: Outer): g o = 5 := byComputing

def Q20: Prop := Q2 0

type Outer2: Prop = | MkOuter2 (q: Q20)

def g2: Outer2 → Nat
  | MkOuter2 q =>
    match q with
      | MkQ2 w => 5

theorem a4 ∀ (o: Outer2): g2 o = 5 := byComputing

-- The calls as values, so the differential test compares the reference
-- evaluator's rule S with the kernel's on them.
def atPf: Nat := f 0 pf

def atLiteral: Nat := f 0 (MkQ2 byComputing)

def atOuter: Nat := g (MkOuter pf)

-- The nickname after a parameter, so the type is forced again once the
-- codomain is applied (the SW-4796 review, finding 1).
def Rest (x: Nat): Type := Q2 x → Nat

def f2: (x: Nat) → Rest x
  | x, MkQ2 w => 5

theorem r1: f2 0 pf = 5 := byComputing

theorem r2 ∀ (s: Q2 0): f2 0 s = 5 := byComputing

-- A recursive family: the type computes to a function type only after the
-- number is known, once per step.
def Fam: Nat → Type
  | 0 => Nat
  | Succ n => (q: Q2 0) → Fam n

def f4: Fam 2
  | MkQ2 w, MkQ2 v => 5

theorem r3: f4 pf pf = 5 := byComputing

theorem r4 ∀ (s t: Q2 0): f4 s t = 5 := byComputing

def atRest: Nat := f2 0 pf

def atFam: Nat := f4 pf pf
