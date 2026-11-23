-- Rules K and S where tests nest or refine: a cast's test inside another's,
-- a match on a proof whose type a match on its index refined, an equation
-- with two indices, and a cast into data along the Abel-Coquand loop.
import Std (Nat, Eq)

def castFn (f g: Nat → Nat) (h: f = g) (n: Nat): Nat := J (y e => Nat) n h

-- The inner cast's ends agree under the outer test's fresh variable `z`.
theorem nestedOk ∀
    (hyp: ∀ (z: Nat) => ((w: Nat) => z) = ((w: Nat) => z))
    (h: ((z: Nat) => castFn (w => z) (w => z) (hyp z) 7) = ((z: Nat) => 7)):
    castFn (z => castFn (w => z) (w => z) (hyp z) 7) (z => 7) h 1 = 1 :=
  byComputing

type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x

-- `h`'s type mentions `x`, which the outer match refines to `0`.
def carry2 (x y: Nat) (h: Same Nat x y) (n: Nat): Nat := match x with
  | Zero =>
    (match h with
      | MkSame => n)
  | Succ k => n

theorem refinedOk ∀ (h: Same Nat 0 0): carry2 0 0 h 4 = 4 := byComputing

type HEq (a: Type) (x: a): (b: Type) → b → Prop = | HRefl: HEq a x a x

def hcast (a b: Type) (x: a) (y: b) (h: HEq a x b y) (n: Nat): Nat := match h with | HRefl => n

theorem twoIndicesOk ∀ (a: Type) (x: a) (h: HEq a x a x): hcast a a x x h 3 = 3 := byComputing

-- A cast into data whose proof is the looping term computes by its ends,
-- which agree; the loop's own cast is into a proposition and stays stuck.
def Bot: Prop := ∀ (a: Prop) => a
def Top: Prop := Bot → Bot
def delta: Top := z => z Top z
def omega: (∀ (a b: Prop) => a = b) → Bot := h a => J (y e => y) delta (h Top a)
def bigOmega: (∀ (a b: Prop) => a = b) → Bot := h => delta (omega h)

def viaLoop (h: ∀ (a b: Prop) => a = b) (n: Nat): Nat := J (y e => Nat) n (bigOmega h (0 = 0))

theorem viaLoopComputes ∀ (h: ∀ (a b: Prop) => a = b): viaLoop h 5 = 5 := byComputing
