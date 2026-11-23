-- Rule S takes a match's branch on a proof field bound by an enclosing
-- match, as on a parameter (docs/reviews/SW-4686-fable-review.md, F1): the
-- field's type is its declared type over the enclosing scrutinee's
-- parameters and earlier fields, and its indices are the constructor's. So
-- conversion is transitive here too: `g o` is `5` for a variable `o`
-- (`a3`), as `a1` and `a2` together already said, and an instance of a
-- checked universal statement checks (`b1c`, `b1` at `k := 5`, where `po`
-- is a proof definition rule F freezes).
import Std (Eq, Nat)

type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0

type Outer: Prop = | MkOuter (q: Q2 0)

def g: Outer → Nat
  | MkOuter q =>
    match q with
      | MkQ2 w => 5

theorem a1 ∀ (o: Outer): g o = g (MkOuter (MkQ2 byComputing)) := byComputing

theorem a2: g (MkOuter (MkQ2 byComputing)) = 5 := byComputing

theorem a3 ∀ (o: Outer): g o = 5 := byComputing

theorem a4 ∀ (s: Q2 0): g (MkOuter s) = 5 := byComputing

def gk (k: Nat): Outer → Nat
  | MkOuter q =>
    match q with
      | MkQ2 w => k

def po: Outer := MkOuter (MkQ2 byComputing)

theorem b1 ∀ (k: Nat): gk k po = gk k (MkOuter (MkQ2 byComputing)) := byComputing

theorem b1c: gk 5 po = gk 5 (MkOuter (MkQ2 byComputing)) := byComputing

-- The field's type over the enclosing type's parameter, and a field two
-- matches deep.
type Around (k: Nat): Prop = | MkAround (q: Q2 k)

def ga (k: Nat): Around k → Nat
  | MkAround q =>
    match q with
      | MkQ2 w => 7

theorem c1 ∀ (o: Around 0): ga 0 o = 7 := byComputing

type Twice: Prop = | MkTwice (o: Outer)

def gt: Twice → Nat
  | MkTwice o =>
    match o with
      | MkOuter q =>
        match q with
          | MkQ2 w => 9

theorem c2 ∀ (t: Twice): gt t = 9 := byComputing

-- An enclosing record whose proof field's index is an earlier data field,
-- taken apart by iota on a literal (`c3`), and one whose proof field's index
-- is the record type's parameter, taken apart by record eta on an unknown
-- record (`c4`).
type Box = { n: Nat, q: Q2 n }

def gb: Box → Nat
  | { n, q } =>
    match q with
      | MkQ2 w => n + 1

theorem c3 ∀ (q: Q2 0): gb { n = 0, q } = 1 := byComputing

type BoxK (k: Nat) = { m: Nat, q: Q2 k }

def gbk (k: Nat): BoxK k → Nat
  | { m, q } =>
    match q with
      | MkQ2 w => m

theorem c4 ∀ (b: BoxK 0): gbk 0 b = b.m := byComputing
