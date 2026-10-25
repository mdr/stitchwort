-- Indexed data types (docs/proposals/indexed-families.md §8). Each reject/
-- index-*.sw example is paired with a definition here.

import Std (Nat)

-- Vectors: a list whose length is in its type. `n` in `VCons` is an
-- implicit field, bound automatically.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

-- No `VNil` arm: it can't happen (paired with reject/index-declared-plus-one.sw).
def head: Vec a (Succ n) → a
  | VCons x _ => x

def tail: Vec a (Succ n) → Vec a n
  | VCons _ xs => xs

def map (f: a → b): Vec a n → Vec b n
  | VNil => VNil
  | VCons x xs => VCons (f x) (map f xs)

-- The second vector's length is the first's (paired with
-- reject/index-missing-arm.sw).
def zipWith (f: a → b → c): Vec a n → Vec b n → Vec c n
  | VNil, VNil => VNil
  | VCons x xs, VCons y ys => VCons (f x y) (zipWith f xs ys)

-- `+` counts down its first argument, so the goals compute (paired with
-- reject/index-stuck-plus.sw).
def append: Vec a n → Vec a m → Vec a (n + m)
  | VNil, ys => ys
  | VCons x xs, ys => VCons x (append xs ys)

-- The same stuck length becomes matchable once `n` is matched.
def lengthOfSum: (n: Nat) → Vec a (n + m) → Nat
  | Zero, VNil => 0
  | Zero, VCons _ _ => 1
  | Succ _, VCons _ _ => 2

def replicate: (n: Nat) → a → Vec a n
  | Zero, _ => VNil
  | Succ k, x => VCons x (replicate k x)

def toList: Vec a n → List a
  | VNil => Nil
  | VCons x xs => Cons x (toList xs)

-- An implicit field, by name: in a value and in a pattern.
def length: Vec a n → Nat
  | VNil => 0
  | VCons [n := k] _ _ => Succ k

def consZero (xs: Vec Nat 2): Vec Nat 3 := VCons [n := 2] 0 xs

-- Numbers below `n`.
type Fin: Nat → Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

-- No `VNil` arm: `VNil` is possible, but then `i: Fin 0` has no values.
def get: Vec a n → Fin n → a
  | VCons x _, FZero => x
  | VCons _ xs, FSucc i => get xs i

-- An outer hypothesis is refined in a branch: `h: p (Succ m)` under
-- `VCons`, through a `match` that isn't the whole body too.
def same (x: t): t := x

def keep (p: Nat → Type) (h: p n) (v: Vec a n): p n :=
  same (match v with
    | VNil => h
    | VCons _ _ => h)

-- A dependent automatic field written out (paired with
-- reject/implicit-field-dependent.sw).
type Dep: (n: Nat) → Fin n → Type =
  | Mk (n: Nat) [i: Fin n]: Dep n i

-- Types as indices live one universe up (paired with
-- reject/index-type-former.sw): matching works on a variable index.
type Ty: Type → Type 1 =
  | TNat: Ty Nat
  | TList (t: Ty b): Ty (List b)

def depth: Ty c → Nat
  | TNat => 0
  | TList t => Succ (depth t)

-- `Le` as an inductive predicate.
type Le: Nat → Nat → Prop =
  | LeZero: Le 0 n
  | LeSucc (h: Le m n): Le (Succ m) (Succ n)

theorem leTrans: Le a b → Le b c → Le a c
  | LeZero, _ => LeZero
  | LeSucc h1, LeSucc h2 => LeSucc (leTrans h1 h2)

theorem leToLeq: Le m n → m ≤ n
  | LeZero => Nat.zeroLe n
  | LeSucc h => leToLeq h

-- A proof with every branch impossible can produce data.
def absurdLe: Le (Succ n) 0 → Nat
  | ()

-- `Even`, an absurd case, and a decision procedure (paired with
-- reject/index-absurd-not-empty.sw).
type Even: Nat → Prop =
  | EvenZero: Even 0
  | EvenTwo (h: Even n): Even (Succ (Succ n))

theorem notEvenOne: Not (Even 1)
  | ()

theorem evenInv: Even (Succ (Succ n)) → Even n
  | EvenTwo h => h

instance decEven: (n: Nat) → Decidable (Even n)
  | 0 => Yes EvenZero
  | 1 => No notEvenOne
  | Succ (Succ k) => match decEven k with
    | Yes h => Yes (EvenTwo h)
    | No r => No (h => r (evenInv h))

-- Defined together, each with its own indices.
type EvenM: Nat → Prop =
  | EvenMZero: EvenM 0
  | EvenMSucc (h: OddM n): EvenM (Succ n)

type OddM: Nat → Prop =
  | OddMSucc (h: EvenM n): OddM (Succ n)

theorem notOddZero: Not (OddM 0)
  | ()

-- Axiom K: matching deletes the equation `x = x`.
type Same (a: Type) (x: a): a → Prop =
  | Refl: Same a x x

theorem sameK (p: Same a x x): p = Refl := match p with
  | Refl => rfl

def vec12: Vec Nat 2 := VCons 1 (VCons 2 VNil)

test "head" := head vec12 == 1
test "tail" := head (tail vec12) == 2
test "map" := toList (map (x => x * 10) vec12) == [10, 20]
test "zipWith" := toList (zipWith (x y => x + y) vec12 vec12) == [2, 4]
test "append" := toList (append vec12 (consZero vec12)) == [1, 2, 0, 1, 2]
test "replicate" := toList (replicate 3 7) == [7, 7, 7]
test "length" := length (consZero vec12) == 3
test "get" := get vec12 (FSucc FZero) == 2
test "depth" := depth (TList (TList TNat)) == 2
def isEven (n: Nat): Bool := match decEven n with
  | Yes _ => True
  | No _ => False

test "decEven" := isEven 10 ∧ not (isEven 7)
