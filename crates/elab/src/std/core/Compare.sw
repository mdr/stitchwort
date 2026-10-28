-- core/Compare.sw. The laws of comparison for `Ordering`, `Nat` and `Int`:
-- `compareEqual`, `compareFlip`, `compareTrans`, and `less`/`le` from
-- `compare`. Loaded with the core: Each `Ord` instance needs its `compare`
-- laws, and `Ord` instances are in the core (docs/proposals/prelude-slim.md
-- §2.1).

-- Orderings (docs/proposals/interfaces.md §6.2)

-- The comparison the other way round.
def Ordering.flip: Ordering → Ordering
  | Less => Greater
  | Equal => Equal
  | Greater => Less

theorem Ordering.lessNotEqual: Not (Less = Equal)
  | p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p)

theorem Ordering.lessNotGreater: Not (Less = Greater)
  | p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p)

theorem Ordering.equalNotLess: Not (Equal = Less)
  | p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p))

theorem Ordering.equalNotGreater: Not (Equal = Greater)
  | p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.cong Ordering.index p))

theorem Ordering.greaterNotLess: Not (Greater = Less)
  | p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p))

theorem Ordering.greaterNotEqual: Not (Greater = Equal)
  | p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.sym (Eq.cong Ordering.index p)))

theorem Ordering.indexInjective: (c: Ordering) → (d: Ordering) → Ordering.index c = Ordering.index d → c = d
  | Less, Less, h => rfl
  | Less, Equal, h => Void.exfalso (Nat.zeroNotSucc 0 h)
  | Less, Greater, h => Void.exfalso (Nat.zeroNotSucc 1 h)
  | Equal, Less, h => Void.exfalso (Nat.succNotZero 0 h)
  | Equal, Equal, h => rfl
  | Equal, Greater, h => Void.exfalso (Nat.zeroNotSucc 0 (Nat.succInjective 0 1 h))
  | Greater, Less, h => Void.exfalso (Nat.succNotZero 1 h)
  | Greater, Equal, h => Void.exfalso (Nat.succNotZero 0 (Nat.succInjective 1 0 h))
  | Greater, Greater, h => rfl

theorem Ordering.andThenEqual: (c: Ordering) → (d: Ordering) → Ordering.andThen c d = Equal → And (c = Equal) (d = Equal)
  | Less, d, h => Void.exfalso (Ordering.lessNotEqual h)
  | Equal, d, h => Both rfl h
  | Greater, d, h => Void.exfalso (Ordering.greaterNotEqual h)

theorem Ordering.flipAndThen: (c: Ordering) → (d: Ordering) →
    Ordering.flip (Ordering.andThen c d) = Ordering.andThen (Ordering.flip c) (Ordering.flip d)
  | Less, d => rfl
  | Equal, d => rfl
  | Greater, d => rfl

-- `Less` is transitive for `c1` then `r1` (lexicographic), given that it
-- is for the first comparisons and for the rest, and that an `Equal` first
-- comparison passes the other one on.
theorem Ordering.andThenTrans: (c1: Ordering) → (c2: Ordering) → (c3: Ordering) →
    (r1: Ordering) → (r2: Ordering) → (r3: Ordering) →
    (c1 = Less → c2 = Less → c3 = Less) → (c1 = Equal → c3 = c2) → (c2 = Equal → c3 = c1) →
    (r1 = Less → r2 = Less → r3 = Less) →
    Ordering.andThen c1 r1 = Less → Ordering.andThen c2 r2 = Less → Ordering.andThen c3 r3 = Less
  | Less, Less, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite t rfl rfl in rfl
  | Less, Equal, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e2 rfl in rfl
  | Less, Greater, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Equal, Less, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e1 rfl in rfl
  | Equal, Equal, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e1 rfl in tr h1 h2
  | Equal, Greater, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Greater, c2, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)

-- `Nat.compare` steps down both numbers together, so its laws are proved by
-- recursion on both.
theorem Nat.compareSucc (m: Nat) (n: Nat): Nat.compare (Succ m) (Succ n) = Nat.compare m n := rfl

theorem Nat.compareEqual: (m: Nat) → (n: Nat) → Nat.compare m n = Equal → m = n
  | Zero, Zero, h => rfl
  | Zero, Succ n, h => Void.exfalso (Ordering.lessNotEqual h)
  | Succ m, Zero, h => Void.exfalso (Ordering.greaterNotEqual h)
  | Succ m, Succ n, h => Eq.cong Succ (Nat.compareEqual m n h)

theorem Nat.compareFlip: (m: Nat) → (n: Nat) → Nat.compare n m = Ordering.flip (Nat.compare m n)
  | Zero, Zero => rfl
  | Zero, Succ n => rfl
  | Succ m, Zero => rfl
  | Succ m, Succ n => Nat.compareFlip m n

theorem Nat.compareTrans: (x: Nat) → (y: Nat) → (z: Nat) →
    Nat.compare x y = Less → Nat.compare y z = Less → Nat.compare x z = Less
  | Zero, Zero, z, h1, h2 => Void.exfalso (Ordering.equalNotLess h1)
  | Zero, Succ y, Zero, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Zero, Succ y, Succ z, h1, h2 => rfl
  | Succ x, Zero, z, h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | Succ x, Succ y, Zero, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Succ x, Succ y, Succ z, h1, h2 => Nat.compareTrans x y z h1 h2

theorem Nat.lessOfCompare: (m: Nat) → (n: Nat) → Nat.compare m n = Less → m < n
  | Zero, Zero, h => Void.exfalso (Ordering.equalNotLess h)
  | Zero, Succ n, h => rfl
  | Succ m, Zero, h => Void.exfalso (Ordering.greaterNotLess h)
  | Succ m, Succ n, h => Nat.lessOfCompare m n h

theorem Nat.compareOfLess: (m: Nat) → (n: Nat) → m < n → Nat.compare m n = Less
  | m, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Zero, Succ n, h => rfl
  | Succ m, Succ n, h => Nat.compareOfLess m n h

theorem Nat.leOfCompare: (m: Nat) → (n: Nat) → Not (Nat.compare m n = Greater) → m ≤ n
  | Zero, n, h => rfl
  | Succ m, Zero, h => Void.exfalso (h rfl)
  | Succ m, Succ n, h => Nat.leOfCompare m n h

theorem Nat.compareOfLe: (m: Nat) → (n: Nat) → m ≤ n → Not (Nat.compare m n = Greater)
  | Zero, Zero, h, e => Ordering.equalNotGreater e
  | Zero, Succ n, h, e => Ordering.lessNotGreater e
  | Succ m, Zero, h, e => Bool.falseNotTrue h
  | Succ m, Succ n, h, e => Nat.compareOfLe m n h e

-- A number at least `Succ k` isn't 0: how `auto` proves `d ≠ 0` from a fact
-- `0 < d` in scope.
theorem Nat.nonzeroOfSuccLe: (k: Nat) → (d: Nat) → Succ k ≤ d → Not (d = 0)
  | k, Zero, h, e => Bool.falseNotTrue h
  | k, Succ d, h, e => Nat.succNotZero d e

theorem Int.compareEqual: (a: Int) → (b: Int) → Int.compare a b = Equal → a = b
  | OfNat m, OfNat n, h => Eq.cong OfNat (Nat.compareEqual m n h)
  | OfNat m, NegSucc n, h => Void.exfalso (Ordering.greaterNotEqual h)
  | NegSucc m, OfNat n, h => Void.exfalso (Ordering.lessNotEqual h)
  | NegSucc m, NegSucc n, h => Eq.cong NegSucc (Eq.sym (Nat.compareEqual n m h))

theorem Int.compareFlip: (a: Int) → (b: Int) → Int.compare b a = Ordering.flip (Int.compare a b)
  | OfNat m, OfNat n => Nat.compareFlip m n
  | OfNat m, NegSucc n => rfl
  | NegSucc m, OfNat n => rfl
  | NegSucc m, NegSucc n => Nat.compareFlip n m

theorem Int.compareTrans: (a: Int) → (b: Int) → (c: Int) →
    Int.compare a b = Less → Int.compare b c = Less → Int.compare a c = Less
  | OfNat x, OfNat y, OfNat z, h1, h2 => Nat.compareTrans x y z h1 h2
  | OfNat x, OfNat y, NegSucc z, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | OfNat x, NegSucc y, c, h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | NegSucc x, OfNat y, OfNat z, h1, h2 => rfl
  | NegSucc x, OfNat y, NegSucc z, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | NegSucc x, NegSucc y, OfNat z, h1, h2 => rfl
  | NegSucc x, NegSucc y, NegSucc z, h1, h2 => Nat.compareTrans z y x h2 h1

theorem Int.lessOfCompare: (a: Int) → (b: Int) → Int.compare a b = Less → Int.LessThan a b
  | OfNat m, OfNat n, h => Nat.lessOfCompare m n h
  | OfNat m, NegSucc n, h => Void.exfalso (Ordering.greaterNotLess h)
  | NegSucc m, OfNat n, h => rfl
  | NegSucc m, NegSucc n, h => Nat.lessOfCompare n m h

theorem Int.compareOfLess: (a: Int) → (b: Int) → Int.LessThan a b → Int.compare a b = Less
  | OfNat m, OfNat n, h => Nat.compareOfLess m n h
  | OfNat m, NegSucc n, h => Void.exfalso (Bool.falseNotTrue h)
  | NegSucc m, OfNat n, h => rfl
  | NegSucc m, NegSucc n, h => Nat.compareOfLess n m h

theorem Int.leOfCompare: (a: Int) → (b: Int) → Not (Int.compare a b = Greater) → Int.LessEq a b
  | OfNat m, OfNat n, h => Nat.leOfCompare m n h
  | OfNat m, NegSucc n, h => Void.exfalso (h rfl)
  | NegSucc m, OfNat n, h => rfl
  | NegSucc m, NegSucc n, h => Nat.leOfCompare n m h

theorem Int.compareOfLe: (a: Int) → (b: Int) → Int.LessEq a b → Not (Int.compare a b = Greater)
  | OfNat m, OfNat n, h, e => Nat.compareOfLe m n h e
  | OfNat m, NegSucc n, h, e => Bool.falseNotTrue h
  | NegSucc m, OfNat n, h, e => Ordering.lessNotGreater e
  | NegSucc m, NegSucc n, h, e => Nat.compareOfLe n m h e
