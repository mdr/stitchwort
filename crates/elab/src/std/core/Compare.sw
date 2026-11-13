--| The laws of comparison for `Ordering`, `Nat` and `Int`:
--| `compareEqual`, `compareFlip`, `compareTrans`, and `less`/`le` from
--| `compare`.
-- Loaded with the core: Each `Ord` instance needs its `compare` laws, and `Ord`
-- instances are in the core (docs/proposals/prelude-slim.md §2.1).

-- Orderings (docs/proposals/interfaces.md §6.2)

--| The comparison the other way round.
def Ordering.flip: (ordering: Ordering) → Ordering
  | Less => Greater
  | Equal => Equal
  | Greater => Less

theorem Ordering.lessNotEqual: Less ≠ Equal
  | p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p)

theorem Ordering.lessNotGreater: Less ≠ Greater
  | p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p)

theorem Ordering.equalNotLess: Equal ≠ Less
  | p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p))

theorem Ordering.equalNotGreater: Equal ≠ Greater
  | p => Nat.zeroNotSucc 0 (Nat.succInjective (Eq.cong Ordering.index p))

theorem Ordering.greaterNotLess: Greater ≠ Less
  | p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p))

theorem Ordering.greaterNotEqual: Greater ≠ Equal
  | p => Nat.zeroNotSucc 0 (Nat.succInjective (Eq.sym (Eq.cong Ordering.index p)))

theorem Ordering.indexInjective (c d: Ordering) (h: Ordering.index c = Ordering.index d): c = d := match c, d with
  | Less, Less => rfl
  | Less, Equal => Void.exfalso (Nat.zeroNotSucc 0 h)
  | Less, Greater => Void.exfalso (Nat.zeroNotSucc 1 h)
  | Equal, Less => Void.exfalso (Nat.succNotZero 0 h)
  | Equal, Equal => rfl
  | Equal, Greater => Void.exfalso (Nat.zeroNotSucc 0 (Nat.succInjective h))
  | Greater, Less => Void.exfalso (Nat.succNotZero 1 h)
  | Greater, Equal => Void.exfalso (Nat.succNotZero 0 (Nat.succInjective h))
  | Greater, Greater => rfl

theorem Ordering.andThenEqual (c d: Ordering) (h: Ordering.andThen c d = Equal): (c = Equal) ∧ (d = Equal) :=
  match c with
    | Equal => Both rfl h

theorem Ordering.flipAndThen (c d: Ordering):
    Ordering.flip (Ordering.andThen c d) = Ordering.andThen (Ordering.flip c) (Ordering.flip d) := match c with
      | Less => rfl
      | Equal => rfl
      | Greater => rfl

--| `Less` is transitive for `c1` then `r1` (lexicographic), given that it
--| is for the first comparisons and for the rest, and that an `Equal` first
--| comparison passes the other one on.
theorem Ordering.andThenTrans (c1 c2 c3 r1 r2 r3: Ordering)
    (t: c1 = Less → c2 = Less → c3 = Less) (e1: c1 = Equal → c3 = c2) (e2: c2 = Equal → c3 = c1)
    (tr: r1 = Less → r2 = Less → r3 = Less)
    (h1: Ordering.andThen c1 r1 = Less) (h2: Ordering.andThen c2 r2 = Less): Ordering.andThen c3 r3 = Less :=
  match c1, c2 with
    | Less, Less => rewrite t rfl rfl in rfl
    | Less, Equal => rewrite e2 rfl in rfl
    | Equal, Less => rewrite e1 rfl in rfl
    | Equal, Equal => rewrite e1 rfl in tr h1 h2

-- `Nat.compare` steps down both numbers together, so its laws are proved by
-- recursion on both.
theorem Nat.compareSucc (m: Nat) (n: Nat): Nat.compare (Succ m) (Succ n) = Nat.compare m n := rfl

theorem Nat.compareEqual (m n: Nat) (h: Nat.compare m n = Equal): m = n := match m, n with
  | Zero, Zero => rfl
  | Succ m, Succ n => Eq.cong Succ (Nat.compareEqual m n h)

theorem Nat.compareFlip (m n: Nat): Nat.compare n m = Ordering.flip (Nat.compare m n) := match m, n with
  | Zero, Zero => rfl
  | Zero, Succ n => rfl
  | Succ m, Zero => rfl
  | Succ m, Succ n => Nat.compareFlip m n

theorem Nat.compareTrans (x y z: Nat)
    (h1: Nat.compare x y = Less) (h2: Nat.compare y z = Less): Nat.compare x z = Less := match x, y, z with
      | Zero, Succ y, Succ z => rfl
      | Succ x, Succ y, Succ z => Nat.compareTrans x y z h1 h2

theorem Nat.lessOfCompare (m n: Nat) (h: Nat.compare m n = Less): m < n := match m, n with
  | Zero, Succ n => rfl
  | Succ m, Succ n => Nat.lessOfCompare m n h

theorem Nat.compareOfLess (m n: Nat) (h: m < n): Nat.compare m n = Less := match m, n with
  | Zero, Succ n => rfl
  | Succ m, Succ n => Nat.compareOfLess m n h

theorem Nat.leOfCompare (m n: Nat) (h: Nat.compare m n ≠ Greater): m ≤ n := match m, n with
  | Zero, n => rfl
  | Succ m, Zero => Void.exfalso (h rfl)
  | Succ m, Succ n => Nat.leOfCompare m n h

theorem Nat.compareOfLe: ∀ (m n: Nat) => m ≤ n → Nat.compare m n ≠ Greater
  | Zero, Zero, h, e => Ordering.equalNotGreater e
  | Zero, Succ n, h, e => Ordering.lessNotGreater e
  | Succ m, Zero, h, e => Bool.falseNotTrue h
  | Succ m, Succ n, h, e => Nat.compareOfLe m n h e

--| A number at least `Succ k` isn't 0: how `auto` proves `d ≠ 0` from a fact
--| `0 < d` in scope.
theorem Nat.nonzeroOfSuccLe: ∀ (k d: Nat) => Succ k ≤ d → d ≠ 0
  | k, Zero, h, e => Bool.falseNotTrue h
  | k, Succ d, h, e => Nat.succNotZero d e

theorem Int.compareEqual (a b: Int) (h: Int.compare a b = Equal): a = b := match a, b with
  | OfNat m, OfNat n => Eq.cong OfNat (Nat.compareEqual m n h)
  | NegSucc m, NegSucc n => Eq.cong NegSucc (Eq.sym (Nat.compareEqual n m h))

theorem Int.compareFlip (a b: Int): Int.compare b a = Ordering.flip (Int.compare a b) := match a, b with
  | OfNat m, OfNat n => Nat.compareFlip m n
  | OfNat m, NegSucc n => rfl
  | NegSucc m, OfNat n => rfl
  | NegSucc m, NegSucc n => Nat.compareFlip n m

theorem Int.compareTrans (a b c: Int)
    (h1: Int.compare a b = Less) (h2: Int.compare b c = Less): Int.compare a c = Less := match a, b, c with
      | OfNat x, OfNat y, OfNat z => Nat.compareTrans x y z h1 h2
      | NegSucc x, OfNat y, OfNat z => rfl
      | NegSucc x, NegSucc y, OfNat z => rfl
      | NegSucc x, NegSucc y, NegSucc z => Nat.compareTrans z y x h2 h1

theorem Int.lessOfCompare (a b: Int) (h: Int.compare a b = Less): Int.LessThan a b := match a, b with
  | OfNat m, OfNat n => Nat.lessOfCompare m n h
  | NegSucc m, OfNat n => rfl
  | NegSucc m, NegSucc n => Nat.lessOfCompare n m h

theorem Int.compareOfLess (a b: Int) (h: Int.LessThan a b): Int.compare a b = Less := match a, b with
  | OfNat m, OfNat n => Nat.compareOfLess m n h
  | NegSucc m, OfNat n => rfl
  | NegSucc m, NegSucc n => Nat.compareOfLess n m h

theorem Int.leOfCompare (a b: Int) (h: Int.compare a b ≠ Greater): Int.LessEq a b := match a, b with
  | OfNat m, OfNat n => Nat.leOfCompare m n h
  | OfNat m, NegSucc n => Void.exfalso (h rfl)
  | NegSucc m, OfNat n => rfl
  | NegSucc m, NegSucc n => Nat.leOfCompare n m h

theorem Int.compareOfLe: ∀ (a b: Int) => Int.LessEq a b → Int.compare a b ≠ Greater
  | OfNat m, OfNat n, h, e => Nat.compareOfLe m n h e
  | OfNat m, NegSucc n, h, e => Bool.falseNotTrue h
  | NegSucc m, OfNat n, h, e => Ordering.lessNotGreater e
  | NegSucc m, NegSucc n, h, e => Nat.compareOfLe n m h e
