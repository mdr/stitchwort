--| `Ordering`, [`Nat.compare`], and the combinators `andThen`
--| and `index` with decidable equality.
-- Loaded with the core: Every `Ord` instance compares to an `Ordering`, and
-- `deriving (Ord)` writes `Ordering.andThen` in full
-- (docs/proposals/prelude-slim.md §2.1).

-- Comparisons

--| The result of comparing two values: `Less`, `Equal` or `Greater`.
type Ordering: Type = | Less | Equal | Greater

--| How `m` compares with `n`: `Nat.compare 2 5` is `Less`.
def Nat.compare (m n: Nat): Ordering := if Nat.equal m n then Equal else (if Nat.leq m n then Less else Greater)

--| The first comparison, unless it's `Equal`.
def Ordering.andThen: (first: Ordering) → (second: Ordering) → Ordering
  | Less, second => Less
  | Equal, second => second
  | Greater, second => Greater

--| The position of an ordering: 0 for `Less`, 1 for `Equal`, 2 for `Greater`.
def Ordering.index: (ordering: Ordering) → Nat
  | Less => 0
  | Equal => 1
  | Greater => 2

--| Decides whether two orderings are equal.
def Ordering.decEq: (a: Ordering) → (b: Ordering) → Decidable (a = b)
  | Less, Less => Decidable.yes rfl
  | Less, Equal => Decidable.no (p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p))
  | Less, Greater => Decidable.no (p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p))
  | Equal, Less => Decidable.no (p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p)))
  | Equal, Equal => Decidable.yes rfl
  | Equal, Greater => Decidable.no (p => Nat.zeroNotSucc 0 (Nat.succInjective (Eq.cong Ordering.index p)))
  | Greater, Less => Decidable.no (p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p)))
  | Greater, Equal => Decidable.no (p => Nat.zeroNotSucc 0 (Nat.succInjective (Eq.sym (Eq.cong Ordering.index p))))
  | Greater, Greater => Decidable.yes rfl
