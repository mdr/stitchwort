-- core/Ordering.sw. `Ordering`, `Nat.compare`, and the combinators `andThen`
-- and `index` with decidable equality. Loaded with the core: Every `Ord`
-- instance compares to an `Ordering`, and `deriving (Ord)` writes
-- `Ordering.andThen` in full (docs/proposals/prelude-slim.md §2.1).

-- Comparisons

type Ordering: Type =
  | Less
  | Equal
  | Greater

def Nat.compare (m: Nat) (n: Nat): Ordering := if Nat.equal m n then Equal else (if Nat.leq m n then Less else Greater)

-- The first comparison, unless it's `Equal`.
def Ordering.andThen: Ordering -> Ordering -> Ordering
  | Less,    o => Less
  | Equal,   o => o
  | Greater, o => Greater

def Ordering.index: Ordering -> Nat
  | Less    => 0
  | Equal   => 1
  | Greater => 2

def Ordering.decEq: (a: Ordering) -> (b: Ordering) -> Decidable (a = b)
  | Less,    Less    => Yes rfl
  | Less,    Equal   => No (p => Nat.zeroNotSucc 0 (Eq.cong Ordering.index p))
  | Less,    Greater => No (p => Nat.zeroNotSucc 1 (Eq.cong Ordering.index p))
  | Equal,   Less    => No (p => Nat.zeroNotSucc 0 (Eq.sym (Eq.cong Ordering.index p)))
  | Equal,   Equal   => Yes rfl
  | Equal,   Greater => No (p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.cong Ordering.index p)))
  | Greater, Less    => No (p => Nat.zeroNotSucc 1 (Eq.sym (Eq.cong Ordering.index p)))
  | Greater, Equal   => No (p => Nat.zeroNotSucc 0 (Nat.succInjective 0 1 (Eq.sym (Eq.cong Ordering.index p))))
  | Greater, Greater => Yes rfl

