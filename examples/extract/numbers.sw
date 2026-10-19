-- Division, decisions and booleans, extracted to JS. Each `/` here is
-- justified by a proof in scope, checked at compile time and erased.
--
-- run: average [2, 4, 9]
-- run: average []
-- run: third [10, 20, 30, 40]
-- run: third [10]
-- run: isEven 7
-- run: isEven 10

def total: List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs

export def average (xs: List Nat): Nat := if h: List.length xs != 0 then total xs / List.length xs else 0

def get: (xs: List a) -> (i: Nat) -> [auto ok: i < List.length xs] -> a
  | Cons x xs, Zero   => x
  | Cons x xs, Succ i => get xs i
  | Nil,       i      => Void.absurd (Bool.falseNotTrue ok)

-- The third element, or 0 if there isn't one.
export def third (xs: List Nat): Nat := if h: 2 < List.length xs then get xs 2 else 0

-- `n % 2 <= 0`, as a `Bool`. `%` by the literal 2 needs no `if`.
export def isEven (n: Nat): Bool := Nat.leq (n % 2) 0
