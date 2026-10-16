-- Division, decisions and booleans, extracted to JS. Each `/` here is
-- justified by a proof in scope, checked at compile time and erased.
--
-- run: average [2, 4, 9]
-- run: average []
-- run: third [10, 20, 30, 40]
-- run: third [10]
-- run: isEven 7
-- run: isEven 10

total : List Nat -> Nat
total Nil         = 0
total (Cons x xs) = x + total xs

export
average : List Nat -> Nat
average xs = if h : List.length xs != 0 then total xs / List.length xs else 0

get : (xs : List a) -> (i : Nat) -> [auto ok : i < List.length xs] -> a
get (Cons x xs) Zero     = x
get (Cons x xs) (Succ i) = get xs i
get Nil         i        = Void.absurd (Bool.falseNotTrue ok)

-- The third element, or 0 if there isn't one.
export
third : List Nat -> Nat
third xs = if h : 2 < List.length xs then get xs 2 else 0

-- `n % 2 <= 0`, as a `Bool`. `%` by the literal 2 needs no `if`.
export
isEven : Nat -> Bool
isEven n = Nat.leq (n % 2) 0
