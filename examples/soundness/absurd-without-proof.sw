-- expect-error: E-AUTO-FALSE
-- An auto argument can't be satisfied by a false proposition: `get` on an
-- empty list is refused at compile time.
get : (xs : List a) -> (i : Nat) -> [auto ok : i < List.length xs] -> a
get (Cons x xs) Zero     = x
get (Cons x xs) (Succ i) = get xs i
get Nil         i        = Void.absurd (Bool.falseNotTrue ok)

nothing : Nat
nothing = get [a := Nat] Nil 0
