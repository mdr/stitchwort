-- A function that calls itself in tail position becomes a loop in the
-- generated JS, so it doesn't use a stack frame per call (JS engines don't
-- eliminate tail calls). Calls in the branches of an `if` count.
--
-- run: sumTo 100000
-- run: lastChar "abc"
-- run: lastChar ""
-- run: countTail 'a' "banana"
-- run: closures 5
-- run: reused [1, 2, 3]
-- run: digits 1234567890

-- Deep enough to overflow the JS stack, if each call used a frame.
sumFrom : Nat -> Nat -> Nat
sumFrom acc 0        = acc
sumFrom acc (Succ n) = sumFrom (acc + Succ n) n

export
sumTo : Nat -> Nat
sumTo n = sumFrom 0 n

lastOf : Char -> List Char -> Char
lastOf c Nil         = c
lastOf c (Cons d ds) = lastOf d ds

export
lastChar : Text -> Char
lastChar t = lastOf '?' (Text.toList t)

-- The recursive call is in tail position; the `if` is in an argument.
countFrom : Char -> Nat -> List Char -> Nat
countFrom c acc Nil         = acc
countFrom c acc (Cons d ds) = countFrom c (if c == d then acc + 1 else acc) ds

export
countTail : Char -> Text -> Nat
countTail c t = countFrom c 0 (Text.toList t)

-- Each turn of the loop makes a closure, which must keep that turn's `n`,
-- not the last one.
adders : List (Nat -> Nat) -> Nat -> List (Nat -> Nat)
adders acc 0        = acc
adders acc (Succ n) = adders (Cons (\x -> x + n) acc) n

applyAll : List (Nat -> Nat) -> List Nat
applyAll Nil         = Nil
applyAll (Cons f fs) = Cons (f 100) (applyAll fs)

export
closures : Nat -> List Nat
closures n = applyAll (adders Nil n)

-- A partial application of a loop, called twice: the first call mustn't
-- change what the second sees.
twice : (List Nat -> List Nat) -> List Nat
twice f = List.append (f Nil) (f (Cons 0 Nil))

export
reused : List Nat -> List Nat
reused xs = twice (List.reverseOnto xs)

-- A loop whose recursive call is in one branch of an `if`, and whose other
-- branch also returns (the prelude's `Nat.digits`).
export
digits : Nat -> Text
digits n = Nat.toText n
