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
def sumFrom (acc: Nat): Nat -> Nat
  | 0      => acc
  | Succ n => sumFrom (acc + Succ n) n

export def sumTo (n: Nat): Nat := sumFrom 0 n

def lastOf (c: Char): List Char -> Char
  | Nil       => c
  | Cons d ds => lastOf d ds

export def lastChar (t: Text): Char := lastOf '?' (Text.toList t)

-- The recursive call is in tail position; the `if` is in an argument.
def countFrom (c: Char) (acc: Nat): List Char -> Nat
  | Nil       => acc
  | Cons d ds => countFrom c (if c == d then acc + 1 else acc) ds

export def countTail (c: Char) (t: Text): Nat := countFrom c 0 (Text.toList t)

-- Each turn of the loop makes a closure, which must keep that turn's `n`,
-- not the last one.
def adders (acc: List (Nat -> Nat)): Nat -> List (Nat -> Nat)
  | 0      => acc
  | Succ n => adders (Cons (\x => x + n) acc) n

def applyAll: List (Nat -> Nat) -> List Nat
  | Nil       => Nil
  | Cons f fs => Cons (f 100) (applyAll fs)

export def closures (n: Nat): List Nat := applyAll (adders Nil n)

-- A partial application of a loop, called twice: the first call mustn't
-- change what the second sees.
def twice (f: List Nat -> List Nat): List Nat := List.append (f Nil) (f (Cons 0 Nil))

export def reused (xs: List Nat): List Nat := twice (List.reverseOnto xs)

-- A loop whose recursive call is in one branch of an `if`, and whose other
-- branch also returns (the prelude's `Nat.digits`).
export def digits (n: Nat): Text := Nat.toText n
