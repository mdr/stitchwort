-- Awkward names at the JS boundary (DESIGN.md §12, "Names"). A field's key
-- is its name with each prime as `$`, and a field called `tag` or
-- `__proto__` is `$tag` or `$__proto__`, so that it can't clash with the
-- constructor's tag or set an object's prototype. Nothing a program names
-- can clash with the generated module's own names, or the JS globals it
-- uses.
--
-- run: twiddle (Fields 1 2 3 4 5 6 7 8 9 10 11)
-- run: twiddle Plain
-- run: labelled (MkLabelled "MkLabelled" 1)
-- run: unbox (MkBox' 7)
-- run: firstTag (MkTagged' 1 2)
-- run: tagged (MkTagged' "a" "b")
-- run: enter 1 2
-- run: decode 3
-- run: Set 4
-- run: BigInt 5
-- run: RangeError (Oops "x")
-- run: args 1 2 3

type Awkward : Type =
  | Plain
  | Fields (tag : Nat) (__proto__ : Nat) (x : Nat) (x' : Nat) (x'' : Nat) (constructor : Nat) (undefined : Nat) (path : Nat) (inside : Nat) (v0 : Nat) (arg0 : Nat)

export
twiddle : Awkward -> Awkward
twiddle Plain                         = Plain
twiddle (Fields a b c d e f g h i j k) = Fields k j i h g f e d c b a

-- The bug this example started from: the field `tag` hid the constructor's.
type Labelled : Type =
  | MkLabelled (tag : Text) (count : Nat)

export
labelled : Labelled -> Labelled
labelled (MkLabelled t n) = MkLabelled (t ++ "!") (Succ n)

type Box' : Type =
  | MkBox' (value : Nat)

export
unbox : Box' -> Nat
unbox (MkBox' n) = n

type Tagged' (a : Type) : Type =
  | MkTagged' (tag : a) (tag' : a)

export
firstTag : Tagged' Nat -> Nat
firstTag (MkTagged' t u) = t

export
tagged : Tagged' Text -> Tagged' Text
tagged (MkTagged' t u) = MkTagged' u t

-- Exports named like the runtime's helpers and like JS globals it uses, and
-- parameters named like the wrapper's own variables, or reserved in JS.
export
enter : (v1 : Nat) -> (v0 : Nat) -> Nat
enter a b = a

export
decode : (undefined : Nat) -> Nat
decode n = Succ n

export
Set : (class : Nat) -> Nat
Set n = n + n

export
BigInt : (arg1 : Nat) -> Nat
BigInt n = n

type Error : Type =
  | Oops (tag : Text)

export
RangeError : Error -> Error
RangeError (Oops t) = Oops (t ++ t)

export
args : (this : Nat) -> (e : Nat) -> (arguments : Nat) -> Nat
args a b c = a + b + c
