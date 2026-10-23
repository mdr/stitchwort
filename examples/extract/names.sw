-- Awkward names at the JS boundary (DESIGN.md §12, "Names"). A field's key
-- is its name with each prime as `$`. The tag is in the property `$tag`,
-- which no field's name can give, so a field called `tag` keeps the key
-- `tag`. The key `__proto__` would set an object's prototype, so a field of
-- that name needs a `js.name` (here, the key it had before attributes).
-- Nothing a program names can clash with the generated module's own names,
-- or the JS globals it uses.
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

type Awkward: Type =
  | Plain
  | Fields (tag: Nat) (@[js.name "$__proto__"] __proto__: Nat) (x: Nat) (x' : Nat) (x'' : Nat) (constructor : Nat) (undefined : Nat) (path : Nat) (inside : Nat) (v0 : Nat) (arg0 : Nat)

export def twiddle : Awkward -> Awkward
  | Plain => Plain
  | Fields a b c d e f g h i j k => Fields k j i h g f e d c b a

-- The bug this example started from: the field `tag` hid the constructor's
-- (when the tag was in the property `tag`).
type Labelled: Type =
  | MkLabelled (tag: Text) (count: Nat)

export def labelled: Labelled -> Labelled
  | MkLabelled t n => MkLabelled (t ++ "!") (Succ n)

type Box' : Type =
  | MkBox' (value: Nat)

export def unbox: Box' -> Nat
  | MkBox' n => n

type Tagged' (a : Type) : Type =
  | MkTagged' (tag: a) (tag' : a)

export def firstTag : Tagged' Nat -> Nat
  | MkTagged' t u => t

export def tagged : Tagged' Text -> Tagged' Text
  | MkTagged' t u => MkTagged' u t

-- Exports named like the runtime's helpers and like JS globals it uses, and
-- parameters named like the wrapper's own variables, or reserved in JS.
export def enter: (v1: Nat) -> (v0: Nat) -> Nat
  | a, b => a

export def decode: (undefined: Nat) -> Nat
  | n => Succ n

export def Set: (class: Nat) -> Nat
  | n => n + n

export def BigInt: (arg1: Nat) -> Nat
  | n => n

type Error: Type =
  | Oops (tag: Text)

export def RangeError: Error -> Error
  | Oops t => Oops (t ++ t)

export def args: (this: Nat) -> (e: Nat) -> (arguments: Nat) -> Nat
  | a, b, c => a + b + c
