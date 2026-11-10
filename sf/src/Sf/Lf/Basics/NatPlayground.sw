-- Software Foundations, Volume 1: Logical Foundations, Basics.v, section
-- "Numbers" (module `NatPlayground`), ported to Stitchwort. Copyright and
-- licence: sf/LICENSE-SF.

-- The book puts its own definition of the natural numbers in a module, so
-- that it doesn't interfere with the standard library's, which the rest
-- of the book uses. Here it is a namespace of its own, with the type
-- named `Nat'` so that it can't be confused with the library's `Nat`.

namespace Sf.Lf.Basics.NatPlayground

-- All the types defined so far, both enumerated types such as `Day`,
-- `Bool` and `Bit`, and tuple types such as `Nybble` built from them, are
-- finite. The natural numbers are an infinite set, so they need a
-- slightly richer form of type declaration.
--
-- There are many ways to write numbers: decimal, hexadecimal, octal,
-- binary. Binary is valuable in hardware, since the digits can be two
-- voltage levels. Here we want a representation that makes *proofs*
-- simple, and the simplest is unary (base 1), with a single digit, as our
-- forebears might have counted days by scratches on a cave wall. The
-- constructor `O` (the letter, not the numeral) represents zero, and `S`
-- applied to the representation of `n` represents `n + 1` ("successor",
-- or "scratch"):

type Nat' =
  | O
  | S (n: Nat')

-- So 0 is `O`, 1 is `S O`, 2 is `S (S O)`, and so on. Read the clauses as:
--
-- - `O` is a natural number;
-- - `S` put in front of a natural number gives another one.
--
-- and these are the only ways to build one. `S (S false)` and
-- `O (O (O S))` are not natural numbers.
--
-- What we have defined is only a *representation*: a way of writing
-- numbers down. The names `O` and `S` mean nothing yet; any two names
-- would do, as in this type:

type OtherNat =
  | Stop
  | Tick (foo: OtherNat)

-- The *interpretation* comes from how we compute with them, by functions
-- that match on the representation, as for booleans and days. Here is
-- the predecessor function:

def pred (n: Nat'): Nat' := match n with
  | O => O
  | S n' => n'

-- The second arm reads: "if `n` has the form `S n'` for some `n'`, then
-- return `n'`."

-- The library's `Nat` is the same type with the constructors called
-- `Zero` and `Succ` (std/core/Data.sw). Numerals are written for it in
-- decimal (`4` is `Succ (Succ (Succ (Succ Zero)))`), and it is stored
-- compactly, so `4000000` costs no more than `4`; Basics.sw goes on with
-- it.
