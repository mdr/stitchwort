-- Software Foundations, Volume 1: Logical Foundations, Basics.v, section
-- "Numbers" (modules `NatPlayground` and `NatPlayground2`), ported to
-- Stitchwort. Copyright and licence: sf/LICENSE-SF.

-- The book defines its own natural numbers in a module, so that they don't
-- interfere with the standard library's, and proves everything about them
-- from scratch. This file is that module, and it is the numbers the
-- Basics and Induction chapters use. It has the book's definitions and no
-- lemmas: the library's `Nat` comes with a large stock of proved facts
-- (`Nat.addComm`, `Nat.mulZero`, ...) and with decision procedures
-- (`omega`) that would solve many of the exercises in one word, so the
-- exercises here are about this type, which none of that applies to.
--
-- Differences from the book:
--
-- - The type is `Nat`, in the namespace `Sf.Lf.Nat`; a chapter imports it
--   as `import Sf.Lf.Nat (Nat, plus, mult, minus)` and doesn't import the
--   library's `Nat`. Constructors come with their type: `Nat` brings `O`
--   and `S`.
-- - Number literals stand for the library's `Nat` only, so `3` can't be
--   written for this type. Write `S (S (S O))`, or `ofNat 3`, a function
--   from a library numeral that computes to the chain: `ofNat 3 = S (S (S
--   O))` is `rfl`. The chapters write `O` and `S O` as they are and use
--   `ofNat` for larger numbers.
-- - There are no `+`, `*`, `-`, `<=` operators for this type: call `plus`,
--   `mult`, `minus`, and (in Basics) `eqb` and `leb` by name.

namespace Sf.Lf.Nat
import Std (Nat as StdNat)

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

type Nat = | O | S (n: Nat)

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

type OtherNat = | Stop | Tick (foo: OtherNat)

-- The *interpretation* comes from how we compute with them, by functions
-- that match on the representation, as for booleans and days. Here is
-- the predecessor function:

def pred (n: Nat): Nat := match n with
  | O => O
  | S n' => n'

-- The second arm reads: "if `n` has the form `S n'` for some `n'`, then
-- return `n'`."

-- Numerals, as described at the top: the chain of `S`s for a library
-- number.

def ofNat (n: StdNat): Nat := match n with
  | Zero => O
  | Succ n' => S (ofNat n')

theorem ofNatThree: ofNat 3 = S (S (S O)) := rfl

-- Multi-argument functions can be defined by recursion too.

def plus (n m: Nat): Nat := match n with
  | O => m
  | S n' => S (plus n' m)

-- Adding three to two gives us five (whew!):

test "plus 3 2" := plus (ofNat 3) (ofNat 2) == ofNat 5

-- The steps of simplification that compute this can be visualised as
-- follows:
--
--         plus 3 2
--    i.e. plus (S (S (S O))) (S (S O))
--     ==> S (plus (S (S O)) (S (S O)))
--           by the second arm of the match
--     ==> S (S (plus (S O) (S (S O))))
--           by the second arm of the match
--     ==> S (S (S (plus O (S (S O)))))
--           by the second arm of the match
--     ==> S (S (S (S (S O))))
--           by the first arm of the match
--    i.e. 5
--
-- Rocq lets parameters of the same type share brackets, `(n m : nat)`.
-- Stitchwort does too: `(n m: Nat)` is `(n: Nat) (m: Nat)`.

def mult (n m: Nat): Nat := match n with
  | O => O
  | S n' => plus m (mult n' m)

theorem testMult1: mult (ofNat 3) (ofNat 3) = ofNat 9 := rfl

-- Two expressions can be matched at once by putting a comma between them:

def minus (n m: Nat): Nat := match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
