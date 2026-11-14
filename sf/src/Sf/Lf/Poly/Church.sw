-- Software Foundations, Volume 1: Logical Foundations, Poly.v, module
-- `Church` (section "Church Numerals (Advanced)", in the module
-- `Exercises`), ported to Stitchwort. Copyright and licence:
-- sf/LICENSE-SF. Exercises are stated as in Basics.sw: a function or a
-- statement with `?` for the reader to fill in. Read it after
-- Exercises.sw.
--
-- This namespace defines its own `plus`, `mult` and `exp`, so it doesn't
-- import those of Nat.sw and Basics.sw.

namespace Sf.Lf.Poly.Exercises.Church
import Sf.Lf.Nat (Nat, O, S)
import Sf.Lf.Poly (doit3times)
import Std (Eq)

-- These exercises explore another way of defining the natural numbers,
-- the *Church numerals*, named after their inventor, the mathematician
-- Alonzo Church. A number `n` is represented by a function that takes a
-- function `f` and gives `f` applied `n` times.

type CNat: Type 1 = (a: Type) → (a → a) → a → a

-- The book's `cnat` is `forall X : Type, (X -> X) -> X -> X`. It
-- quantifies over all types, so it is a type in the universe above
-- `Type`, `Type 1`, and a synonym for it says so (without `: Type 1`,
-- "expected something of type `Type`, but this has type `Type 1`").
--
-- Some numbers in this notation. Applying a function once should be the
-- same as applying it:

def one: CNat := (a: Type) (f: a → a) (x: a) => f x

-- `two` applies `f` twice:

def two: CNat := (a: Type) (f: a → a) (x: a) => f (f x)

-- `zero` is a little trickier: how do you apply a function zero times?
-- Simply: give back the argument untouched.

def zero: CNat := (a: Type) (f: a → a) (x: a) => x

-- In general a number `n` is `(a: Type) f x => f (f … (f x) …)`, with
-- `n` copies of `f`; write that informally as `(a: Type) f x => fⁿ x`,
-- with `f⁰ x` being just `x`. The earlier `doit3times` is the Church
-- numeral 3:

def three: CNat := (a: Type) => doit3times

-- (The book writes `@doit3times`, to make its implicit type argument
-- explicit. In Stitchwort the lambda takes the type, and `doit3times`
-- gets it implicitly; its type, `(a → a) → a → a`, is checked against
-- what `three` must give.)
--
-- So `n a f x` means "do it `n` times", where `n` is a Church numeral
-- and "it" is applying `f`, starting from `x`.
--
-- Another way to see it: `f` is the successor operation on `a`, and `x`
-- is the zero of `a`. With those names:

def zero': CNat := (a: Type) (succ: a → a) (zero: a) => zero

def one': CNat := (a: Type) (succ: a → a) (zero: a) => succ zero

def two': CNat := (a: Type) (succ: a → a) (zero: a) => succ (succ zero)

-- Passing `S` as `succ` and `O` as `zero` gives the book's numbers:

theorem zeroChurchPeano: zero Nat S O = O := rfl

theorem oneChurchPeano: one Nat S O = S O := rfl

theorem twoChurchPeano: two Nat S O = S (S O) := rfl

-- So a functional language needn't have numbers built in, or even be
-- able to define them as a data type: they can be represented by
-- functions alone (if not efficiently).
--
-- Representing them isn't enough: we need arithmetic too. Complete the
-- functions below, and make sure their tests pass, by `rfl`.

-- Exercise: 2 stars, advanced (church_scc)
--
-- Define the successor of a Church numeral. Given `n`, `scc n` should
-- apply its function once more than `n` does: given `(a: Type) f x =>
-- fⁿ x`, it gives `(a: Type) f x => fⁿ⁺¹ x`. In other words, do it `n`
-- times, then once more.

--| Exercise (church_scc): replace the `?` with the definition.
def scc (n: CNat): CNat := ?

theorem scc1: scc zero = one := ?

theorem scc2: scc one = two := ?

theorem scc3: scc two = three := ?

-- Exercise: 3 stars, advanced (church_plus)
--
-- Define the sum of two Church numerals. Given `(a: Type) f x => fⁿ x`
-- and `(a: Type) f x => fᵐ x`, `plus` should give `(a: Type) f x =>
-- fⁿ⁺ᵐ x`: do it `n` times, then `m` more times.
--
-- Hint: the "zero" argument of a Church numeral needn't be just `x`.

--| Exercise (church_plus): replace the `?` with the definition.
def plus (n m: CNat): CNat := ?

theorem plus1: plus zero one = one := ?

theorem plus2: plus two three = plus three two := ?

theorem plus3: plus (plus two two) three = plus one (plus three three) := ?

-- Exercise: 3 stars, advanced (church_mult)
--
-- Define the product of two Church numerals.
--
-- Hint: the "successor" argument of a Church numeral needn't be just
-- `f`.
--
-- Warning: a Church numeral can't be given `CNat` itself as its type
-- argument. `CNat` is a `Type 1`, and a numeral takes a `Type`: `two
-- CNat` is "expected something of type `Type`, but this has type `Type
-- 1`". That is how Stitchwort, like Rocq ("Universe inconsistency"),
-- prevents the paradox of a type that contains itself. So leave the type
-- argument as it is.

--| Exercise (church_mult): replace the `?` with the definition.
def mult (n m: CNat): CNat := ?

theorem mult1: mult one one = one := ?

theorem mult2: mult zero (plus three three) = zero := ?

theorem mult3: mult two three = plus three three := ?

-- Exercise: 3 stars, advanced (church_exp)
--
-- Define exponentiation of two Church numerals.
--
-- Hint: the type argument of a Church numeral needn't be just `a`. But
-- again, it can't be `CNat` itself. Finding the right type can be
-- tricky.

--| Exercise (church_exp): replace the `?` with the definition.
def exp (n m: CNat): CNat := ?

theorem exp1: exp two two = plus two two := ?

theorem exp2: exp three zero = one := ?

theorem exp3: exp three two = plus (mult two (mult two two)) one := ?
