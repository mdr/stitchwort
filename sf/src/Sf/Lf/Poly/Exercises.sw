-- Software Foundations, Volume 1: Logical Foundations, Poly.v, module
-- `Exercises` (the chapter's "Additional Exercises"), ported to
-- Stitchwort. Copyright and licence: sf/LICENSE-SF. Exercises are stated
-- as in Basics.sw: a statement or a function with `?` for the reader to
-- fill in. Read it after Poly.sw; its last section, the module `Church`,
-- is Church.sw.

namespace Sf.Lf.Poly.Exercises
import Sf.Lf.Nat (..)
import Sf.Lf.Basics (..)
import Sf.Lf.Induction (..)
import Sf.Lf.Poly (..)
import Std (Eq)

-- Exercise: 2 stars, standard (fold_length)
--
-- Many common functions on lists can be written with `fold`. For
-- example, here is another definition of `length`:

def foldLength (l: List a): Nat := fold (_ n => S n) l O

theorem testFoldLength1: foldLength (ofNats [4, 7, 0]) = ofNat 3 := rfl

-- Prove that `foldLength` is correct.
--
-- (The book's hint, to `unfold fold_length` when `simpl` won't, has no
-- counterpart to need here: a proof term is checked up to computation,
-- so `foldLength l` and `fold (_ n => S n) l O` are already the same
-- goal.)

theorem foldLengthCorrect ∀ (l: List a): foldLength l = length l := ?

-- Exercise: 3 stars, standard (fold_map)
--
-- `map` can be written with `fold` too. Finish `foldMap`:

--| Exercise (fold_map): replace the `?` with the definition.
def foldMap (f: a → b) (l: List a): List b := ?

-- Then state a theorem `foldMapCorrect`, saying that `foldMap` is
-- correct, and prove it.
--
--     theorem foldMapCorrect …

-- Exercise: 2 stars, advanced (currying)
--
-- The type `a → b → c` can be read as describing functions that take
-- two arguments, an `a` and a `b`, and give a `c`. As in partial
-- application, it means `a → (b → c)`: given an `a`, such a function
-- gives a function of type `b → c`, which given a `b` gives a `c`. Every
-- function takes one input, but some give a function back, which is what
-- makes partial application (`plus3`) work.
--
-- A function of type `Prod a b → c`, on the other hand, takes its one
-- input as a pair: both arguments at once, so no partial application.
--
-- A function can be converted between the two types. From `Prod a b →
-- c` to `a → b → c` is *currying*, after the logician Haskell Curry, and
-- the other way is *uncurrying*. Currying is:

def prodCurry (f: Prod a b → c) (x: a) (y: b): c := f (Pair x y)

-- As an exercise, define its inverse, `prodUncurry`, and then prove the
-- theorems below, which show that the two are inverses.

--| Exercise (currying): replace the `?` with the definition.
def prodUncurry (f: a → b → c) (p: Prod a b): c := ?

-- As a (trivial) example of currying's use, one of the earlier examples
-- can be shortened:

theorem testMap1': map (plus (ofNat 3)) (ofNats [2, 0, 2]) = ofNats [5, 3, 5] := rfl

-- Thought exercise: before asking `:t` in the REPL, `stitchwort doc` (or
-- hovering in the editor), can you work out the two functions' types?

theorem uncurryCurry ∀ (f: a → b → c) (x: a) (y: b): prodCurry (prodUncurry f) x y = f x y := ?

theorem curryUncurry ∀ (f: Prod a b → c) (p: Prod a b): prodUncurry (prodCurry f) p = f p := ?

-- Exercise: 2 stars, advanced, optional (nth_error_informal)
--
-- Recall the definition of `nthError`, here written with `if`:
--
--     def nthError (l: List a) (n: Nat): Option a := match l with
--       | Nil => None
--       | Cons x l' => if eqb n O then Some x else nthError l' (pred n)
--
-- Write a careful informal proof of this theorem:
--
--     ∀ (a: Type) (l: List a) (n: Nat) => length l = n → nthError l n = None
--
-- Make sure to state the induction hypothesis *explicitly*.
