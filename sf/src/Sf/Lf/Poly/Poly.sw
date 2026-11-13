-- Software Foundations, Volume 1: Logical Foundations, Poly.v ("Poly:
-- Polymorphism and Higher-Order Functions"), ported to Stitchwort.
-- Copyright and licence: sf/LICENSE-SF. Exercises are stated as in
-- Basics.sw: a statement or a function with `?` for the reader to fill
-- in. The numbers are the book's own, from Nat.sw, and so are the lists:
-- this chapter's `List` is defined below, not the library's (see
-- README.md).
--
-- The book's modules are namespaces in files next to this one:
-- `MumbleGrumble` (an exercise, after `repeat`), `OptionPlayground`
-- (after `split`), and `Exercises`, the chapter's last part, with its
-- module `Church` inside it. Read this file first; the comments say where
-- each of the others comes in.
--
-- The book starts from the previous chapters' definitions (`From LF
-- Require Export Lists`); the imports below bring them in.

namespace Sf.Lf.Poly
import Sf.Lf.Nat (..)
import Sf.Lf.Basics (..)
import Sf.Lf.Induction (..)
import Sf.Lf.Lists (..)
import Std (Eq, List as StdList, Nat as StdNat)

-- # Polymorphism
--
-- This chapter continues with basic functional programming. Its new
-- ideas are *polymorphism* (abstracting functions over the types of the
-- data they work on) and *higher-order functions* (treating functions as
-- data). Polymorphism first.

-- ## Polymorphic Lists
--
-- The last chapter's lists held only numbers. Real programs need lists
-- of other things too: of booleans, of lists, and so on. We *could*
-- define a new data type for each, for example:

type BoolList =
  | BoolNil
  | BoolCons (b: Bool) (l: BoolList)

-- but that soon becomes tedious: each type needs its own constructor
-- names, and, worse, its own `length`, `app`, `rev` and the rest, and
-- its own proofs of their properties (`revLength`, `appAssoc`, ...).
--
-- Instead, a data type can take a type as a parameter. Here is a
-- *polymorphic list* type:

type List (a: Type) =
  | Nil
  | Cons (x: a) (l: List a)

-- This is the last chapter's `NatList` with the `Nat` in `Cons` replaced
-- by a type `a`, which the header binds, and `NatList` replaced by `List
-- a`. `List Nat` is now the old `NatList`.
--
-- The book names the type parameter `X`. In Stitchwort a name that
-- starts with a capital letter is a type or a constructor, never a
-- variable, so type variables are lower case, `a`, `b`, `c`, as in the
-- library. (This `List`, `Nil` and `Cons` are the chapter's own, and hide
-- the library's in these files; the library's list type is imported as
-- `StdList`.)
--
-- What sort of thing is `List` itself? A function from types to types:
-- for any type `a`, `List a` is the type of lists whose elements are of
-- type `a`. The book's `Check list : Type -> Type` asks Rocq to confirm
-- that. In the editor, hovering over a name shows its type. In sf/,
-- `stitchwort repl src/Sf/Lf/Poly/Poly.sw` then `:t List Nat` gives
-- `Type`, and `stitchwort doc Sf.Lf.Poly.List` prints the header, `type
-- List (a: Type)`.
--
-- The parameter `a` becomes a parameter of the constructors `Nil` and
-- `Cons` too. Here Stitchwort and Rocq differ. In Rocq, `nil` and `cons`
-- first take the type as an ordinary argument, `nil nat` and `cons nat 3
-- (nil nat)`, until the book declares it implicit, a few sections on.
-- In Stitchwort a data type's parameters are *always* implicit in its
-- constructors: `Nil` and `Cons` have the types
--
--     Nil: [a: Type] → List a
--     Cons: [a: Type] → a → List a → List a
--
-- where `[a: Type] →` means "for every type `a`, worked out by the
-- compiler" (Rocq's `forall {X : Type},`), and the type of an element
-- is never written: `Cons (ofNat 3) Nil` is a `List Nat`, and `Cons
-- True Nil` a `List Bool`. Writing the type, `Nil Nat`, is an error,
-- "`Nil` takes 0 argument(s)". Where nothing says what `a` is, give the
-- whole expression a type: `(Nil: List Nat)`.
--
-- The list-processing functions can now be written once for every
-- element type. Here is `repeat`, with the element type as an ordinary,
-- *explicit* parameter `(a: Type)`, as the book first writes it:

def repeat (a: Type) (x: a) (count: Nat): List a := match count with
  | O => Nil
  | S count' => Cons x (repeat a x count')

-- `repeat` is applied first to a type, then to an element of that type
-- (and a number):

theorem testRepeat1: repeat Nat (ofNat 4) (ofNat 2) = Cons (ofNat 4) (Cons (ofNat 4) Nil) := rfl

-- To build other kinds of list, give it another type:

theorem testRepeat2: repeat Bool False (S O) = Cons False Nil := rfl

-- The mumble-grumble exercise comes here: MumbleGrumble.sw.

-- ### Type Annotation Inference
--
-- The book now writes `repeat` again with no types on its parameters,
-- `Fixpoint repeat' X x count : list X := …`, and Rocq works the types
-- out from how they are used. Stitchwort doesn't: every parameter of a
-- definition has a type, and leaving one off is "a parameter needs a
-- type". A definition's header is checked before its body, so its types
-- must be known from the header alone (that is also what lets a reader,
-- or the editor, see a definition's type without reading its body).
-- `(x: _)` doesn't help either: the compiler "couldn't work out what
-- goes here", since only the body would say.
--
-- Inside a body, though, types are inferred as in Rocq: in `repeat`
-- above, nothing says that `Nil` is a `List a` or that `count'` is a
-- `Nat`.

-- ### Type Argument Synthesis
--
-- A polymorphic function needs a type as well as its other arguments.
-- In `repeat`, the recursive call passes `a` along, though the next
-- argument, `x`, is an `a`, so the type could only be `a`. As in Rocq,
-- `_` asks the compiler to work an argument out:

def repeat'' (a: Type) (x: a) (count: Nat): List a := match count with
  | O => Nil
  | S count' => Cons x (repeat'' _ x count')

-- The book's example of what that saves is the list 1, 2, 3, `cons nat 1
-- (cons nat 2 (cons nat 3 (nil nat)))`, which becomes `cons _ 1 (cons _
-- 2 (cons _ 3 (nil _)))`. Since Stitchwort's constructors never take the
-- type, it is shorter still:

def list123: List Nat := Cons (S O) (Cons (ofNat 2) (Cons (ofNat 3) Nil))

-- (A definition's type is always written, as above: `def list123 := …`
-- without one is a parse error.)

-- ### Implicit Arguments
--
-- Rocq's `Arguments nil {X}` declares, after the fact, that a function's
-- type argument is always to be inferred. Stitchwort has no such
-- declaration: whether a parameter is implicit is part of the function's
-- own header, so `repeat` above stays explicit. The other way, which the
-- book prefers from here on, is to mark the parameter implicit where the
-- function is defined: Rocq's curly braces, Stitchwort's square
-- brackets:

def repeat''' [a: Type] (x: a) (count: Nat): List a := match count with
  | O => Nil
  | S count' => Cons x (repeat''' x count')

-- The recursive call doesn't pass `a`: it is inferred.
--
-- Stitchwort goes one step further. A lower-case name that a header uses
-- only as a type, and doesn't bind, is bound as an implicit parameter
-- automatically, so `[a: Type]` can be left out. The rest of the chapter
-- does that: `def app (l1 l2: List a): List a` means `def app [a: Type]
-- (l1 l2: List a): List a`.
--
-- The book then shows the trouble with making a *type's* parameter
-- implicit, `Inductive list' {X:Type}`: `list'` would then be written
-- without its type, `list'` rather than `list' nat`, which is "a step too
-- far". Stitchwort doesn't allow it: "a type's parameters in brackets
-- must be `auto`", since a type's other parameters are always given.
--
-- A few more list functions, on the new lists:

def app (l1 l2: List a): List a := match l1 with
  | Nil => l2
  | Cons h t => Cons h (app t l2)

def rev (l: List a): List a := match l with
  | Nil => Nil
  | Cons h t => app (rev t) (Cons h Nil)

def length (l: List a): Nat := match l with
  | Nil => O
  | Cons _ l' => S (length l')

theorem testRev1: rev (Cons (S O) (Cons (ofNat 2) Nil)) = Cons (ofNat 2) (Cons (S O) Nil) := rfl

theorem testRev2: rev (Cons True Nil) = Cons True Nil := rfl

theorem testLength1: length (Cons (S O) (Cons (ofNat 2) (Cons (ofNat 3) Nil))) = ofNat 3 := rfl

-- ### Supplying Type Arguments Explicitly
--
-- Now and then there isn't enough information to infer a type argument.
-- The book's example is `Fail Definition mynil := nil.` In Stitchwort a
-- definition's type is always written, and the nearest is a type with a
-- hole in it:
--
--     def mynil: List _ := Nil
--
--     [E-UNSOLVED] Error: can't work out an implicit argument
--       ╰── the compiler couldn't work out what goes here
--
-- The cure is the same as in the book, a type that says what the list
-- holds:

def mynil: List Nat := Nil

-- Rocq's other cure is `@nil nat`: `@` turns a function's implicit
-- arguments back into explicit ones, for one use. Stitchwort instead
-- passes an implicit argument by its name, in square brackets:
-- `repeat''' [a := Nat] O O` is `repeat''' O O` with `a` given. This
-- works for a definition's implicit parameters, but not for a
-- constructor's: their type parameters have no names, so `Nil [a :=
-- Nat]` is an error ("its parameters have no names"), and a type
-- annotation is the way.

def mynil': List Nat := repeat''' [a := Nat] O O

-- With the type arguments implicit, the book defines notation for its
-- lists, as for `NatList`: `x :: y` for `cons x y`, `[ ]` for `nil`,
-- `[x; ..; y]` for a list of elements, and `x ++ y` for `app x y`. As in
-- the last chapter, Stitchwort's list syntax, `[1, 2, 3]` and `[x,
-- ..l]`, and its `++`, are built in and always mean the library's
-- `List`, and there is no `Notation` to give them to this one. So this
-- port writes `Cons` and `Nil` in patterns and statements, calls `app`
-- by name, and converts a library list literal for a list of examples:

def ofList (xs: StdList a): List a := match xs with
  | [] => Nil
  | [x, ..rest] => Cons x (ofList rest)

-- For lists of the book's numbers, `ofNats` converts the numbers too, as
-- `ofNat` does one:

def ofNats (xs: StdList StdNat): List Nat := match xs with
  | [] => Nil
  | [x, ..rest] => Cons (ofNat x) (ofNats rest)

-- The book's `[1; 2; 3]`:

def list123''': List Nat := ofNats [1, 2, 3]

theorem list123Same: list123''' = list123 := rfl

-- `ofList [True, False]` is a `List Bool`, and a list of lists of
-- numbers is `ofList [ofNats [1], ofNats [2, 3]]`. Both compute, so
-- `rfl` sees through them.

-- ### Exercises

-- Exercise: 2 stars, standard (poly_exercises)
--
-- Some simple exercises, like those in the Lists chapter, for practice
-- with polymorphism. Complete the proofs.

theorem appNilR ∀ (l: List a): app l Nil = l := ?

-- The book's `l ++ m ++ n` is `l ++ (m ++ n)`, since its `++` groups to
-- the right.

theorem appAssoc ∀ (l m n: List a): app l (app m n) = app (app l m) n := ?

theorem appLength ∀ (l1 l2: List a): length (app l1 l2) = plus (length l1) (length l2) := ?

-- Exercise: 2 stars, standard (more_poly_exercises)
--
-- Some slightly more interesting ones:

theorem revAppDistr ∀ (l1 l2: List a): rev (app l1 l2) = app (rev l2) (rev l1) := ?

theorem revInvolutive ∀ (l: List a): rev (rev l) = l := ?

-- ## Polymorphic Pairs
--
-- In the same way, the last chapter's pairs of numbers generalise to
-- *polymorphic pairs*, often called *products*:

type Prod (a b: Type) =
  | Pair (x: a) (y: b)

-- As with lists, `Pair`'s type arguments are implicit. The book now
-- defines the notation `(x, y)` for `pair x y`, and `X * Y` for the type
-- `prod X Y`. Stitchwort has the same two notations built in, `(x, y)`
-- and `(a, b)`, but for the library's pair type (`Pair a b`, with
-- constructor `MkPair`), so this port writes `Pair x y` and `Prod a b`.
--
-- It's easy at first to confuse `Pair x y` and `Prod a b`. `Pair x y` is
-- a *value* built from two values, and `Prod a b` a *type* built from
-- two types: if `x` is an `a` and `y` a `b`, then `Pair x y` is a `Prod
-- a b`.
--
-- The projections look much as they would in any functional language:

def fst (p: Prod a b): a := match p with
  | Pair x y => x

def snd (p: Prod a b): b := match p with
  | Pair x y => y

-- `combine` takes two lists and makes a list of pairs. Many functional
-- languages call it `zip`; the book follows Rocq's library.

def combine (lx: List a) (ly: List b): List (Prod a b) := match lx, ly with
  | Nil, _ => Nil
  | _, Nil => Nil
  | Cons x tx, Cons y ty => Cons (Pair x y) (combine tx ty)

-- Exercise: 1 star, standard, optional (combine_checks)
--
-- Answer these on paper, then check your answers with Stitchwort:
--
-- - What is the type of `combine`? (In `stitchwort repl
--   src/Sf/Lf/Poly/Poly.sw`, `:t combine`.)
-- - What does `combine (ofNats [1, 2]) (ofList [False, False, True,
--   True])` compute to? (Write your answer as a test, `test "combine" :=
--   combine … == …`, and run `stitchwort test`.)

-- Exercise: 2 stars, standard, especially useful (split)
--
-- `split` is the right inverse of `combine`: it takes a list of pairs
-- and gives a pair of lists. Many functional languages call it `unzip`.
-- Fill in its definition, and make sure it passes the test.

--| Exercise (split): replace the `?` with the definition.
def split (l: List (Prod a b)): Prod (List a) (List b) := ?

theorem testSplit: split (ofList [Pair (S O) False, Pair (ofNat 2) False]) = Pair (ofNats [1, 2]) (ofList [False, False]) := ?

-- ## Polymorphic Options
--
-- The last polymorphic type for now generalises the last chapter's
-- `NatOption`. The book defines it in a module, OptionPlayground.sw,
-- because Rocq's library already has an `option`, and that is the one
-- the rest of the chapter uses. The port does the same: from here on,
-- `Option`, `Some` and `None` are the library's, which is the same type.
--
-- `nthError` now works on lists of any type:

def nthError (l: List a) (n: Nat): Option a := match l with
  | Nil => None
  | Cons x l' => match n with
    | O => Some x
    | S n' => nthError l' n'

theorem testNthError1: nthError (ofNats [4, 5, 6, 7]) O = Some (ofNat 4) := rfl

theorem testNthError2: nthError (ofList [ofNats [1], ofNats [2]]) (S O) = Some (ofNats [2]) := rfl

theorem testNthError3: nthError (ofList [True]) (ofNat 2) = None := rfl

-- Exercise: 1 star, standard, optional (hd_error_poly)
--
-- Complete the definition of a polymorphic version of the last chapter's
-- `hdError`, and make sure it passes the tests.

--| Exercise (hd_error_poly): replace the `?` with the definition.
def hdError (l: List a): Option a := ?

-- The book shows `@hd_error`'s type here, `forall X : Type, list X ->
-- option X`. In the REPL, `:t hdError` prints `[a: Type] → Sf.Lf.Poly.List a →
-- Option a`, even before you have filled in the `?`; `stitchwort doc
-- Sf.Lf.Poly.hdError` prints the header, `def hdError (l: List a): Option
-- a`. Either way `a` is bound automatically and implicitly, so there is no
-- `@` form to ask for.

theorem testHdError1: hdError (ofNats [1, 2]) = Some (S O) := ?

theorem testHdError2: hdError (ofList [ofNats [1], ofNats [2]]) = Some (ofNats [1]) := ?

-- # Functions as Data
--
-- Like most modern programming languages, especially functional ones
-- (OCaml, Haskell, Racket, Scala, Clojure, ...), Stitchwort treats
-- functions as first-class: they can be passed as arguments, returned as
-- results, stored in data structures, and so on.

-- ## Higher-Order Functions
--
-- Functions that work on other functions are called *higher-order*.
-- Here is a simple one:

def doit3times (f: a → a) (n: a): a := f (f (f n))

-- The argument `f` is itself a function, from `a` to `a`, and
-- `doit3times` applies it three times to `n`. Its type is `[a: Type] →
-- (f: a → a) → (n: a) → a`.

theorem testDoit3times: doit3times minustwo (ofNat 9) = ofNat 3 := rfl

theorem testDoit3times': doit3times negb True = False := rfl

-- ## Filter
--
-- A more useful higher-order function: it takes a list of `a`s and a
-- *predicate* on `a` (a function from `a` to `Bool`), and keeps the
-- elements for which the predicate gives `True`.
--
-- The book names the predicate `test`, which is a keyword in Stitchwort
-- (it starts a test), so here it is `keep`.

def filter (keep: a → Bool) (l: List a): List a := match l with
  | Nil => Nil
  | Cons h t => if keep h then Cons h (filter keep t) else filter keep t

-- Applied to the predicate `even` and a list of numbers, `filter` gives
-- the even ones:

theorem testFilter1: filter even (ofNats [1, 2, 3, 4]) = ofNats [2, 4] := rfl

def lengthIs1 (l: List a): Bool := eqb (length l) (S O)

theorem testFilter2: filter lengthIs1 (ofList [ofNats [1, 2], ofNats [3], ofNats [4], ofNats [5, 6, 7], Nil, ofNats [8]]) = ofList [ofNats [3], ofNats [4], ofNats [8]] := rfl

-- With `filter`, the Lists chapter's `countoddmembers` is one line:

def countoddmembers' (l: List Nat): Nat := length (filter odd l)

theorem testCountoddmembers'1: countoddmembers' (ofNats [1, 0, 3, 1, 4, 5]) = ofNat 4 := rfl

theorem testCountoddmembers'2: countoddmembers' (ofNats [0, 2, 4]) = O := rfl

theorem testCountoddmembers'3: countoddmembers' Nil = O := rfl

-- ## Anonymous Functions
--
-- It is a little sad to have to define and name `lengthIs1` just to pass
-- it to `filter` once. Higher-order functions are often given one-off
-- functions like that, and naming each would be tedious. Instead, a
-- function can be written where it is used, without a name. Rocq writes
-- it `fun n => n * n`; Stitchwort leaves out the `fun`, writing `n => mult
-- n n`, read "the function that, given `n`, gives `mult n n`". As an
-- argument it goes in brackets:

theorem testAnonFun': doit3times (n => mult n n) (ofNat 2) = ofNat 256 := rfl

-- The `filter` example again, with an anonymous function:

theorem testFilter2': filter (l => eqb (length l) (S O)) (ofList [ofNats [1, 2], ofNats [3], ofNats [4], ofNats [5, 6, 7], Nil, ofNats [8]]) = ofList [ofNats [3], ofNats [4], ofNats [8]] := rfl

-- (A parameter can be given a type, `(n: Nat) => mult n n`, where
-- nothing else says what it is. Stitchwort also has *clause lambdas*,
-- `match | O => … | S n => …`, a function that matches on its argument
-- straight away; docs/syntax.md, "Clause lambdas".)

-- Exercise: 2 stars, standard (filter_even_gt7)
--
-- Use `filter` (instead of a recursion of your own) to write
-- `filterEvenGt7`, which takes a list of numbers and keeps those that
-- are even and greater than 7.

--| Exercise (filter_even_gt7): replace the `?` with the definition.
def filterEvenGt7 (l: List Nat): List Nat := ?

theorem testFilterEvenGt7_1: filterEvenGt7 (ofNats [1, 2, 6, 9, 10, 3, 12, 8]) = ofNats [10, 12, 8] := ?

theorem testFilterEvenGt7_2: filterEvenGt7 (ofNats [5, 2, 6, 19, 129]) = Nil := ?

-- Exercise: 3 stars, standard (partition)
--
-- Use `filter` to write `partition`, which, given a predicate on `a` and
-- a `List a`, gives a pair of lists: the elements that satisfy the
-- predicate, and those that don't, each in the order of the original
-- list.

--| Exercise (partition): replace the `?` with the definition.
def partition (keep: a → Bool) (l: List a): Prod (List a) (List a) := ?

theorem testPartition1: partition odd (ofNats [1, 2, 3, 4, 5]) = Pair (ofNats [1, 3, 5]) (ofNats [2, 4]) := ?

theorem testPartition2: partition (x => False) (ofNats [5, 9, 0]) = Pair Nil (ofNats [5, 9, 0]) := ?

-- ## Map
--
-- Another handy higher-order function is `map`:

def map (f: a → b) (l: List a): List b := match l with
  | Nil => Nil
  | Cons h t => Cons (f h) (map f t)

-- It takes a function `f` and a list `[n1, n2, n3, ...]`, and gives the
-- list `[f n1, f n2, f n3, ...]`, with `f` applied to each element in
-- turn:

theorem testMap1: map (x => plus (ofNat 3) x) (ofNats [2, 0, 2]) = ofNats [5, 3, 5] := rfl

-- The input and output lists' element types needn't be the same: `map`
-- has two type parameters, `a` and `b`. So it can take a list of
-- numbers and a function from numbers to booleans, and give a list of
-- booleans:

theorem testMap2: map odd (ofNats [2, 1, 2, 5]) = ofList [False, True, False, True] := rfl

-- or even a list of numbers and a function from numbers to *lists* of
-- booleans, giving a list of lists of booleans:

theorem testMap3: map (n => ofList [even n, odd n]) (ofNats [2, 1, 2, 5]) = ofList [ofList [True, False], ofList [False, True], ofList [True, False], ofList [False, True]] := rfl

-- ### Exercises

-- Exercise: 3 stars, standard (map_rev)
--
-- Show that `map` and `rev` commute. (Hint: you may need a lemma of your
-- own first.)

theorem mapRev ∀ (f: a → b) (l: List a): map f (rev l) = rev (map f l) := ?

-- Exercise: 2 stars, standard, especially useful (flat_map)
--
-- `map` maps a `List a` to a `List b` with a function of type `a → b`.
-- `flatMap` does the same with a function of type `a → List b`, joining
-- the lists it gives into one ("flattening" them):
--
--     flatMap (n => ofList [n, S n, S (S n)]) (ofNats [1, 5, 10])
--       = ofNats [1, 2, 3, 5, 6, 7, 10, 11, 12]

--| Exercise (flat_map): replace the `?` with the definition.
def flatMap (f: a → List b) (l: List a): List b := ?

theorem testFlatMap1: flatMap (n => ofList [n, n, n]) (ofNats [1, 5, 4]) = ofNats [1, 1, 1, 5, 5, 5, 4, 4, 4] := ?

-- Lists aren't the only type for which `map` makes sense. Here is `map`
-- for `Option`:

def optionMap (f: a → b) (xo: Option a): Option b := match xo with
  | None => None
  | Some x => Some (f x)

-- Exercise: 2 stars, standard, optional (implicit_args)
--
-- The definitions and uses of `filter` and `map` use implicit arguments
-- in many places. Make them explicit: add `(a: Type)` (and `(b: Type)`)
-- at the front of each header, then pass the types where they are now
-- needed, and check that Stitchwort accepts the result. (This one isn't
-- handed in: it is easiest in a copy of this file that you throw away.)

-- ## Fold
--
-- An even more powerful higher-order function is `fold`. It inspired the
-- "reduce" operation at the heart of Google's map/reduce framework.

def fold (f: a → b → b) (l: List a) (init: b): b := match l with
  | Nil => init
  | Cons h t => f h (fold f t init)

-- (The book calls the last parameter `b`; here `b` is the type, so the
-- value is `init`.)
--
-- Intuitively, `fold` puts the binary operator `f` between each pair of
-- elements of the list. For example, `fold plus [1, 2, 3, 4]` means `1 +
-- 2 + 3 + 4`. To make that precise it also needs a starting value, the
-- first second argument of `f`. So
--
--     fold plus [1, 2, 3, 4] 0
--
-- gives
--
--     1 + (2 + (3 + (4 + 0))).

theorem foldExample1: fold andb (ofList [True, True, False, True]) True = False := rfl

theorem foldExample2: fold mult (ofNats [1, 2, 3, 4]) (S O) = ofNat 24 := rfl

theorem foldExample3: fold app (ofList [ofNats [1], Nil, ofNats [2, 3], ofNats [4]]) Nil = ofNats [1, 2, 3, 4] := rfl

theorem foldExample4: fold (l n => plus (length l) n) (ofList [ofNats [1], Nil, ofNats [2, 3, 2], ofNats [4]]) O = ofNat 5 := rfl

-- Exercise: 1 star, standard, optional (fold_types_different)
--
-- `fold`'s type has *two* type variables, `a` and `b`, and `f` takes an
-- `a` and a `b` and gives a `b`. `foldExample4` above is one case where
-- it helps for `a` and `b` to differ. Can you think of others?

-- ## Functions That Construct Functions
--
-- Most of the higher-order functions so far take functions as
-- arguments. Now some that *return* functions. To start, a function that
-- takes a value `x` and gives a function from `Nat` to `a` that always
-- gives `x`, whatever its argument:

def constfun (x: a): Nat → a := (k: Nat) => x

def ftrue: Nat → Bool := constfun True

theorem constfunExample1: ftrue O = True := rfl

theorem constfunExample2: (constfun (ofNat 5)) (ofNat 99) = ofNat 5 := rfl

-- (The book's `Definition ftrue := constfun true.` has no type; here
-- `ftrue` needs one, `Nat → Bool`.)
--
-- In fact the functions of several arguments already seen are examples
-- of functions as data too. Recall the type of `plus`: `Nat → Nat →
-- Nat`.

def plus3: Nat → Nat := plus (ofNat 3)

theorem testPlus3: plus3 (ofNat 4) = ofNat 7 := rfl

theorem testPlus3': doit3times plus3 O = ofNat 9 := rfl

theorem testPlus3'': doit3times (plus (ofNat 3)) O = ofNat 9 := rfl

-- Similarly:

def foldPlus: List Nat → Nat → Nat := fold plus

-- This is *partial application*. `→` groups to the right, so a function
-- type `A → B → C` means `A → (B → C)`: "a function from `A` to a
-- function from `B` to `C`".
--
-- So `fold` can be thought of not as a function of three arguments, but
-- as a function of one that
--
-- 1. takes an argument `f` of type `a → b → b`, and
-- 2. gives a function of type `List a → b → b` that "remembers" `f`.
--
-- `fold plus` gives `fold` its first argument, `plus`, and gets back a
-- function that sums the elements of any list of numbers. It still
-- expects two more arguments: a list and a starting value.
--
-- (Stitchwort's checker treats `plus3` and `(n => plus (ofNat 3) n)` as
-- the same function: eta, as in Rocq.)

-- # Additional Exercises
--
-- The book's module `Exercises` is Exercises.sw, next to this file, with
-- its module `Church` in Church.sw.
