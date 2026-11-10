-- Software Foundations, Volume 1: Logical Foundations, Basics.v ("Basics:
-- Functional Programming in Rocq"), ported to Stitchwort. Copyright and
-- licence: sf/LICENSE-SF.
--
-- The book's prose is kept as comments, shortened where it is about Rocq's
-- own mechanics; where Stitchwort does something differently, a sentence
-- says so. Names follow Stitchwort's style: the book's `next_working_day`
-- is `nextWorkingDay`, `test_orb1` is `testOrb1`, and types start with a
-- capital (`Day`, `Bin`). The book's modules (`Playground`,
-- `TuplePlayground`, `NatPlayground`, `NatPlayground2`, `LateDays`) are
-- namespaces in files next to this one.
--
-- Exercises. The book leaves each exercise for the reader, ending it with
-- `Admitted`, and asks that solutions not be posted. Here:
--
-- - a theorem to prove is stated as a definition of a `Prop`, named as in
--   the book: `def plusIdExercise: Prop := ∀ (n m o: Nat) => …`. To do the
--   exercise, turn it into a theorem with the same statement and a proof,
--   `theorem plusIdExercise (n m o: Nat) (h1: n = m) …: … := …`;
-- - a function to write is defined with a placeholder body, marked
--   "Exercise", so that the definitions after it that use it still check.
--   The placeholder is not the answer: replace it.
--
-- Stitchwort's `?` is the nearest thing to `Admitted`, but a project with
-- a `?` in it doesn't pass `stitchwort check`, which is why this port
-- doesn't use it for the exercises (docs/reviews/SW-2707-software-foundations-port.md).

namespace Sf.Lf.Basics
import Std (Nat)

-- # Introduction
--
-- The *functional style* of programming is founded on simple, everyday
-- mathematical intuitions: if a procedure or method has no side effects,
-- then (ignoring efficiency) all we need to understand about it is how it
-- maps inputs to outputs, so we can think of it as a concrete method for
-- computing a mathematical function. That is one sense of "functional" in
-- "functional programming". The direct connection between programs and
-- simple mathematical objects supports both formal correctness proofs and
-- sound informal reasoning about program behaviour.
--
-- The other sense is that functions are *first-class* values: they can be
-- passed as arguments to other functions, returned as results, included
-- in data structures, and so on.
--
-- Other common features of functional languages include *algebraic data
-- types* and *pattern matching*, which make it easy to build and take
-- apart rich data structures, and *polymorphic type systems* for
-- abstraction and reuse. Stitchwort has all of these.
--
-- The first half of this chapter introduces the core of Stitchwort's
-- functional language. The second half introduces the basic ways of
-- proving properties of programs. In Rocq those are *tactics*, commands
-- that build a proof step by step; in Stitchwort a proof is written as a
-- term, much like a program, and the chapter shows the term for each
-- tactic proof in the book.
--
-- (The book's section on homework submission and its test scripts,
-- `BasicsTest.v`, are about the course's grading tools and are left out.)

-- # Data and Functions

-- ## Enumerated Types
--
-- Rocq's built-in features are extremely small: instead of the usual
-- atomic data types (booleans, integers, strings), it has a powerful way
-- of defining new data types from scratch, with all those familiar types
-- as instances. The book recapitulates almost all the definitions it
-- needs instead of taking them from the standard library.
--
-- Stitchwort is the same at its core: `Bool`, `Nat` and `List` are
-- ordinary data types in its standard library (std/core/Data.sw), though
-- numbers are stored compactly and have fast arithmetic. Where the book
-- defines its own copy of a library type, this port says so and uses the
-- library's.

-- ## Days of the Week
--
-- To see how a data type definition works, start with a very simple
-- example. This declaration defines a set of data values, a *type*:

type Day =
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

-- The new type is called `Day`, and its members are `Monday`, `Tuesday`,
-- and so on. Having defined `Day`, we can write functions on days:

def nextWorkingDay (d: Day): Day := match d with
  | Monday => Tuesday
  | Tuesday => Wednesday
  | Wednesday => Thursday
  | Thursday => Friday
  | Friday => Monday
  | Saturday => Monday
  | Sunday => Monday

-- The argument and result types are declared on the first line. Like most
-- functional languages, Stitchwort can often work types out when they're
-- not given, but a top-level definition always states them.
--
-- Having defined a function, we can check that it works on examples. The
-- book shows three ways.
--
-- First, Rocq's `Compute` evaluates an expression and prints the result.
-- Stitchwort's equivalents are outside the file: `stitchwort eval FILE
-- EXPR`, or `stitchwort repl FILE`, prints the value of an expression. In
-- the file itself, a `test` states the value expected, and `stitchwort
-- test` checks it:

test "next working day after Friday" := nextWorkingDay Friday == Monday

test "two working days after Saturday" := nextWorkingDay (nextWorkingDay Saturday) == Tuesday

-- Second, we can record what we expect the result to be as an *example*,
-- which is a theorem: an assertion with a name, and a proof that the
-- checker verifies. Rocq's `Example` and `Theorem` mean the same thing;
-- Stitchwort has only `theorem`.

theorem testNextWorkingDay: nextWorkingDay (nextWorkingDay Saturday) = Tuesday := rfl

-- The book's proof is `simpl. reflexivity.`: "both sides of the equation
-- evaluate to the same thing". Stitchwort's `rfl` says exactly that: the
-- checker computes both sides and compares them.
--
-- The difference between the first two: a `test` is run, on the fast
-- runtime, and only for the inputs written; a theorem is a proof, checked
-- by the kernel, and can be about every input, as the second half of the
-- chapter shows.
--
-- Third, Rocq can *extract* a program in a more conventional language
-- (OCaml, Scheme or Haskell) from a definition. Stitchwort runs its
-- programs itself (`stitchwort run`), builds native executables
-- (`stitchwort build`), and extracts JavaScript (`stitchwort build
-- --js`).
--
-- (The book's `From Stdlib Require Export String.` is there for its
-- grading scripts and has no counterpart here.)

-- ## Booleans
--
-- Following the pattern of the days of the week, the book defines the
-- type `bool` of booleans, with members `true` and `false`. Stitchwort's
-- library has the same type, `Bool`, with constructors `True` and
-- `False`, and this port uses it. The functions on booleans the book
-- defines next are written out here over the library's `Bool`; the
-- library has them too, as `not`, `&&` and `||`.

def negb (b: Bool): Bool := match b with
  | True => False
  | False => True

def andb (b1: Bool) (b2: Bool): Bool := match b1 with
  | True => b2
  | False => False

def orb (b1: Bool) (b2: Bool): Bool := match b1 with
  | True => True
  | False => b2

-- The last two show the syntax of multi-argument definitions. Their
-- application is shown by the following "unit tests", which together are
-- a complete specification of `orb`, its truth table:

theorem testOrb1: orb True False = True := rfl

theorem testOrb2: orb False False = False := rfl

theorem testOrb3: orb False True = True := rfl

theorem testOrb4: orb True True = True := rfl

-- Rocq's `Notation` command gives existing definitions a more familiar
-- infix syntax: the book writes `Notation "x && y" := (andb x y)`.
-- Stitchwort has no notation command: its operators are fixed, and each
-- stands for a library function (`&&` for `Bool.and`, `||` for
-- `Bool.or`, defined as `andb` and `orb` are here). So this example uses
-- the library's `||`:

theorem testOrb5: (False || False || True) = True := rfl

-- (In the book's `.v` files, code inside comments is put in square
-- brackets. Here it is in backquotes, as in Markdown.)
--
-- These examples are also a chance to introduce conditional expressions:

def negb' (b: Bool): Bool := if b then False else True

def andb' (b1: Bool) (b2: Bool): Bool := if b1 then b2 else False

def orb' (b1: Bool) (b2: Bool): Bool := if b1 then True else b2

-- Rocq's conditionals generalise in one small way: since `bool` isn't
-- built in, an `if` works on *any* data type with exactly two
-- constructors, the first counting as true. For example, a type `Bw` with
-- black and white, and `invert`:

type Bw =
  | BwBlack
  | BwWhite

-- Stitchwort's `if` takes a `Bool` (or a decidable proposition, such as
-- `n ≤ 5`), not any two-constructor type, so `invert` is a `match`:

def invert (x: Bw): Bw := match x with
  | BwBlack => BwWhite
  | BwWhite => BwBlack

test "invert BwBlack" := invert BwBlack == BwWhite

test "invert BwWhite" := invert BwWhite == BwBlack

-- Exercise: 1 star, standard (nandb)
--
-- Complete the definition of `nandb`, then make sure that each example
-- below can be proved. The function should return `True` if either or
-- both of its inputs are `False`.
--
-- Hint: if a proof by `rfl` fails, check that `nandb` computes on
-- `True` and `False`: a definition by `match` on its arguments does.

--| Exercise (nandb): replace this placeholder with the definition.
def nandb (b1: Bool) (b2: Bool): Bool := False

def testNandb1: Prop := nandb True False = True

def testNandb2: Prop := nandb False False = True

def testNandb3: Prop := nandb False True = True

def testNandb4: Prop := nandb True True = False

-- Exercise: 1 star, standard (andb3)
--
-- Do the same for `andb3`. It should return `True` when all of its inputs
-- are `True`, and `False` otherwise.

--| Exercise (andb3): replace this placeholder with the definition.
def andb3 (b1: Bool) (b2: Bool) (b3: Bool): Bool := False

def testAndb31: Prop := andb3 True True True = True

def testAndb32: Prop := andb3 False True True = False

def testAndb33: Prop := andb3 True False True = False

def testAndb34: Prop := andb3 True True False = False

-- ## Types
--
-- Every expression has a type that says what sort of thing it computes.
-- Rocq's `Check` prints the type of an expression, and with `: T` after
-- it, checks that it has that type. Stitchwort has no such command inside
-- a file; in `stitchwort repl`, `:t` prints the expression and its type,
-- and in the editor
-- hovering over a name shows it:
--
--     > :t True
--     True: Bool
--     > :t negb True
--     negb True: Bool
--     > :t negb
--     negb: Bool → Bool
--
-- Functions like `negb` are data values too, just like `True` and
-- `False`. Their types are *function types*, written with arrows:
-- `Bool → Bool` ("`Bool` arrow `Bool`") reads "given an input of type
-- `Bool`, this function produces an output of type `Bool`". The type of
-- `andb`, `Bool → Bool → Bool`, reads "given two inputs, each a `Bool`,
-- this function produces a `Bool`". Stitchwort accepts `->` for `→`.

-- ## New Types from Old
--
-- The types so far are *enumerated types*: their definitions list a
-- finite set of elements, the *constructors*. Here is a more interesting
-- definition, where one of the constructors takes an argument:

type Rgb =
  | Red
  | Green
  | Blue

type Color =
  | Black
  | White
  | Primary (p: Rgb)

-- A data type definition does two things:
--
-- - it introduces a set of new *constructors* (`Red`, `Primary`, `True`,
--   `Monday`, …);
-- - it groups them into a new named type (`Bool`, `Rgb`, `Color`).
--
-- *Constructor expressions* apply a constructor to zero or more other
-- constructor expressions, obeying the declared number and types of its
-- arguments: `Red`, `True` and `Primary Red` are, `Red Primary`,
-- `True Red` and `Primary (Primary Red)` aren't. The definitions say
-- which constructor expressions belong to `Rgb` and `Color`:
--
-- - `Red`, `Green` and `Blue` belong to `Rgb`;
-- - `Black` and `White` belong to `Color`;
-- - if `p` belongs to `Rgb`, then `Primary p` belongs to `Color`;
-- - and the expressions formed in these ways are the *only* members.
--
-- Functions on colours are defined by pattern matching, as for `Day` and
-- `Bool`:

def monochrome (c: Color): Bool := match c with
  | Black => True
  | White => True
  | Primary p => False

-- Since `Primary` takes an argument, a pattern for it has either a
-- variable, as above (whose name we choose freely), or a constant of the
-- right type, as below:

def isred (c: Color): Bool := match c with
  | Black => False
  | White => False
  | Primary Red => True
  | Primary _ => False

-- The pattern `Primary _` here is shorthand for "`Primary` applied to any
-- `Rgb` constructor except `Red`". (The wildcard `_` has the same effect
-- as the variable `p` in `monochrome`.)

-- ## Modules
--
-- Rocq has a module system: declarations between `Module X` and `End X`
-- are named `X.foo` afterwards, which lets the book reuse names. In
-- Stitchwort a namespace plays that part, and has a file of its own:
-- `Playground.sw`, next to this file, holds the book's
-- `Playground.foo: Rgb`, so this `foo` can be a `Bool`.

def foo: Bool := True

-- ## Tuples
--
-- The book's `TuplePlayground` module, with `Bit`, `Nybble` and
-- `allZero`, is TuplePlayground.sw.

-- ## Numbers
--
-- The book's own natural numbers, `O` and `S`, and `pred` are in the
-- module `NatPlayground`: NatPlayground.sw. From here on the numbers are
-- the library's `Nat`, with constructors `Zero` and `Succ` and decimal
-- numerals. A `Succ` chain written out is printed in decimal when it is
-- closed: in the REPL, `Succ (Succ (Succ (Succ Zero)))` prints `4: Nat`.

def minustwo (n: Nat): Nat := match n with
  | Zero => Zero
  | Succ Zero => Zero
  | Succ (Succ n') => n'

test "minustwo 4" := minustwo 4 == 2

-- The constructor `Succ` has the type `Nat → Nat`, just as `Nat.pred` and
-- `minustwo` do: all three can be applied to a number to give a number.
-- But there is a fundamental difference. `Nat.pred` and `minustwo` are
-- defined by *computation rules* (`minustwo 4` computes to `2`), while
-- `Succ` has no behaviour attached: it is a way of writing numbers down,
-- as the numeral `1` in `111` is a piece of data, not a computation.
--
-- For most interesting computations on numbers, pattern matching isn't
-- enough: we also need recursion. To check that `n` is even, we may need
-- to check whether `n - 2` is. Rocq introduces recursive functions with
-- `Fixpoint` instead of `Definition`; in Stitchwort a `def` may call
-- itself, and the checker sees that each call is on a smaller argument
-- (here `n'`, a part of `n`).

def even (n: Nat): Bool := match n with
  | Zero => True
  | Succ Zero => False
  | Succ (Succ n') => even n'

-- `odd` could be defined by a similar recursion, but here is a simpler
-- way:

def odd (n: Nat): Bool := negb (even n)

theorem testOdd1: odd 1 = True := rfl

theorem testOdd2: odd 4 = False := rfl

-- Multi-argument functions can be defined by recursion too. The book's
-- `plus`, `mult` and `minus`, in the module `NatPlayground2`, are in
-- NatPlayground2.sw; the library's `+`, `*` and `-` are defined the same
-- way.

def exp (base power: Nat): Nat := match power with
  | Zero => Succ Zero
  | Succ p => base * exp base p

-- Exercise: 1 star, standard (factorial)
--
-- Recall the factorial function:
--
--     factorial(0) = 1
--     factorial(n) = n * factorial(n - 1)    (if n > 0)
--
-- Translate it into Stitchwort.

--| Exercise (factorial): replace this placeholder with the definition.
def factorial (n: Nat): Nat := Zero

def testFactorial1: Prop := factorial 3 = 6

def testFactorial2: Prop := factorial 5 = 10 * 12

-- The book now gives `plus`, `minus` and `mult` the infix notations `+`,
-- `-` and `*`, with precedence levels. Stitchwort's `+`, `-` and `*` on
-- `Nat` are already the library's, defined as the book's.
--
-- Even testing equality is a user-defined operation in Rocq. Here is a
-- function `eqb` that tests natural numbers for `eq`uality, giving a
-- `b`oolean. It uses nested `match`es; a match on both at once, as in
-- `minus`, would do too.

def eqb (n m: Nat): Bool := match n with
  | Zero => match m with
    | Zero => True
    | Succ m' => False
  | Succ n' => match m with
    | Zero => False
    | Succ m' => eqb n' m'

-- Similarly, `leb` tests whether its first argument is less than or equal
-- to its second, giving a boolean.

def leb (n m: Nat): Bool := match n with
  | Zero => True
  | Succ n' => match m with
    | Zero => False
    | Succ m' => leb n' m'

theorem testLeb1: leb 2 2 = True := rfl

theorem testLeb2: leb 2 4 = True := rfl

theorem testLeb3: leb 4 2 = False := rfl

-- The book gives these the notations `x =? y` and `x <=? y`. In
-- Stitchwort they are the library's tests `x == y` and `x <= y`, used as
-- `Bool`s; `Nat.equal` and `Nat.leq` (std/core) are defined as `eqb` and
-- `leb` are here.

theorem testLeb3': (4 <= 2) = False := rfl

-- We now have two symbols that both look like equality: `=` and `==`.
-- `x = y` is a logical *claim*, a proposition, that we can try to prove;
-- `x == y` is a boolean *expression* whose value, `True` or `False`, we
-- can compute.
--
-- Stitchwort and Rocq differ here in a way worth knowing early. In Rocq,
-- `n <= m` (the proposition) is an inductive relation, and `n <=? m` (the
-- test) is a separate function, joined by lemmas. In Stitchwort, the
-- proposition `n ≤ m` is *defined* as the test giving `True`:
-- `Nat.LessEq n m := Nat.leq n m = True` (D3479: what a program can
-- test, a proof states as its test). So `3 ≤ 5` is proved by `rfl`, a
-- hypothesis `h: n ≤ m` is also a fact about the program's `if n <= m`,
-- and goals print it as `n ≤ m`. `x = y` stays the logical equality on
-- every type.

-- Exercise: 1 star, standard (ltb)
--
-- Fill in the definition of `ltb`, which tests natural numbers for
-- `l`ess-`t`han. Hint: instead of a new recursion, define it from a
-- previous function.

--| Exercise (ltb): replace this placeholder with the definition.
def ltb (n m: Nat): Bool := False

def testLtb1: Prop := ltb 2 2 = False

def testLtb2: Prop := ltb 2 4 = True

def testLtb3: Prop := ltb 4 2 = False

-- # Proof by Simplification
--
-- Each example so far has made a precise claim about a function on
-- particular inputs, and each proof was the same: compute both sides and
-- check that they're identical.

theorem plus11: 1 + 1 = 2 := rfl

-- The same "proof by simplification" can establish more interesting
-- properties. That `0` is a neutral element for `+` on the left can be
-- proved just by observing that `0 + n` computes to `n` whatever `n` is,
-- which can be read off the definition of `+`.

theorem plusON (n: Nat): 0 + n = n := rfl

-- Rocq writes this `forall n : nat, 0 + n = n`, and its proof starts with
-- `intros n`, which moves `n` from the quantifier into the *context* of
-- assumptions ("suppose `n` is some number…"). In Stitchwort the usual
-- way to state it is with `n` as a parameter, before the colon, as a
-- function has (D3470); then `n` is in scope in the proof already. The
-- statement with the quantifier is the same theorem, and its proof is a
-- function of `n`, which is what `intros` builds:

theorem plusON': ∀ (n: Nat) => 0 + n = n := n => rfl

-- Any other name would do in place of `n`, though it might confuse a
-- human reader:

theorem plusON'': ∀ (n: Nat) => 0 + n = n := m => rfl

-- Rocq's `simpl` shows the goal after computing, before `reflexivity`
-- finishes; `reflexivity` computes more (it unfolds definitions too).
-- Stitchwort has no steps to show between: `rfl` computes both sides in
-- full. To see a goal, write `?` where the proof goes; `stitchwort
-- check` (or hovering in the editor) shows the goal, computed.
--
-- `intros`, `simpl` and `reflexivity` are *tactics*: commands between
-- `Proof` and `Qed` that guide the checking of a claim. Stitchwort has
-- none: a proof is a term. The theorems below are proved the same way.

theorem plus1L (n: Nat): 1 + n = Succ n := rfl

theorem mult0L (n: Nat): 0 * n = 0 := rfl

-- The suffix `L` (the book's `_l`) is pronounced "on the left".

-- # Proof by Rewriting
--
-- This theorem is a bit more interesting:

theorem plusIdExample (n m: Nat) (h: n = m): n + n = m + m := rewrite h in rfl

-- It isn't a claim about all numbers `n` and `m`, but a more specialised
-- property that only holds when `n = m`. Rocq writes the hypothesis with
-- an arrow, `n = m -> n + n = m + m` ("implies"), and `intros H` names
-- it; in Stitchwort it is a parameter with a name, `(h: n = m)`.
--
-- Since `n` and `m` are arbitrary, computing alone can't prove it. But if
-- `n = m`, we can replace `n` by `m` in the goal and get an equation with
-- the same expression on both sides. `rewrite h in rfl` does that: it
-- replaces the left side of `h` by its right side in the goal, then
-- proves the result, `m + m = m + m`, by `rfl`. `rewrite <- h` would
-- rewrite from right to left.

-- Exercise: 1 star, standard (plus_id_exercise)
--
-- Prove this. (It has two hypotheses, `n = m` and `m = o`.)

def plusIdExercise: Prop := ∀ (n m o: Nat) => n = m → m = o → n + m = m + o

-- Rocq's `Admitted` accepts a theorem without proof. That is useful when
-- developing a long proof: state the lemmas you expect to need, admit
-- them, and make sure the main argument works before proving them. Every
-- `Admitted` is a door left open for nonsense to enter the checked world.
-- Stitchwort's `?` plays that part while developing: a theorem whose
-- proof is (or contains) `?` can be used by the theorems after it, the
-- checker shows the goal at the `?`, and `stitchwort check` fails until
-- every `?` is filled, so the door is never left open by accident.
--
-- Rocq's `Check` also shows the statements of theorems. The book looks at
-- two from its standard library, `mult_n_O: forall n, 0 = n * 0` and
-- `mult_n_Sm: forall n m, n * m + n = n * S m`. Stitchwort's library has
-- `Nat.mulZero (n: Nat): n * 0 = 0` and `Nat.mulSucc (n m: Nat):
-- n * Succ m = n + n * m`: `stitchwort doc Nat.mulZero` prints a
-- theorem's statement, and `stitchwort search 'Nat.mul _ (Succ _) = _'`
-- finds theorems by their shape.
--
-- `rewrite` can use a theorem as well as a hypothesis. If the theorem has
-- parameters, `rewrite` works out what they are by finding the theorem's
-- left side in the goal.

theorem multN0M0 (p q: Nat): p * 0 + q * 0 = 0 := rewrite Nat.mulZero p, Nat.mulZero q in rfl

-- (The book rewrites with `<- mult_n_O`, right to left, because Rocq's
-- lemma is stated `0 = n * 0`.)

-- Exercise: 1 star, standard (mult_n_1)
--
-- Use `Nat.mulSucc` and `Nat.mulZero` to prove this. (Recall that `1` is
-- `Succ Zero`.)

def multN1: Prop := ∀ (p: Nat) => p * 1 = p

-- # Proof by Case Analysis
--
-- Not everything can be proved by computing and rewriting: unknown values
-- (arbitrary numbers, booleans, lists) can block computation. In the
-- book, this is the example where `simpl` gets stuck:
--
--     Theorem plus_1_neq_0_firsttry : forall n : nat,
--       (n + 1) =? 0 = false.
--
-- because `+` and `eqb` both start by matching on their first argument,
-- and `n` is unknown.
--
-- In Stitchwort this one doesn't get stuck. The library's `+` is special
-- in one way: when its first argument is unknown and its second is a
-- `Succ` (as `1` is), it computes on the second, so `n + 1` computes to
-- `Succ n`, and then `eqb (Succ n) 0` computes to `False`
-- (docs/proposals/nat-add-recursion.md). `rfl` proves it:

theorem plus1Neq0FirstTry (n: Nat): eqb (n + 1) 0 = False := rfl

-- The book's point stands for other functions. `eqb 0 n` is stuck on
-- `n`, as `plus_1_neq_0_firsttry` is in Rocq; the next exercise
-- (`zeroNbeqPlus1`) is one too, and so is anything about the book's own
-- `plus` (Induction.sw shows it). To make progress, we consider the
-- possible forms of `n` separately. If `n` is `Zero`, we can compute the
-- result. If `n` is `Succ n'` for some `n'`, then, though we don't know
-- which number it is, we know it starts with a `Succ`, and that is enough
-- to compute the result. Rocq's tactic for this is `destruct`; in
-- Stitchwort it is a `match`, the same as in a program:

theorem plus1Neq0 (n: Nat): eqb (n + 1) 0 = False := match n with
  | Zero => rfl
  | Succ n' => rfl

-- The `match` makes two cases, and each must be proved. In each, the
-- goal has `n` replaced by that case's form: `eqb (0 + 1) 0 = False`,
-- then `eqb (Succ n' + 1) 0 = False`.
--
-- The book's `destruct n as [| n'] eqn:E` names the variables of each
-- case (`as [| n']`), and the equation `n = O` or `n = S n'` (`eqn:E`).
-- In a `match` the names are in the patterns, and `match e: n with`
-- names the equation `e`. The book's bullets, `-` and `+`, mark which
-- part of a proof belongs to which case, and in Rocq they are optional;
-- in a `match` the arms always do, by their indentation.
--
-- `match` works on any data type. Here it proves that boolean negation
-- is its own inverse:

theorem negbInvolutive (b: Bool): negb (negb b) = b := match b with
  | True => rfl
  | False => rfl

-- A `match` can go inside a case, splitting further. The book marks the
-- levels with different bullets (`-`, then `+`), or with braces:

theorem andbCommutative (b c: Bool): andb b c = andb c b := match b with
  | True => match c with
    | True => rfl
    | False => rfl
  | False => match c with
    | True => rfl
    | False => rfl

-- The book's `andb_commutative'` is the same proof with braces instead of
-- bullets; in Stitchwort it would be the proof above again, so it isn't
-- repeated. Three levels:

theorem andb3Exchange (b c d: Bool): andb (andb b c) d = andb (andb b d) c := match b with
  | True => match c with
    | True => match d with
      | True => rfl
      | False => rfl
    | False => match d with
      | True => rfl
      | False => rfl
  | False => match c with
    | True => match d with
      | True => rfl
      | False => rfl
    | False => match d with
      | True => rfl
      | False => rfl

-- Splitting every variable and computing is mechanical, and Stitchwort
-- has a word for it: `cases` finds what the goal is stuck on, splits it
-- as a `match` would, and closes each case by computing (up to 64
-- cases). So `andb3Exchange` is also just:

theorem andb3Exchange' (b c d: Bool): andb (andb b c) d = andb (andb b d) c := cases

-- Exercise: 2 stars, standard (andb_true_elim2)
--
-- Prove this, splitting into cases (and subcases) with `match`. Hints
-- from the book: you will need to split both booleans; it helps to look
-- at what the hypothesis says in each case before splitting the second;
-- and if the hypotheses contradict each other, there is nothing left to
-- prove (in Stitchwort an impossible case is the pattern `()`, or
-- `Void.exfalso` of a proof of `False = True`).

def andbTrueElim2: Prop := ∀ (b c: Bool) => andb b c = True → c = True

-- Many proofs split a variable right after introducing it. Rocq has a
-- shorthand, `intros [|n]`, which loses the equation `eqn:E` would give.
-- In Stitchwort the patterns of the `match` do both jobs already:

theorem plus1Neq0' (n: Nat): eqb (n + 1) 0 = False := match n with
  | Zero => rfl
  | Succ n => rfl

-- With nothing to name, Rocq writes `intros [] []`. A `match` on both
-- variables at once:

theorem andbCommutative'' (b c: Bool): andb b c = andb c b := match b, c with
  | True, True => rfl
  | True, False => rfl
  | False, True => rfl
  | False, False => rfl

-- Exercise: 1 star, standard (zero_nbeq_plus_1)

def zeroNbeqPlus1: Prop := ∀ (n: Nat) => eqb 0 (n + 1) = False

-- ## More on Notation (Optional)
--
-- Rocq's notations each have a precedence level and an associativity
-- (`1+2*3*4` is `1+((2*3)*4)`) and a *scope* (`nat_scope`, `type_scope`,
-- `0%nat`). Stitchwort's operators are fixed, with a fixed precedence
-- table (docs/syntax.md, "Logic notation"), and a numeral's type is
-- worked out from where it is used, so none of this has a counterpart.

-- ## Fixpoints and Structural Recursion (Optional)
--
-- A copy of the definition of addition:

def plus' (n m: Nat): Nat := match n with
  | Zero => m
  | Succ n' => Succ (plus' n' m)

-- Rocq notes that `plus'` is "decreasing on 1st argument": the recursive
-- calls are only on strictly smaller values of `n`, so every call
-- terminates. Rocq demands that some argument of every `Fixpoint` be
-- decreasing, which guarantees that every function terminates on all
-- inputs; but its check isn't very sophisticated, so some functions have
-- to be written in slightly unnatural ways.
--
-- Stitchwort's rule is the same, for the same reason: a function that
-- might not terminate could prove anything. Where the recursion isn't on
-- a part of an argument, a `decreasing` clause names a measure that goes
-- down at each call, and the checker asks for a proof that it does
-- (docs/syntax.md, "decreasing"). A function that may really not
-- terminate is marked `Partial`, and can't be used in proofs.

-- Exercise: 2 stars, standard, optional (decreasing)
--
-- To get a concrete sense of this, find a way to write a sensible
-- recursive definition (of a simple function on numbers, say) that does
-- terminate on all inputs, but that the checker rejects because of this
-- restriction. Then see whether `decreasing` lets you write it.

-- # More Exercises

-- ## Warmups

-- Exercise: 1 star, standard (identity_fn_applied_twice)

def identityFnAppliedTwice: Prop := ∀ (f: Bool → Bool) => (∀ (x: Bool) => f x = x) → ∀ (b: Bool) => f (f b) = b

-- Exercise: 1 star, standard (negation_fn_applied_twice)
--
-- State and prove a theorem `negationFnAppliedTwice` like the previous
-- one, but where the hypothesis says that `f x = negb x`.

-- Exercise: 3 stars, standard, optional (andb_eq_orb)
--
-- Hint: this can be a bit tricky, depending on how you approach it. You
-- will probably need both `match` and `rewrite`, but splitting everything
-- in sight is not the best way.

def andbEqOrb: Prop := ∀ (b c: Bool) => andb b c = orb b c → b = c

-- ## Course Late Policies, Formalized
--
-- In LateDays.sw (the book's module `LateDays`).

-- ## Binary Numerals

-- Exercise: 3 stars, standard (binary)
--
-- We can generalise the unary representation of natural numbers to the
-- more efficient binary one, treating a binary number as a sequence of
-- constructors `B0` and `B1` (for 0s and 1s), ended by a `Z`. In unary, a
-- number is a sequence of `Succ`s ended by a `Zero`. For example:
--
--     decimal               binary                 unary
--        0                       Z                  Zero
--        1                    B1 Z                  Succ Zero
--        2                B0 (B1 Z)                 Succ (Succ Zero)
--        3                B1 (B1 Z)                 Succ (Succ (Succ Zero))
--        4            B0 (B0 (B1 Z))                …
--        5            B1 (B0 (B1 Z))
--        6            B0 (B1 (B1 Z))
--        7            B1 (B1 (B1 Z))
--        8        B0 (B0 (B0 (B1 Z)))
--
-- The low-order bit is on the left and the high-order bit on the right,
-- the opposite of the way binary numbers are usually written. That makes
-- them easier to work with. (What number is `B0 Z`?)

type Bin =
  | Z
  | B0 (n: Bin)
  | B1 (n: Bin)

-- Complete the definitions of an increment function `incr` for binary
-- numbers, and of `binToNat`, which converts a binary number to unary.

--| Exercise (binary): replace this placeholder with the definition.
def incr (m: Bin): Bin := m

--| Exercise (binary): replace this placeholder with the definition.
def binToNat (m: Bin): Nat := Zero

-- These unit tests should hold once the functions are defined correctly.
-- Of course, unit tests don't fully show that they are right: we return
-- to that at the end of the next chapter.

def testBinIncr1: Prop := incr (B1 Z) = B0 (B1 Z)

def testBinIncr2: Prop := incr (B0 (B1 Z)) = B1 (B1 Z)

def testBinIncr3: Prop := incr (B1 (B1 Z)) = B0 (B0 (B1 Z))

def testBinIncr4: Prop := binToNat (B0 (B1 Z)) = 2

def testBinIncr5: Prop := binToNat (incr (B1 Z)) = 1 + binToNat (B1 Z)

def testBinIncr6: Prop := binToNat (incr (incr (B1 Z))) = 2 + binToNat (B1 Z)

def testBinIncr7: Prop := binToNat (B0 (B0 (B0 (B1 Z)))) = 8

-- # Testing Your Solutions
--
-- Each chapter of the book comes with a test script (`BasicsTest.v`) that
-- checks the exercises are solved and their statements unchanged. Here,
-- `stitchwort check` in sf/ checks every proof, and `stitchwort audit
-- Sf.Lf.Basics` reports any theorem that rests on an unfinished `?` or an
-- axiom.
