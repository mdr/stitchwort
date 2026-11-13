-- Software Foundations, Volume 1: Logical Foundations, Lists.v ("Lists:
-- Working with Structured Data"), module `NatList`, ported to Stitchwort.
-- Copyright and licence: sf/LICENSE-SF. Exercises are stated as in
-- Basics.sw: a statement or a function with `?` for the reader to fill
-- in. The numbers are the book's own, from Nat.sw (see README.md).
--
-- The book puts nearly all of this chapter in a module `NatList`, so that
-- the next chapter (Poly) can define polymorphic lists with the same
-- names. Here the module is this namespace, `Sf.Lf.Lists.NatList`; the
-- chapter's last section, Partial Maps, is in Lists.sw and PartialMap.sw
-- next to this file. Read this file first.
--
-- The book starts from the previous chapters' definitions (`From LF
-- Require Export Induction`); the imports below bring them in, with the
-- book's numbers from Nat.sw.

namespace Sf.Lf.Lists.NatList
import Sf.Lf.Nat (Nat, O, S, ofNat, plus, pred)
import Sf.Lf.Basics (..)
import Sf.Lf.Induction (..)
import Std (Eq, Nat as StdNat)

-- # Pairs of Numbers
--
-- In a data type definition, each constructor can take any number of
-- arguments: none (as with `True` and `O`), one (as with `S`), or more
-- than one, as here:

type NatProd =
  | Pair (n1 n2: Nat)

-- "The one and only way to construct a pair of numbers is by applying the
-- constructor `Pair` to two arguments of type `Nat`."
--
-- The book's `Check (pair 3 5) : natprod` asks Rocq to confirm a type.
-- Stitchwort's REPL does that with `:t` (in this folder, `stitchwort repl
-- src/Sf/Lf/Lists/NatList.sw`, then `import Sf.Lf.Nat (ofNat)` and `:t
-- Pair (ofNat 3) (ofNat 5)`), and in the editor, hovering over an
-- expression shows its type.
--
-- Functions for taking a pair apart are defined by pattern matching:

def fst (p: NatProd): Nat := match p with
  | Pair x y => x

def snd (p: NatProd): Nat := match p with
  | Pair x y => y

test "fst (pair 3 5)" := fst (Pair (ofNat 3) (ofNat 5)) == ofNat 3

-- The book now gives pairs the notation `(x, y)`, with a `Notation`
-- declaration, and defines `fst'` and `snd'` again using it in patterns.
-- Stitchwort has no `Notation` (its operators and brackets are a fixed
-- set, and always mean the library's types): `(x, y)` is the library's
-- own pair type, `Pair a b` (std/core/Data.sw), which Poly's polymorphic
-- pairs will correspond to. So this chapter writes its pairs as `Pair x
-- y`, and `fst'` and `snd'` would be `fst` and `snd` again.

def swapPair (p: NatProd): NatProd := match p with
  | Pair x y => Pair y x

-- Matching on a pair, `| Pair x y`, is not the same as matching on two
-- values at once, `match n, m with | O, _ => …`, as `minus` in Nat.sw
-- does. One has one value with two parts, the other two values. Writing
-- one for the other is an error: `match p with | x, y => x` says "this
-- alternative has 2 patterns, but the `match` has 1 scrutinee".
--
-- If we state properties of pairs in a slightly peculiar way, `rfl` can
-- prove them by computing:

theorem surjectivePairing' ∀ (n m: Nat): Pair n m = Pair (fst (Pair n m)) (snd (Pair n m)) := rfl

-- But `rfl` is not enough if the statement is more natural:
--
--     theorem surjectivePairingStuck (p: NatProd): p = Pair (fst p) (snd p) := rfl
--
--     [E-REFL] Error: `rfl` can't prove this
--       ╰─── `p` and `Pair (fst p) (snd p)` aren't equal
--
-- `fst p` can't compute until `p` is known to be a `Pair`. A `match`
-- exposes that structure, as Rocq's `destruct` does:

theorem surjectivePairing ∀ (p: NatProd): p = Pair (fst p) (snd p) := match p with
  | Pair n m => rfl

-- Unlike the `match` on a `Nat`, which has two arms, this has only one,
-- because a `NatProd` can be built in only one way.
--
-- (Had `NatProd` been declared as a record, `type NatProd = { n1: Nat,
-- n2: Nat }`, `surjectivePairingStuck` would hold by `rfl`: Stitchwort's
-- checker knows that a record value is the record of its fields, record
-- eta.)

-- Exercise: 1 star, standard (snd_fst_is_swap)

theorem sndFstIsSwap ∀ (p: NatProd): Pair (snd p) (fst p) = swapPair p := ?

-- Exercise: 1 star, standard, optional (fst_swap_is_snd)

theorem fstSwapIsSnd ∀ (p: NatProd): fst (swapPair p) = snd p := ?

-- # Lists of Numbers
--
-- Generalising the definition of pairs, a list of numbers is "either the
-- empty list or else a pair of a number and another list":

type NatList =
  | Nil
  | Cons (n: Nat) (l: NatList)

-- (These `Nil` and `Cons` are this chapter's own and hide the library's
-- in this file, as the book's `nil` and `cons` do.)
--
-- For example, here is a three-element list:

def mylist: NatList := Cons (S O) (Cons (ofNat 2) (Cons (ofNat 3) Nil))

-- The book now declares the notations `x :: l` for `cons x l`, `[ ]` for
-- `nil` and `[x; ..; y]` for a list of elements, and explains Rocq's
-- precedence levels. Stitchwort's list syntax, `[1, 2, 3]` and
-- `[x, ..l]`, and its `++`, are built in and always mean the library's
-- `List`, and there is no `Notation` to give them to `NatList`. So this
-- port writes the constructors, and for longer lists of numbers it
-- converts a library list literal, as `ofNat` converts a number:

def ofList (xs: List StdNat): NatList := match xs with
  | [] => Nil
  | [x, ..rest] => Cons (ofNat x) (ofList rest)

theorem mylist1: mylist = ofList [1, 2, 3] := rfl

-- `ofList [1, 2, 3]` computes to `Cons (S O) (Cons (S (S O)) (Cons (S (S
-- (S O))) Nil))`, so `rfl` sees the two as equal. The book's three
-- spellings of `mylist` (with `::`, without brackets, and with `[1;2;3]`)
-- become this one.

-- ## Repeat
--
-- `repeat` takes a number `n` and a `count`, and gives a list of length
-- `count` in which every element is `n`.

def repeat (n count: Nat): NatList := match count with
  | O => Nil
  | S count' => Cons n (repeat n count')

-- ## Length
--
-- `length` computes the length of a list.

def length (l: NatList): Nat := match l with
  | Nil => O
  | Cons h t => S (length t)

-- ## Append
--
-- `app` appends (concatenates) two lists.

def app (l1 l2: NatList): NatList := match l1 with
  | Nil => l2
  | Cons h t => Cons h (app t l2)

-- The book writes `app` as the infix `++`. Stitchwort's `++` is the
-- library's (lists and text), so `app` is called by name.

theorem testApp1: app (ofList [1, 2, 3]) (ofList [4, 5]) = ofList [1, 2, 3, 4, 5] := rfl

theorem testApp2: app Nil (ofList [4, 5]) = ofList [4, 5] := rfl

theorem testApp3: app (ofList [1, 2, 3]) Nil = ofList [1, 2, 3] := rfl

-- ## Head and Tail
--
-- `hd` gives the first element (the "head") of a list, and `tl` everything
-- but the first (the "tail"). The empty list has no first element, so
-- `hd` takes a default to give in that case.

def hd (default: Nat) (l: NatList): Nat := match l with
  | Nil => default
  | Cons h t => h

def tl (l: NatList): NatList := match l with
  | Nil => Nil
  | Cons h t => t

theorem testHd1: hd O (ofList [1, 2, 3]) = S O := rfl

theorem testHd2: hd O Nil = O := rfl

theorem testTl: tl (ofList [1, 2, 3]) = ofList [2, 3] := rfl

-- ## Exercises

-- Exercise: 2 stars, standard, especially useful (list_funs)
--
-- Complete the definitions of `nonzeros`, `oddmembers` and
-- `countoddmembers`. The tests show what they should do.

--| Exercise (list_funs): replace the `?` with the definition.
def nonzeros (l: NatList): NatList := ?

theorem testNonzeros: nonzeros (ofList [0, 1, 0, 2, 3, 0, 0]) = ofList [1, 2, 3] := ?

--| Exercise (list_funs): replace the `?` with the definition.
def oddmembers (l: NatList): NatList := ?

theorem testOddmembers: oddmembers (ofList [0, 1, 0, 2, 3, 0, 0]) = ofList [1, 3] := ?

-- The book declares `countoddmembers` with `Definition` rather than
-- `Fixpoint`, to encourage defining it from functions already written
-- rather than by a recursion of its own. Stitchwort has one `def` for
-- both, so that is up to you.

--| Exercise (list_funs): replace the `?` with the definition.
def countoddmembers (l: NatList): Nat := ?

theorem testCountoddmembers1: countoddmembers (ofList [1, 0, 3, 1, 4, 5]) = ofNat 4 := ?

theorem testCountoddmembers2: countoddmembers (ofList [0, 2, 4]) = O := ?

theorem testCountoddmembers3: countoddmembers Nil = O := ?

-- Exercise: 3 stars, advanced (alternate)
--
-- Complete the definition of `alternate`, which interleaves two lists
-- into one, taking elements from the first and the second in turn. See
-- the tests.
--
-- Hint: there are natural ways of writing `alternate` that the checker
-- refuses because it can't see that every recursive call is on a smaller
-- argument (`E-TERMINATION`). If that happens, try matching on both lists
-- at once, `match l1, l2 with`.

--| Exercise (alternate): replace the `?` with the definition.
def alternate (l1 l2: NatList): NatList := ?

theorem testAlternate1: alternate (ofList [1, 2, 3]) (ofList [4, 5, 6]) = ofList [1, 4, 2, 5, 3, 6] := ?

theorem testAlternate2: alternate (ofList [1]) (ofList [4, 5, 6]) = ofList [1, 4, 5, 6] := ?

theorem testAlternate3: alternate (ofList [1, 2, 3]) (ofList [4]) = ofList [1, 4, 2, 3] := ?

theorem testAlternate4: alternate Nil (ofList [20, 30]) = ofList [20, 30] := ?

-- ## Bags via Lists
--
-- A bag (or multiset) is like a set, except that each element can
-- appear more than once. One way to represent a bag of numbers is as a
-- list.

type Bag = NatList

-- Exercise: 3 stars, standard, especially useful (bag_functions)
--
-- Complete the definitions of `count`, `sum`, `add` and `member` for
-- bags.

--| Exercise (bag_functions): replace the `?` with the definition.
def count (v: Nat) (s: Bag): Nat := ?

-- All these proofs can be done with `rfl`.

theorem testCount1: count (S O) (ofList [1, 2, 3, 1, 4, 1]) = ofNat 3 := ?

theorem testCount2: count (ofNat 6) (ofList [1, 2, 3, 1, 4, 1]) = O := ?

-- Multiset `sum` is like set union: `sum a b` contains all the elements
-- of `a` and of `b`. (Mathematicians usually define union on multisets a
-- little differently, with max instead of sum, which is why this isn't
-- called `union`.)
--
-- The header deliberately gives the arguments no names. Implement `sum`
-- with a function already defined, without changing the header.

--| Exercise (bag_functions): replace the `?` with the definition.
def sum: Bag → Bag → Bag := ?

theorem testSum1: count (S O) (sum (ofList [1, 2, 3]) (ofList [1, 4, 1])) = ofNat 3 := ?

--| Exercise (bag_functions): replace the `?` with the definition.
def add (v: Nat) (s: Bag): Bag := ?

theorem testAdd1: count (S O) (add (S O) (ofList [1, 4, 1])) = ofNat 3 := ?

theorem testAdd2: count (ofNat 5) (add (S O) (ofList [1, 4, 1])) = O := ?

--| Exercise (bag_functions): replace the `?` with the definition.
def member (v: Nat) (s: Bag): Bool := ?

theorem testMember1: member (S O) (ofList [1, 4, 1]) = True := ?

theorem testMember2: member (ofNat 2) (ofList [1, 4, 1]) = False := ?

-- Exercise: 3 stars, standard, optional (bag_more_functions)
--
-- Some more bag functions to practise with.
--
-- When `removeOne` is applied to a bag without the number to remove, it
-- should give the bag back unchanged. (This exercise is optional, but the
-- advanced track needs `removeOne` for a later exercise.)

--| Exercise (bag_more_functions): replace the `?` with the definition.
def removeOne (v: Nat) (s: Bag): Bag := ?

theorem testRemoveOne1: count (ofNat 5) (removeOne (ofNat 5) (ofList [2, 1, 5, 4, 1])) = O := ?

theorem testRemoveOne2: count (ofNat 5) (removeOne (ofNat 5) (ofList [2, 1, 4, 1])) = O := ?

theorem testRemoveOne3: count (ofNat 4) (removeOne (ofNat 5) (ofList [2, 1, 4, 5, 1, 4])) = ofNat 2 := ?

theorem testRemoveOne4: count (ofNat 5) (removeOne (ofNat 5) (ofList [2, 1, 5, 4, 5, 1, 4])) = S O := ?

--| Exercise (bag_more_functions): replace the `?` with the definition.
def removeAll (v: Nat) (s: Bag): Bag := ?

theorem testRemoveAll1: count (ofNat 5) (removeAll (ofNat 5) (ofList [2, 1, 5, 4, 1])) = O := ?

theorem testRemoveAll2: count (ofNat 5) (removeAll (ofNat 5) (ofList [2, 1, 4, 1])) = O := ?

theorem testRemoveAll3: count (ofNat 4) (removeAll (ofNat 5) (ofList [2, 1, 4, 5, 1, 4])) = ofNat 2 := ?

theorem testRemoveAll4: count (ofNat 5) (removeAll (ofNat 5) (ofList [2, 1, 5, 4, 5, 1, 4, 5, 1, 4])) = O := ?

--| Exercise (bag_more_functions): replace the `?` with the definition.
def included (s1 s2: Bag): Bool := ?

theorem testIncluded1: included (ofList [1, 2]) (ofList [2, 1, 4, 1]) = True := ?

theorem testIncluded2: included (ofList [1, 2, 2]) (ofList [2, 1, 4, 1]) = False := ?

-- Exercise: 2 stars, standard, optional (add_inc_count)
--
-- Adding a value to a bag should increase the value's count by one.
-- State this as a theorem, `addIncCount`, and prove it.
--
--     theorem addIncCount …

-- # Reasoning About Lists
--
-- As with numbers, simple facts about functions on lists can sometimes be
-- proved by computing alone:

theorem nilApp ∀ (l: NatList): app Nil l = l := rfl

-- This works because `Nil` is the value `app` matches on, its "scrutinee",
-- so the `match` in `app` can choose its arm.
--
-- And, as with numbers, it sometimes helps to split an unknown list into
-- its two shapes, empty and non-empty:

theorem tlLengthPred ∀ (l: NatList): pred (length l) = length (tl l) := match l with
  | Nil => rfl
  | Cons n l' => rfl

-- The `Nil` case works because `tl Nil` was chosen to be `Nil`. The arm
-- `Cons n l'` names the two arguments of `Cons`, the head and the tail of
-- the list, as the book's `destruct l as [| n l']` does.
--
-- Usually, though, interesting theorems about lists need induction.
--
-- (The book's micro-sermon: simply *reading* proofs won't help you much.
-- Work through each one, and look at the goal at each point: replace an
-- arm's proof with `?` and run `stitchwort check`, or use the editor's
-- goal view. Otherwise the exercises will make no sense when you get to
-- them.)

-- ## Induction on Lists
--
-- Each data type declaration defines a set of values built up from its
-- constructors: a `Bool` is `True` or `False`, a number is `O` or `S`
-- applied to another number, a list is `Nil` or `Cons` applied to a
-- number and a list. These are the *only* possible shapes of its values.
-- So to show that `P` holds for every list `l`, it is enough to show:
--
-- - that `P` holds of `l` when `l` is `Nil`;
-- - that `P` holds of `l` when `l` is `Cons n l'`, for a number `n` and
--   a smaller list `l'`, assuming that `P` holds of `l'`.
--
-- Larger lists can always be broken down into smaller ones, ending at
-- `Nil`, so the two together show that `P` holds of every list. As with
-- numbers in Induction.sw, the proof is a `match`, and in the `Cons`
-- arm the theorem calls itself on the smaller list `l1'`: that call is
-- the induction hypothesis.

theorem appAssoc ∀ (l1 l2 l3: NatList): app (app l1 l2) l3 = app l1 (app l2 l3) := match l1 with
  | Nil => rfl
  | Cons n l1' => rewrite appAssoc l1' l2 l3 in rfl

-- In the `Cons` arm the goal computes to `Cons n (app (app l1' l2) l3) =
-- Cons n (app l1' (app l2 l3))`; the induction hypothesis rewrites the
-- left side to the right. (`Eq.cong (Cons n) (appAssoc l1' l2 l3)`, which
-- puts a `Cons n` on both sides of the hypothesis, is the same proof.)
--
-- The book observes that its Rocq proof is not illuminating as a static
-- document, since the goal and context at each point are invisible. The
-- term is a little better (the two cases are its two arms), but the goal
-- of each is still unwritten. For comparison, an informal proof:
--
-- *Theorem*: for all lists `l1`, `l2` and `l3`,
-- `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`.
--
-- *Proof*: by induction on `l1`.
--
-- - First, suppose `l1 = []`. We must show
--
--       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
--
--   which follows directly from the definition of `++`.
--
-- - Next, suppose `l1 = n :: l1'`, with
--
--       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
--
--   (the induction hypothesis). We must show
--
--       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
--
--   By the definition of `++`, this follows from
--
--       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
--
--   which is immediate from the induction hypothesis. *Qed*.

-- ## Generalizing Statements
--
-- Sometimes a statement has to be made more general before induction can
-- prove it, because a more general statement gives a more general
-- (stronger) induction hypothesis. If you are stuck in a proof, it may
-- help to step back and try to prove something stronger.
--
--     theorem repeatDoubleFirstTry (c n: Nat): app (repeat n c) (repeat n c) = repeat n (plus c c) := match c with
--       | O => rfl
--       | S c' => ?
--
--     [GOAL] Goal: in `repeatDoubleFirstTry`
--       ╰── n: Nat
--           c': Nat
--           ⊢ Cons n (app (repeat n c') (Cons n (repeat n c'))) = Cons n (repeat n (plus c' (S c')))
--
-- We are stuck. The induction hypothesis, `repeatDoubleFirstTry c' n`, is
-- about `repeat n (plus c' c')`, and the goal has `repeat n (plus c' (S
-- c'))`. If the hypothesis worked for any second summand, the proof would
-- go through. So we generalise:

theorem repeatPlus ∀ (c1 c2 n: Nat): app (repeat n c1) (repeat n c2) = repeat n (plus c1 c2) := match c1 with
  | O => rfl
  | S c1' => rewrite <- repeatPlus c1' c2 n in rfl

-- ## Reversing a List
--
-- A slightly more involved example: a function `rev` that reverses a
-- list, defined with `app`.

def rev (l: NatList): NatList := match l with
  | Nil => Nil
  | Cons h t => app (rev t) (Cons h Nil)

theorem testRev1: rev (ofList [1, 2, 3]) = ofList [3, 2, 1] := rfl

theorem testRev2: rev Nil = Nil := rfl

-- Now let's prove that reversing a list doesn't change its length. The
-- first attempt gets stuck in the `Cons` case:
--
--     theorem revLengthFirstTry (l: NatList): length (rev l) = length l := match l with
--       | Nil => rfl
--       | Cons n l' => ?
--
--     [GOAL] Goal: in `revLengthFirstTry`
--       ╰── n: Nat
--           l': NatList
--           ⊢ length (app (rev l') (Cons n Nil)) = S (length l')
--
-- The goal is an equation about `app`, and nothing we have proved says
-- anything useful about it. The induction hypothesis, `length (rev l') =
-- length l'`, would make a little progress, rewriting `S (length l')` to
-- `S (length (rev l'))`, but no further.
--
-- A first idea is to prove exactly the fact that is missing. But that
-- fails too, because the induction hypothesis isn't general enough:
--
--     theorem appRevLengthSFirstTry (l: NatList) (n: Nat): length (app (rev l) (Cons n Nil)) = S (length (rev l)) := match l with
--       | Nil => rfl
--       | Cons m l' => ?
--
--     [GOAL] Goal: in `appRevLengthSFirstTry`
--       ╰── n: Nat
--           m: Nat
--           l': NatList
--           ⊢ length (app (app (rev l') (Cons m Nil)) (Cons n Nil)) = S (length (app (rev l') (Cons m Nil)))
--
-- The hypothesis is about `app (rev l') (Cons n Nil)`, which doesn't
-- appear. The lemma is more specific than it needs to be: it holds for
-- every list, not only reversed ones.

theorem appLengthS ∀ (l: NatList) (n: Nat): length (app l (Cons n Nil)) = S (length l) := match l with
  | Nil => rfl
  | Cons m l' => rewrite appLengthS l' n in rfl

-- Now the original proof goes through.

theorem revLength ∀ (l: NatList): length (rev l) = length l := match l with
  | Nil => rfl
  | Cons n l' => rewrite appLengthS (rev l') n, revLength l' in rfl

-- `appLengthS` is narrow: its second list has one element. Here is the
-- general version, for any two lists.

theorem appLength ∀ (l1 l2: NatList): length (app l1 l2) = plus (length l1) (length l2) := match l1 with
  | Nil => rfl
  | Cons n l1' => rewrite appLength l1' l2 in rfl

-- For comparison, informal proofs of these two theorems:
--
-- *Theorem*: for all lists `l1` and `l2`, `length (l1 ++ l2) = length l1
-- + length l2`.
--
-- *Proof*: by induction on `l1`.
--
-- - First, suppose `l1 = []`. We must show
--
--       length ([] ++ l2) = length [] + length l2,
--
--   which follows directly from the definitions of `length`, `++` and
--   `plus`.
--
-- - Next, suppose `l1 = n :: l1'`, with
--
--       length (l1' ++ l2) = length l1' + length l2.
--
--   We must show
--
--       length ((n :: l1') ++ l2) = length (n :: l1') + length l2.
--
--   This follows directly from the definitions of `length` and `++`
--   together with the induction hypothesis. *Qed*.
--
-- *Theorem*: for all lists `l`, `length (rev l) = length l`.
--
-- *Proof*: by induction on `l`.
--
-- - First, suppose `l = []`. We must show
--
--       length (rev []) = length [],
--
--   which follows directly from the definitions of `length` and `rev`.
--
-- - Next, suppose `l = n :: l'`, with
--
--       length (rev l') = length l'.
--
--   We must show
--
--       length (rev (n :: l')) = length (n :: l').
--
--   By the definition of `rev`, this follows from
--
--       length ((rev l') ++ [n]) = S (length l'),
--
--   which, by the previous lemma, is the same as
--
--       length (rev l') + length [n] = S (length l').
--
--   This follows directly from the induction hypothesis and the
--   definition of `length`. *Qed*.
--
-- These are long-winded and pedantic. After a few of them, a proof that
-- gives fewer details and highlights only the steps that aren't obvious
-- is easier to follow:
--
-- *Theorem*: for all lists `l`, `length (rev l) = length l`.
--
-- *Proof*: first observe, by a straightforward induction on `l`, that
-- `length (l ++ [n]) = S (length l)` for any `l`. The main property then
-- follows by another induction on `l`, using the observation together
-- with the induction hypothesis in the case where `l = n' :: l'`. *Qed*.
--
-- Which style is better depends on the audience and on how familiar the
-- proof's shape is to them. The pedantic one is a good default for now.

-- ## Search
--
-- To use a theorem in a proof we need its name, and it is often hard to
-- remember what has been proved, let alone what it is called. Rocq's
-- `Search` lists the theorems that mention something, or whose statement
-- has a given shape. Stitchwort's is `stitchwort search`, run in sf/
-- (docs/syntax.md, "Lemma search"):
--
--     stitchwort search 'rev'                                  # everything whose type mentions `rev`
--     stitchwort search 'plus _ _ = plus _ _'                  # equations between two sums
--     stitchwort search 'plus _ _ = plus _ _' --in Sf.Lf.Induction
--     stitchwort search 'plus ?x ?y = plus ?y ?x'              # the same `?x` and `?y` on both sides
--
-- `?x` is a variable of the pattern, standing for the same term wherever
-- it occurs, and `_` for any term. `--in` keeps to one namespace. As with
-- Rocq's `Search` and its `Admitted` theorems, a theorem whose proof is
-- still `?` is listed, marked `(open goal)`, after the finished matches of
-- equal fit: Induction's `addComm` turns up before you have proved it.
-- (`stitchwort search --at FILE:LINE:COLUMN`,
-- at a `?`, lists what might close that goal, though for an exercise
-- that is cheating.)

-- ## List Exercises, Part 1

-- Exercise: 3 stars, standard (list_exercises)
--
-- More practice with lists:

theorem appNilR ∀ (l: NatList): app l Nil = l := ?

theorem revAppDistr ∀ (l1 l2: NatList): rev (app l1 l2) = app (rev l2) (rev l1) := ?

-- An *involution* is a function that is its own inverse: applying it
-- twice gives back the original input.

theorem revInvolutive ∀ (l: NatList): rev (rev l) = l := ?

-- There is a short solution to the next one. If you find yourself
-- getting tangled up, step back and look for a simpler way.

theorem appAssoc4 ∀ (l1 l2 l3 l4: NatList): app l1 (app l2 (app l3 l4)) = app (app (app l1 l2) l3) l4 := ?

-- An exercise about your `nonzeros`:

theorem nonzerosApp ∀ (l1 l2: NatList): nonzeros (app l1 l2) = app (nonzeros l1) (nonzeros l2) := ?

-- Exercise: 2 stars, standard (eqblist)
--
-- Fill in the definition of `eqblist`, which compares lists of numbers
-- for equality, and prove that `eqblist l l` gives `True` for every list
-- `l`.

--| Exercise (eqblist): replace the `?` with the definition.
def eqblist (l1 l2: NatList): Bool := ?

theorem testEqblist1: eqblist Nil Nil = True := ?

theorem testEqblist2: eqblist (ofList [1, 2, 3]) (ofList [1, 2, 3]) = True := ?

theorem testEqblist3: eqblist (ofList [1, 2, 3]) (ofList [1, 2, 4]) = False := ?

theorem eqblistRefl ∀ (l: NatList): True = eqblist l l := ?

-- ## List Exercises, Part 2
--
-- A couple of little theorems about your bag functions.

-- Exercise: 1 star, standard (count_member_nonzero)

theorem countMemberNonzero ∀ (s: Bag): leb (S O) (count (S O) (Cons (S O) s)) = True := ?

-- This lemma about `leb` might help in the next exercise (and later
-- chapters use it too).

theorem lebNSn ∀ (n: Nat): leb n (S n) = True := match n with
  | O => rfl
  | S n' => lebNSn n'

-- In the `S n'` case, `leb (S n') (S (S n'))` computes to `leb n' (S
-- n')`, so the induction hypothesis is the whole proof. (The book's
-- script says the same in three steps: `simpl. rewrite IHn'.
-- reflexivity.`)
--
-- Before the next exercise, fill in `removeOne` above.

-- Exercise: 3 stars, advanced (remove_does_not_increase_count)

theorem removeDoesNotIncreaseCount ∀ (s: Bag): leb (count O (removeOne O s)) (count O s) = True := ?

-- Exercise: 3 stars, standard, optional (bag_count_sum)
--
-- Write down an interesting theorem `bagCountSum` about bags, involving
-- `count` and `sum`, and prove it. (You may find that how hard the proof
-- is depends on how you defined `count`. Hint: if you defined `count`
-- with `eqb`, a `match` can split on any expression, not only a
-- variable: `match h: eqb v n with | True => … | False => …` names the
-- equation `h` in each arm.)
--
--     theorem bagCountSum …

-- Exercise: 3 stars, advanced (involution_injective)
--
-- Prove that every involution is injective. Involutions were defined
-- above, at `revInvolutive`. An *injective* function is one-to-one: it
-- maps distinct inputs to distinct outputs, with no collisions.

theorem involutionInjective ∀ (f: Nat → Nat) (h: ∀ (n: Nat) => n = f (f n)) (n1 n2: Nat) (e: f n1 = f n2): n1 = n2 := ?

-- Exercise: 2 stars, advanced (rev_injective)
--
-- Prove that `rev` is injective. Don't do it by induction, which would
-- be hard. Reuse the technique of `involutionInjective` instead (but not
-- that theorem itself: the types are different).

theorem revInjective ∀ (l1 l2: NatList) (h: rev l1 = rev l2): l1 = l2 := ?

-- # Options
--
-- Suppose we want a function that gives the `n`th element of a list. If
-- its type is `NatList → Nat → Nat`, we have to choose a number to give
-- when the list is too short:

def nthBad (l: NatList) (n: Nat): Nat := match l with
  | Nil => ofNat 42
  | Cons a l' => match n with
    | O => a
    | S n' => nthBad l' n'

-- That's not good: if `nthBad` gives 42, we don't know whether that
-- value is in the list or the arguments were bad. Better to give the
-- result a type with an error value among its outcomes: `NatOption`.

type NatOption =
  | Some (n: Nat)
  | None

-- (The constructors are capitalised following the library's `Option`,
-- the general version of this type, whose `Some` and `None` these hide
-- in this file.)
--
-- `nthError` gives `None` when the list is too short, and `Some a` when
-- `a` is at position `n`.

def nthError (l: NatList) (n: Nat): NatOption := match l with
  | Nil => None
  | Cons a l' => match n with
    | O => Some a
    | S n' => nthError l' n'

theorem testNthError1: nthError (ofList [4, 5, 6, 7]) O = Some (ofNat 4) := rfl

theorem testNthError2: nthError (ofList [4, 5, 6, 7]) (ofNat 3) = Some (ofNat 7) := rfl

theorem testNthError3: nthError (ofList [4, 5, 6, 7]) (ofNat 9) = None := rfl

-- `optionElim` takes the number out of a `NatOption`, giving a default in
-- the `None` case.

def optionElim (d: Nat) (o: NatOption): Nat := match o with
  | Some n' => n'
  | None => d

-- Exercise: 2 stars, standard (hd_error)
--
-- With the same idea, fix `hd` so that it doesn't need a default for the
-- `Nil` case.

--| Exercise (hd_error): replace the `?` with the definition.
def hdError (l: NatList): NatOption := ?

theorem testHdError1: hdError Nil = None := ?

theorem testHdError2: hdError (ofList [1]) = Some (S O) := ?

theorem testHdError3: hdError (ofList [5, 6]) = Some (ofNat 5) := ?

-- Exercise: 1 star, standard, optional (option_elim_hd)
--
-- This relates your `hdError` to the old `hd`.

theorem optionElimHd ∀ (l: NatList) (default: Nat): hd default l = optionElim default (hdError l) := ?
