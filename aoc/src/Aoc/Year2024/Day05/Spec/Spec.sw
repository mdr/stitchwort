-- Day 5 as the puzzle states it. The proofs (Proofs/) show the program
-- computes these, for every print queue (part 2 under the assumption below).

namespace Aoc.Year2024.Day05.Spec
import Aoc.Year2024.Day05 (..)
import Std (And, Bool, List, Nat, Not)

-- "Page number X must be printed at some point before page number Y": no
-- copy of Y comes before a copy of X.
def printedBefore (x: Nat) (y: Nat): List Nat → Bool
  | Nil => True
  | Cons page later => (!(page == y) || !(later.any (== x))) && printedBefore x y later

-- "The notation X|Y means that if both page number X and page number Y are to
-- be produced as part of an update, page number X must be printed at some
-- point before page number Y."
def followsRule (pages: List Nat) (rule: Rule): Bool :=
  !(pages.any (== rule.before) && pages.any (== rule.after)) || printedBefore rule.before rule.after pages

-- "Determine which updates are already in the right order": those that follow
-- every rule.
def rightOrder (rules: List Rule) (update: Update): Bool := rules.all (followsRule update.pages)

-- "What do you get if you add up the middle page number from those
-- correctly-ordered updates?"
def middlesOfOrdered (queue: PrintQueue): Nat := queue.updates.filter (rightOrder queue.rules) |> .sumBy .middlePage

-- "Use the page ordering rules to put the page numbers in the right order":
-- the same pages, in the right order.
def CorrectOrdering (rules: List Rule) (update: Update) (ordered: Update): Prop :=
  And (List.Perm ordered.pages update.pages) (rightOrder rules ordered = True)

-- "Find the updates which are not in the correct order. What do you get if
-- you add up the middle page numbers after correctly ordering just those
-- updates?", with `ordering` putting each in order.
def middlesOfReordered (queue: PrintQueue) (ordering: Update → Update): Nat :=
  queue.updates.filter (update => !(rightOrder queue.rules update))
    |> .map ordering
    |> .sumBy .middlePage

-- Whether there is a rule X|Y with these pages.
def ruleSays (rules: List Rule) (x: Nat) (y: Nat): Bool := rules.any (rule => rule.before == x && rule.after == y)

-- The puzzle doesn't say so, but part 2 needs it, and it holds on the real
-- input: on each update's pages the rules are a strict total order. No two
-- pages are ordered both ways, any two different pages are ordered one way,
-- and the order is transitive. On all pages, the rules aren't transitive.
def Asymmetric (rules: List Rule) (pages: List Nat): Prop :=
  (x: Nat) → (y: Nat) → x ∈ pages → y ∈ pages → ruleSays rules x y = True → ruleSays rules y x = False

def Total (rules: List Rule) (pages: List Nat): Prop :=
  (x: Nat) → (y: Nat) → x ∈ pages → y ∈ pages → Not (x = y) → ruleSays rules x y = False → ruleSays rules y x = True

def Transitive (rules: List Rule) (pages: List Nat): Prop :=
  (x: Nat) → (y: Nat) → (z: Nat) → x ∈ pages → y ∈ pages → z ∈ pages →
    ruleSays rules x y = True → ruleSays rules y z = True → ruleSays rules x z = True

def StrictTotalOrderOn (rules: List Rule) (pages: List Nat): Prop :=
  And (Asymmetric rules pages) (And (Total rules pages) (Transitive rules pages))
