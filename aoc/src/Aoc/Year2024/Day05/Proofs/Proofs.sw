-- Day 5, part 1 proved, for every print queue: the program's check is the
-- puzzle's "in the right order", so part 1 adds up the middle pages it asks
-- for. Part 2 is in Part2.sw.

namespace Aoc.Year2024.Day05.Proofs
import Aoc.Year2024.Day05 (..)
import Aoc.Year2024.Day05.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Map, Nat, Not, Set, Void)

-- Two pairs of numbers are equal when both parts are.
theorem pairEqual (a: Nat) (b: Nat) (c: Nat) (d: Nat): ((a, b) == (c, d)) = (a == c && b == d) :=
  match Nat.decEq a c, Nat.decEq b d with
    | Yes p, Yes q => rfl
    | Yes p, No r => rfl
    | No r, dq => rfl

-- Looking a pair up in the rule set is asking whether some rule says so.
theorem mustPrecedeCorrect (rules: List Rule) (x: Nat) (y: Nat): mustPrecede (ruleSet rules) x y = ruleSays rules x y :=
  let pairOf := (rule: Rule) => (rule.before, rule.after)
  rewrite Set.containsFromList (x, y) (rules.map pairOf), List.anyMap rules (pair => Map.Spec.sameKey (x, y) pair) pairOf
    in List.anyCong rules (rule => Map.Spec.sameKey (x, y) (pairOf rule)) (rule => rule.before == x && rule.after == y)
      (rule => rewrite Map.Spec.sameKeyDecide (x, y) (pairOf rule) in pairEqual rule.before rule.after x y)

-- A test that every element passes.
theorem allTrue: (xs: List a) → (p: a → Bool) → ((x: a) → p x = True) → xs.all p = True
  | Nil, p, h => rfl
  | Cons x xs, p, h => rewrite h x in allTrue xs p h

-- A test that no element passes.
theorem anyFalse: (xs: List a) → (p: a → Bool) → ((x: a) → p x = False) → xs.any p = False
  | Nil, p, h => rfl
  | Cons x xs, p, h => rewrite h x in anyFalse xs p h

-- Every element passes both tests when every element passes each.
theorem allAnd: (xs: List a) → (p: a → Bool) → (q: a → Bool) → xs.all (x => p x && q x) = (xs.all p && xs.all q)
  | Nil, p, q => rfl
  | Cons x xs, p, q =>
    match px: p x, qx: q x with
      | True, True => allAnd xs p q
      | True, False => cases
      | False, qx => rfl

-- "No x is related to any y" read either way round.
theorem noneRelated (related: a → b → Bool): (xs: List a) → (ys: List b) →
    xs.all (x => !(ys.any (y => related x y))) = ys.all (y => !(xs.any (x => related x y)))
  | Nil, ys => Eq.sym (allTrue ys (y => True) (y => rfl))
  | Cons x xs, ys =>
    let unfolded := List.allCong ys (y => !(List.any (Cons x xs) (x2 => related x2 y))) (y => !(related x y) && !(xs.any (x2 => related x2 y)))
      (y =>
        match r: related x y with
          | True => rfl
          | False => rfl)
    rewrite unfolded, allAnd ys (y => !(related x y)) (y => !(xs.any (x2 => related x2 y))), <- noneRelated related xs ys,
      List.allNotAny ys (y => !(related x y))
      in rewrite List.anyCong ys (y => !(!(related x y))) (y => related x y) (y => cases) in rfl

-- A rule is broken only by an update with both of its pages.
theorem brokenHasBoth (x: Nat) (y: Nat): (pages: List Nat) → printedBefore x y pages = False →
    And (pages.any (== x) = True) (pages.any (== y) = True)
  | Nil, broken => Void.exfalso (Bool.trueNotFalse broken)
  | Cons page later, broken =>
    match laterBroken: printedBefore x y later with
      | False =>
        match brokenHasBoth x y later laterBroken with
          | Both hasX hasY => Both (List.anyConsEqTrue page x later hasX) (List.anyConsEqTrue page y later hasY)
      | True =>
        match isY: page == y, hasX: later.any (== x) with
          | True, True => Both (cases) rfl
          | True, False => cases
          | False, hasX => cases

-- So the puzzle's "if both pages are in the update" adds nothing.
theorem followsRuleIsPrintedBefore (pages: List Nat) (rule: Rule): followsRule pages rule = printedBefore rule.before rule.after pages :=
  match printed: printedBefore rule.before rule.after pages with
    | True => cases
    | False =>
      match brokenHasBoth rule.before rule.after pages printed with
        | Both hasBefore hasAfter => rewrite hasBefore, hasAfter in rfl

-- `inOrder` depends only on what the test says.
theorem inOrderCong (precedes1: Nat → Nat → Bool) (precedes2: Nat → Nat → Bool) (same: (x: Nat) → (y: Nat) → precedes1 x y = precedes2 x y):
    (pages: List Nat) → inOrder precedes1 pages = inOrder precedes2 pages
  | Nil => rfl
  | Cons page later =>
    rewrite List.allCong later (laterPage => !(precedes1 laterPage page)) (laterPage => !(precedes2 laterPage page)) (laterPage => rewrite same laterPage page in rfl),
      inOrderCong precedes1 precedes2 same later
      in rfl

-- No later page is the rule's first page while this one is its second: this
-- page isn't the rule's second page, or the first page doesn't follow it.
theorem ruleKept (rule: Rule) (page: Nat) (later: List Nat):
    !(later.any (laterPage => rule.before == laterPage && rule.after == page)) = (!(page == rule.after) || !(later.any (== rule.before))) :=
  rewrite DecEq.eqComm page rule.after in
    match isPage: rule.after == page with
      | True =>
        Eq.cong (found => !found)
          (List.anyCong later (laterPage => rule.before == laterPage && True) (== rule.before)
            (laterPage => rewrite DecEq.eqComm rule.before laterPage in cases))
      | False => rewrite anyFalse later (laterPage => rule.before == laterPage && False) (laterPage => cases) in rfl

-- No later page has a rule putting it before this one: every rule about this
-- page is kept by it.
theorem noRuleBroken (rules: List Rule) (page: Nat) (later: List Nat):
    later.all (laterPage => !(ruleSays rules laterPage page)) = rules.all (rule => !(page == rule.after) || !(later.any (== rule.before))) :=
  Eq.trans (noneRelated (laterPage rule => rule.before == laterPage && rule.after == page) later rules)
    (List.allCong rules (rule => !(later.any (laterPage => rule.before == laterPage && rule.after == page)))
      (rule => !(page == rule.after) || !(later.any (== rule.before))) (rule => ruleKept rule page later))

-- The program's check, by the rules as written, is "every rule is kept".
theorem inOrderPrintedBefore (rules: List Rule): (pages: List Nat) → inOrder (ruleSays rules) pages = rules.all (rule => printedBefore rule.before rule.after pages)
  | Nil => Eq.sym (allTrue rules (rule => printedBefore rule.before rule.after Nil) (rule => rfl))
  | Cons page later =>
    let keptHere := rules.all (rule => printedBefore rule.before rule.after later)
    Eq.trans (Eq.cong (keptLater => later.all (laterPage => !(ruleSays rules laterPage page)) && keptLater) (inOrderPrintedBefore rules later))
      (Eq.trans (Eq.cong (keptByPage => keptByPage && keptHere) (noRuleBroken rules page later))
        (Eq.sym (allAnd rules (rule => !(page == rule.after) || !(later.any (== rule.before))) (rule => printedBefore rule.before rule.after later))))

-- The check by the rules as written is the puzzle's "in the right order".
theorem inOrderRuleSays (rules: List Rule) (update: Update): inOrder (ruleSays rules) update.pages = rightOrder rules update :=
  rewrite inOrderPrintedBefore rules update.pages
    in List.allCong rules (rule => printedBefore rule.before rule.after update.pages) (followsRule update.pages)
      (rule => Eq.sym (followsRuleIsPrintedBefore update.pages rule))

-- So is the program's check, by the rule set.
theorem inOrderCorrect (rules: List Rule) (update: Update): inOrder (mustPrecede (ruleSet rules)) update.pages = rightOrder rules update :=
  Eq.trans (inOrderCong (mustPrecede (ruleSet rules)) (ruleSays rules) (mustPrecedeCorrect rules) update.pages) (inOrderRuleSays rules update)

-- Part 1 adds up the middle pages of the updates in the right order.
theorem part1Correct (queue: PrintQueue): solvePart1 queue = middlesOfOrdered queue :=
  rewrite List.filterCongMem queue.updates (update => inOrder (mustPrecede (ruleSet queue.rules)) update.pages) (rightOrder queue.rules)
    (queued inQueue => inOrderCorrect queue.rules queued)
    in rfl
