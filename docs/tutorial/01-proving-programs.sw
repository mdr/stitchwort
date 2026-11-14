-- Proving things about programs, part 1: a shopping basket
--
-- This file is a tutorial. Open it in VS Code and read it from top to
-- bottom; each step tells you what to do in the editor. It takes about
-- 30 to 45 minutes. You need to know how to program, but nothing about
-- theorem proving.
--
-- As committed, every proof in the file is finished, so the file checks.
-- The exercises ask you to take a proof apart, break the program, or type
-- a variant that is given in a comment, and then to put it back.

-- ## Step 1. Setup
--
-- From a checkout of the Stitchwort repository:
--
--     nix develop -c task vscode:install
--
-- This builds the `stitchwort` program and installs the VS Code
-- extension; run it again after pulling, so the two stay in step. Put
-- `target/release` on your PATH, or set the setting `stitchwort.path` to
-- `target/release/stitchwort`, then run "Developer: Reload Window" from
-- the command palette (Cmd-Shift-P, or Ctrl-Shift-P).
--
-- Check that it works: in Step 2, hover over `cost` in `def Item.cost`.
-- A box shows `def Main.Item.cost (item: Item): Nat` and its doc comment
-- (a file on its own is the namespace `Main`). If nothing shows, look at
-- the "Stitchwort" channel in the Output panel: it is the language
-- server's log.
--
-- A few more things to try now, as you'll use them throughout:
--
-- - Hover over a use of a name, such as `totalOf` in its own second arm:
--   the box shows its type, its doc, and the equations the compiler made
--   from its arms (`totalOf.eq2`), which proofs can use.
-- - F12 on a name jumps to its definition, including into the standard
--   library; Shift-F12 lists its uses.
-- - Cmd-Shift-O (Ctrl-Shift-O) lists the declarations of this file.
-- - Above each `test` there is a "▶ Run test" link (above the first also
--   "▶ Run tests", and "▶ Run" above `main`): click it to run that test
--   and see the result.
-- - Errors show as red squiggles as you type, without saving. The
--   Problems panel (Cmd-Shift-M, Ctrl-Shift-M) lists them in full.
--
-- The command line works too. In a terminal, in this folder:
--
--     stitchwort check 01-proving-programs.sw
--     stitchwort test 01-proving-programs.sw

import Std (List, Nat)

-- ## Step 2. A small program
--
-- A basket holds items; each item has a price in pence and a count. A
-- coupon takes something off the total.

type Item = { name: Text, pence: Nat, count: Nat }

--| What the basket's line for this item costs, in pence.
def Item.cost (item: Item): Nat := item.pence * item.count

--| The cost of every item, in pence.
def totalOf: List Item → Nat
  | [] => 0
  | [item, ..rest] => item.cost + totalOf rest

type Basket = { items: List Item }

def Basket.empty: Basket := { items = [] }

def Basket.add (basket: Basket) (item: Item): Basket := { items = [item, ..basket.items] }

--| Two baskets put together at the till.
def Basket.merge (basket other: Basket): Basket := { items = basket.items ++ other.items }

def Basket.total (basket: Basket): Nat := totalOf basket.items

type Coupon = | NoCoupon | PenceOff (pence: Nat) | PercentOff (percent: Nat)

--| What is left to pay of `total` pence. `-` on `Nat` stops at 0, so a
--| coupon worth more than the basket makes it free.
def Coupon.apply (coupon: Coupon) (total: Nat): Nat := match coupon with
  | NoCoupon => total
  | PenceOff pence => total - pence
  | PercentOff percent => total - total * percent / 100

def tea: Item := { name = "tea", pence = 250, count = 2 }
def milk: Item := { name = "milk", pence = 90, count = 1 }
def shopping: Basket := Basket.empty.add tea |>.add milk

-- Tests are `Bool` expressions run by `stitchwort test`. Run them now from
-- a terminal (Step 1 has the command), or with "▶ Run tests": they all
-- pass. The editor checks that a test's types are right, but doesn't run
-- it as you type: change `590` to `600` below and nothing turns red until
-- you click "▶ Run test", which then marks the failing test in the file
-- (`stitchwort test` reports it too). Put it back afterwards.

test "the total adds up each line" := shopping.total == 590
test "pence off" := (PenceOff 100).apply shopping.total == 490
test "a big coupon makes it free" := (PenceOff 1000).apply shopping.total == 0
test "ten percent off" := (PercentOff 10).apply shopping.total == 531

-- ## Step 3. First theorems
--
-- A test checks one input. A theorem states a fact for every input, and
-- the checker checks its proof. A theorem looks like a definition: after
-- the name and parameters comes its statement, and after `:=` its proof.
--
-- The simplest proof is `rfl`: both sides of the `=` compute to the same
-- value. Here that's a test written as a theorem:

theorem shoppingTotal: shopping.total = 590 := rfl

-- `rfl` also works when the statement has variables, as long as computing
-- needs nothing more than the definitions. Adding an item puts it at the
-- front of the list, and `totalOf` has an arm for exactly that shape, so
-- this holds by computing, for every basket and every item:

theorem addCost ∀ (basket: Basket) (item: Item): (basket.add item).total = item.cost + basket.total := rfl

theorem emptyTotal: Basket.empty.total = 0 := rfl

-- Hover over the name `addCost`: the box shows the statement as you wrote
-- it. The dot form `basket.add item` is a call of `Basket.add`, and some
-- messages write it that way, as `Basket.total shopping`. Hover over
-- `rfl` for what `rfl` is.

-- ## Step 4. Holes: let the checker tell you what's needed
--
-- You rarely know a whole proof before you start. Write `?` where a part
-- is missing, and the checker tells you the goal there: the names in scope
-- with their types, and after `⊢`, what has to go in place of the `?`.
--
-- The theorem below says a coupon never makes you pay more. Its proof is
-- finished; take it apart to see how it was built:
--
-- 1. Select everything after `:=` in `couponNeverAdds` and type `?`.
--    The `?` gets a blue underline: an open goal, not an error. Hover over
--    it. The box shows
--
--        in `couponNeverAdds`
--        coupon: Coupon
--        total: Nat
--        ⊢ coupon.apply total ≤ total
--
--    The goal is the statement, as you wrote it.
--
--    For a goal that follows the cursor, run "Stitchwort: Show Goals" from
--    the command palette: a panel opens beside the editor, and shows the
--    goal of whichever `?` you are in or near. Keep it open from here on.
--
-- 2. `coupon.apply` is a `match` on the coupon, so the proof is too. Replace
--    the `?` with
--
--        match coupon with
--          | NoCoupon => ?
--
--    A red squiggle says the `match` is missing cases (`E-NONEXHAUSTIVE`).
--    Put the cursor on `match` and press Cmd-. (Ctrl-.), or click the
--    light bulb: "Add the missing arms" writes them for you, each with `?`.
--
-- 3. Now there are three goals, one per coupon. Move between them and watch
--    the Goals panel: in the `NoCoupon` arm the goal is `total ≤ total`,
--    and in the `PenceOff` arm `total - pence ≤ total`. In each arm the
--    checker knows which coupon it is, so `coupon.apply` has computed.
--
-- 4. These are all arithmetic, which `omega` proves: `+`, `-`,
--    comparisons, and multiplying or dividing by a constant, using every
--    fact in scope. Put the cursor on one of the `?`s and press Cmd-. again:
--    on a goal, the light bulb offers proofs that close it, each already
--    checked ("Replace ? with `omega` (closes it alone)"). Pick it, or type
--    `omega` yourself, in each arm. (Cmd-. on the single `?` of step 1
--    offers `cases`, which is the next paragraph.)

theorem couponNeverAdds ∀ (coupon: Coupon) (total: Nat): coupon.apply total ≤ total := match coupon with
  | NoCoupon => omega
  | PenceOff pence => omega
  | PercentOff percent => omega

-- `cases` does steps 2 to 4 in one go: it splits on whatever the goal is
-- stuck on, as `match` would, and closes each case by computing, by a
-- hypothesis, or by `omega`. Try replacing the whole proof above with
-- `cases`. Use it when the cases are routine; write the `match` when you
-- want to see them.

-- ## Step 5. Induction is recursion
--
-- `totalOf` walks a list, and so does a proof about it. Here is the fact
-- that merging two baskets adds their totals, built up from `?` the same
-- way. Take `totalAppend`'s proof apart again, and follow along:
--
-- 1. The proof has two arms, as `totalOf` has: a theorem whose statement
--    ends `∀ (items: List Item) => …` can have arms, as a function can.
--    Replace each arm's proof with `?`:
--
--        | [] => ?
--        | [item, ..rest] => ?
--
--    The first goal is
--    `totalOf others = totalOf others`: `totalOf []` computed to `0`, and
--    `0 + n` to `n`. That's `rfl`.
--
-- 2. The second goal, in the Goals panel, is
--
--        ⊢ item.cost + totalOf (rest ++ others) = item.cost + totalOf rest + totalOf others
--
--    The left side has `totalOf (rest ++ others)`, which is this same
--    theorem for the shorter list `rest`. Calling the theorem on `rest`
--    is how induction is written: `totalAppend others rest` is the
--    induction hypothesis, and the checker makes sure the recursion gets
--    smaller, as it does for any function.
--
-- 3. `rewrite p` uses an equation `p: a = b` to replace `a` with `b` in
--    the goal, and then tries `rfl` on what's left. Write
--    `rewrite totalAppend others rest` in the second arm. It is red,
--    with `E-REFL`: hover over it, and the last note shows the goal after
--    rewriting,
--    `item.cost + (totalOf rest + totalOf others) = item.cost + totalOf rest + totalOf others`.
--    It's the same sum, bracketed differently. `Nat.addAssoc` is the
--    library's lemma that moves the brackets (F12 on it shows its
--    statement), and `rewrite` takes several equations, used in order.
--    That gives the proof below.
--
--    `omega [totalAppend others rest]` proves it too: `omega` with an
--    extra fact. Try it.

theorem totalAppend ∀ (others: List Item):
    ∀ (items: List Item) => totalOf (items ++ others) = totalOf items + totalOf others
  | [] => rfl
  | [item, ..rest] => rewrite totalAppend others rest, Nat.addAssoc

-- With the lemma proved, the fact about baskets needs no work of its own.

theorem mergeTotal ∀ (basket other: Basket): (basket.merge other).total = basket.total + other.total :=
  totalAppend other.items basket.items

-- `Basket.total` and `Basket.merge` compute straight to `totalOf` and
-- `++`, so this statement already is `totalAppend`'s, for the two
-- baskets' items. Hover over `mergeTotal` and over `totalAppend` to
-- compare them.

-- ## Step 6. Side conditions and `auto`
--
-- Splitting the bill only makes sense with at least one person. The
-- parameter `[auto someone: people ≠ 0]` is a proof the caller has to
-- give, but doesn't write: the checker finds it itself, by deciding the
-- statement when the numbers are known, or from a fact in scope.

def Basket.share (basket: Basket) (people: Nat) [auto someone: people ≠ 0]: Nat := basket.total / people

test "shared three ways" := shopping.share (people := 3) == 196

-- Here `auto` decided `3 ≠ 0`. In `shareAtMost` it uses the hypothesis
-- `someone`, which says the same thing. The proof is a lemma from the
-- library; to find such lemmas, put the cursor on a `?` and press Cmd-.,
-- or run `stitchwort search --at 01-proving-programs.sw:LINE` in a
-- terminal, with the line of the `?`.

theorem shareAtMost ∀ (basket: Basket) (people: Nat) (someone: people ≠ 0): basket.share people ≤ basket.total :=
  Nat.divLe basket.total people

-- ## Step 7. Mistakes on purpose
--
-- The point of a proof about a program is that it breaks when the program
-- does. Try each of these, read the error, then put things back.
--
-- **Break 1: a coupon that adds.** In `Coupon.apply`, change the
-- `PenceOff` arm to `total + pence` (a sign slip). `couponNeverAdds` turns
-- red, at its `PenceOff` arm:
--
--     [E-OMEGA] `omega` can't prove `total + pence ≤ total`
--
-- Hover over the red `omega` to read the notes. The third is `omega`'s
-- own guess at values that break it (it says it may not be real). The
-- last is different: the checker ran the statement itself and found
--
--     this statement is false; a counterexample:
--       coupon = PenceOff 1
--       total = 0
--
-- When a note says the statement is false, no proof will work: fix the
-- program, or the statement. Fix it: change `+` back to `-`. The test
-- "pence off" catches this bug too, but only when the tests run, and
-- only for that one basket.
--
-- **Break 2: a basket that forgets.** Change `Basket.add` to keep the old
-- items and drop the new one: `{ items = basket.items }`. Two theorems
-- turn red. `shoppingTotal` says the left side computed to `0`, not
-- `590`. `addCost` says
--
--     [E-REFL] `rfl` can't prove this
--     `(basket.add item).total` and `item.cost + basket.total` aren't equal
--
-- and its notes show what each side computed to, `totalOf basket.items`
-- against `item.pence * item.count + totalOf basket.items`, then a
-- counterexample: an empty basket and an item costing 1. Put `Basket.add`
-- back.
--
-- **Break 3: share between nobody.** Uncomment this test:
--
--     test "nobody pays" := shopping.share (people := 0) == 0
--
-- `auto` decides `0 ≠ 0` and finds it false (`E-AUTO-FALSE`): the call is
-- rejected before anything runs. Comment it out again.
--
-- **Break 4: the wrong hypothesis.** In `totalAppend`'s second arm,
-- replace the proof with `totalAppend others rest`. It is the induction
-- hypothesis, but not the goal: `E-TYPE-MISMATCH` shows the type it
-- expected and the type it got, side by side. Comparing them is how you
-- see what's left to do (here, adding `item.cost` to both sides). Put the
-- proof back.

-- ## Step 8. Wrapping up
--
-- You have seen:
--
-- - a theorem is a test for every input, checked as you type;
-- - `rfl` proves what computes, `omega` arithmetic, `cases` routine case
--   splits;
-- - `?` shows a goal; the Goals panel follows the cursor, and Cmd-. on a
--   `?` offers checked proofs;
-- - a proof by `match` follows the program's own cases; a proof about a
--   list calls itself on the rest, which is induction;
-- - `rewrite` uses an equation, from the library or your own lemma;
-- - `[auto …]` parameters are proofs the checker finds;
-- - when the program is wrong, the proof breaks, often with a
--   counterexample.
--
-- Next, in part 2: specs. So far the theorems said things about the
-- program in its own terms. Part 2 writes down what a correct checkout is,
-- separately from the code, and proves the code meets it, with
-- `stitchwort check --counterexamples` to try a statement before proving it.
--
-- More: docs/guide/10-proofs.md (the guide's chapter on proofs) and
-- docs/syntax.md (the reference).
