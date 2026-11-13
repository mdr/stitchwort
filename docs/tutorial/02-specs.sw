-- Proving things about programs, part 2: specs
--
-- This is the second part of the tutorial; part 1 is
-- 01-proving-programs.sw, and this part assumes you've done it. As
-- before, open the file in VS Code and read it from top to bottom; it takes
-- about 30 to 45 minutes.
--
-- Part 1's theorems described the program in its own terms: what `add`
-- does to `total`, what `merge` does. This part writes down, separately
-- from the code, what a correct checkout is, and proves that the code
-- meets it. That separate description is a *spec* (a specification).
--
-- As committed, every proof in the file is finished, so the file checks.
-- The exercises ask you to type a statement given in a comment, take a
-- proof apart, or break the program, and then to put things back.

-- ## Step 1. Setup
--
-- The same as part 1: the editor shows goals and errors as you type, and
-- in a terminal, in this folder,
--
--     stitchwort check 02-specs.sw
--     stitchwort test 02-specs.sw
--
-- check and test the file. This part adds one command, in Step 4.

import Std (List, Nat, Exists)

-- ## Step 2. The program: a till
--
-- The shop's types are part 1's: a file on its own can't import another
-- file, so they're repeated here.

type Item = {
  name: Text,
  pence: Nat,
  count: Nat
}

--| What the basket's line for this item costs, in pence.
def Item.cost (item: Item): Nat := item.pence * item.count

type Basket = { items: List Item }

type Coupon =
  | NoCoupon
  | PenceOff (pence: Nat)
  | PercentOff (percent: Nat)

--| What is left to pay of `total` pence. `-` on `Nat` stops at 0.
def Coupon.apply (coupon: Coupon) (total: Nat): Nat := match coupon with
  | NoCoupon => total
  | PenceOff pence => total - pence
  | PercentOff percent => total - total * percent / 100

-- What's new is the till. It works the way a real till does: it scans the
-- items one at a time and keeps a running total, so it never needs to look
-- back at an item it has passed. `scan running items` carries on from a
-- running total of `running` pence.

--| The till's loop: `running` is the total of the items scanned so far.
def scan (running: Nat): List Item → Nat
  | [] => running
  | [item, ..rest] => scan (running + item.cost) rest

--| What the till charges: every item scanned, then the coupon.
def Basket.checkout (basket: Basket) (coupon: Coupon): Nat := scan 0 basket.items |> coupon.apply

def tea: Item := { name = "tea", pence = 250, count = 2 }
def milk: Item := { name = "milk", pence = 90, count = 1 }
def shopping: Basket := { items = [tea, milk] }

test "the till adds up each line" := shopping.checkout NoCoupon == 590
test "the till takes the coupon off" := shopping.checkout (PenceOff 100) == 490

-- ## Step 3. The spec: what a correct checkout is
--
-- The tests pass, for one basket. Is the till right for every basket? To
-- say what "right" means, write it down a second time, in the plainest way
-- you can: the cost of each line, added up, less the coupon. This is the
-- spec. It is a definition like any other, but its job is different: it
-- should be obviously correct when you read it. It's never run at the
-- till, so it can be as slow or as wasteful as clarity needs.
--
-- `totalOf` is part 1's: the first line's cost plus the rest's. It needs
-- no running total; you can check each arm against the sentence above.

--| The cost of every item, line by line, in pence.
def totalOf: List Item → Nat
  | [] => 0
  | [item, ..rest] => item.cost + totalOf rest

--| What a checkout should charge: the cost of each line, added up, less
--| the coupon.
def Basket.shouldCharge (basket: Basket) (coupon: Coupon): Nat := totalOf basket.items |> coupon.apply

-- The theorem to aim for says that the till charges what it should, for
-- every basket and every coupon:
--
--     theorem checkoutCorrect (basket: Basket) (coupon: Coupon):
--       basket.checkout coupon = basket.shouldCharge coupon
--
-- It's proved at the end of Step 6. The spec uses two pieces of the
-- program, `Item.cost` and `Coupon.apply`, as if they were obviously
-- right; Step 8 shows what that costs.

-- ## Step 4. Try a statement before proving it
--
-- A proof can take a while to find, and a false statement has none. So
-- try the statement first: write it with `?` as its proof. Type this at the
-- end of the file:
--
--     theorem scanIsTotal (items: List Item): scan 0 items = totalOf items := ?
--
-- Hover over the `?`: the goal is the statement, with no note under it.
-- When a `?`'s statement is false, the checker usually says so there: it
-- runs the statement on many inputs, as part 1's breaks showed. To see
-- that, break the till: in `scan`'s second arm, change `item.cost` to
-- `item.pence`, a till that forgets to multiply by the count. Now the
-- hover on the `?` ends with
--
--     this statement is false; a counterexample:
--       items = [{ name = "", pence = 1, count = 0 }]
--     `scan 0 items = totalOf items` is false:
--       left:  1
--       right: 0
--
-- One item, at 1p, of which the customer took none: the till charges 1p,
-- the spec says 0. A counterexample is a test case the checker wrote for
-- you, and the smallest it could find. (Further down, `scanAdds` turns
-- red too, with the same counterexample: it's a proof about `scan`, which
-- Step 6 explains.)
--
-- The command line runs the same search on every theorem of a file,
-- proved or not, with more inputs. Run it in a terminal:
--
--     stitchwort check --counterexamples 02-specs.sw
--
-- After the errors and goals it prints a line for each statement found
-- false, among them
--
--     ✗ scanIsTotal  counterexample: items = [{ name = "", pence = 1, count = 0 }]
--
-- and then a count. Put `item.cost` back and run it again: the `✗` lines
-- are gone. Add `--verbose` for a line per theorem; `scanIsTotal`'s is
--
--     ~ scanIsTotal  none in 10000 cases (sizes up to 40; evidence, not a proof)
--
-- (You'll also see lines for `Item.ext` and `Basket.ext`: theorems the
-- compiler makes for every record type, saying two records with equal
-- fields are equal. Ignore them here.)
--
-- `~` means no counterexample in 10,000 tries, with lists of up to 40
-- items. That's good evidence, and only evidence: it is not a proof, and
-- `check` still fails while the `?` is open. Delete `scanIsTotal` before
-- going on; Step 5 proves it.

-- ## Step 5. The first try, and why it fails
--
-- `scan` walks a list, so the proof is by induction, as `totalAppend` was
-- in part 1: arms for `[]` and `[item, ..rest]`, the second calling the
-- theorem on `rest`. Type this at the end of the file:
--
--     theorem scanFirstTry: ∀ (items: List Item) => scan 0 items = totalOf items
--       | [] => rfl
--       | [item, ..rest] => ?
--
-- The `[]` arm is `rfl`: both sides compute to `0`. Hover over the second
-- `?`:
--
--     item: Item
--     rest: List Item
--     ⊢ scan (item.pence * item.count) rest = item.cost + totalOf rest
--
-- `scan 0 [item, ..rest]` took one step, to `scan (0 + item.cost) rest`,
-- and computing went on into `0 + item.cost`, which is
-- `item.pence * item.count`: the same number as the `item.cost` on the
-- right, written out.
--
-- The induction hypothesis `scanFirstTry rest` says
-- `scan 0 rest = totalOf rest`. Try it: replace the `?` with
-- `rewrite scanFirstTry rest`. It's red:
--
--     [E-REWRITE-NOTHING] `rewrite` found no `scan 0 rest` in the goal
--
-- and the error's notes show the goal again. The goal scans `rest` from a
-- running total of `item.cost`; the hypothesis only knows about scanning
-- from `0`. After one item, the till is never at `0` again, so a theorem
-- about starting from `0` can't follow it. Delete `scanFirstTry`.

-- ## Step 6. Say what the loop does from anywhere
--
-- The fix is to prove more. Say what `scan` does from *any* running total:
-- it adds the items' total to it. That is a statement about every `running`
-- and every list, so it starts with `∀` and has two variables; its arms
-- match on both, as a function of two arguments would.

theorem scanAdds: ∀ (running: Nat) (items: List Item) => scan running items = running + totalOf items
  | running, [] => rfl
  | running, [item, ..rest] => omega [scanAdds (running + item.cost) rest]

-- Take it apart as before: replace the second arm's proof with `?`. The
-- goal is
--
--     ⊢ scan (running + item.cost) rest = running + (item.cost + totalOf rest)
--
-- and now the induction hypothesis fits: `scanAdds` itself, called on the
-- running total the till has reached, `running + item.cost`, and the
-- shorter list. It says
-- `scan (running + item.cost) rest = running + item.cost + totalOf rest`,
-- and what's left is moving brackets, which `omega` does when it's given
-- the hypothesis as a fact. Put the proof back.
--
-- Making a statement more general so that its induction goes through is
-- the most common move in proofs about loops. When the induction
-- hypothesis is about a different starting point from the goal's, ask what
-- the loop does from any starting point.
--
-- The theorem you wanted is now one case of `scanAdds`, from `0`:

theorem checkoutCorrect ∀ (basket: Basket) (coupon: Coupon): basket.checkout coupon = basket.shouldCharge coupon :=
  rewrite scanAdds 0 basket.items

-- `rewrite` replaces `scan 0 basket.items` with `0 + totalOf basket.items`,
-- and then both sides compute to the same thing. Hover over
-- `checkoutCorrect`: the statement mentions only `checkout`, which callers
-- use, and `shouldCharge`, the spec. `scan` and `scanAdds` are how it was
-- proved, which a reader of the statement needn't know.

-- ## Step 7. Specs as properties: `∀`, `∧` and `∃`
--
-- A spec doesn't have to be a second program. Often it's a property that
-- every input should have. Coupons are a good place for these.
--
-- **A property that's false.** Applying two percentage coupons is
-- multiplying by two numbers, and multiplying doesn't care about order,
-- so surely the order of the coupons doesn't matter. Try it; type
--
--     theorem percentOrder (first: Nat) (second: Nat) (total: Nat):
--       (PercentOff second).apply ((PercentOff first).apply total)
--         = (PercentOff first).apply ((PercentOff second).apply total) := ?
--
-- and hover over the `?`:
--
--     this statement is false; a counterexample:
--       first = 1
--       second = 2
--       total = 101
--
-- 1% off £1.01 leaves 100p, then 2% off that leaves 98p. 2% off £1.01
-- takes off 2p (2.02p, rounded down), leaving 99p, then 1% of 99p rounds
-- down to nothing. Rounding to whole pence makes the order matter. The
-- code isn't wrong here: the belief was. A counterexample says the program
-- and the statement disagree, not which one is wrong; deciding that is up
-- to you. Here the shop has to choose an order and write it down. Delete
-- `percentOrder`.
--
-- **Pence coupons do add up.** Two pence coupons are one coupon for both
-- amounts. `omega` proves it: once `apply` computes, it's subtraction.

theorem penceOffTwice ∀ (first: Nat) (second: Nat) (total: Nat): (PenceOff second).apply ((PenceOff first).apply total) = (PenceOff (first + second)).apply total := omega

-- **Two facts at once: `∧`.** `p ∧ q` ("and") says both. A pence coupon
-- never adds to the total, and never takes off more than it says:

theorem penceOffFair ∀ (pence: Nat) (total: Nat): (PenceOff pence).apply total ≤ total ∧ total ≤ (PenceOff pence).apply total + pence := omega

-- `omega` proves both halves together. A proof of `p ∧ q` is also a pair,
-- `Both p q`: replace `omega` with `Both ? ?`, and the two `?`s have the
-- goals `total - pence ≤ total` and `total ≤ total - pence + pence`. Prove
-- each with `omega`, then put the single `omega` back.
--
-- **Some coupon will do: `∃`.** The shop promises to match any lower
-- price. `∃ (coupon: Coupon) => …` ("there exists") says some coupon
-- brings the total down to the target. To prove it, you name one: a proof
-- of `∃ (x: T) => P` is `Witness x p`, the value `x` and a proof `p` that
-- it works.

theorem priceMatch ∀ (total: Nat) (target: Nat) (cheaper: target ≤ total): ∃ (coupon: Coupon) => coupon.apply total = target :=
  Witness (PenceOff (total - target)) omega

-- Replace the `omega` with `?`: the goal is
-- `total - (total - target) = target`, the statement with the witness
-- put in for `coupon`, and `omega` proves it from the hypothesis
-- `cheaper`. Put `omega` back, and delete `(cheaper: target ≤ total)`
-- from the statement: `omega` turns red, and the model in its notes is
-- `total = 0` and `target = 1`. A target above the total can't be matched
-- by taking money off. Put the hypothesis back.
--
-- The counterexample search can't try every coupon for each input, so it
-- leaves `∃` statements to proof: `stitchwort check --counterexamples
-- --verbose` gives `priceMatch` the line
-- `- priceMatch  not applicable: nothing decides the conclusion: …`, and
-- a failing proof of one gets no "this statement is false" note.

-- ## Step 8. Mistakes on purpose
--
-- **Break 1: a spec that's wrong the same way.** In `Item.cost`, change
-- `*` to `+`. Every theorem still checks: the till and the spec both use
-- `Item.cost`, so they agree, both wrong. Run the tests: "the till adds
-- up each line" fails. A proof that the program meets its spec is only as
-- good as the spec, so keep the spec plain, test it on a few inputs you
-- worked out by hand, and be careful about what it borrows from the
-- program. Put `*` back.
--
-- **Break 2: a till that skips the last item.** In `scan`, add an arm
-- above the second, `| [item] => running`. `scanAdds` turns red, at its
-- second arm, and the last note of the error is a counterexample: a
-- running total of 0 and one item at 1p, which the till now charges
-- nothing for. `checkoutCorrect` stays clear: its own proof is still
-- right, given what `scanAdds` says, so the error is shown where the
-- false statement is. (`check` fails, so nothing is trusted until it's
-- fixed.) Remove the arm.
--
-- **Break 3: the wrong witness.** In `priceMatch`, change the witness to
-- `PenceOff target`. `omega` is red: it can't prove
-- `total - target = target`. Its model, `total = 1` and `target = 0`,
-- says it "may not be a real counterexample", and as Step 7 said, the
-- search that would confirm it doesn't run on an `∃`. Check it by hand:
-- taking 0p off 1p leaves 1p, not 0p, so it is real. Put the witness
-- back.

-- ## Step 9. Wrapping up
--
-- You have seen:
--
-- - a spec says what the program should do, in the plainest words, apart
--   from how the program does it; a theorem says the program meets it;
-- - write a statement with `?` first: the hover, and
--   `stitchwort check --counterexamples`, find inputs that make it false,
--   and finding none is evidence, not proof;
-- - a counterexample says the program and the statement disagree, and you
--   decide which is wrong;
-- - a loop with a running total is proved by saying what it does from any
--   running total;
-- - `∀` for every value, `∧` for both, `∃` for some value, proved by
--   naming a `Witness`;
-- - a proof is only as good as its spec.
--
-- More: docs/guide/10-proofs.md (the guide's chapter on proofs, including
-- "A specification and its program") and docs/syntax.md (the reference,
-- "Counterexamples to a theorem").
