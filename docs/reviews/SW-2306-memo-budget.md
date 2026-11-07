# SW-2306: review of SW-2285 and SW-2288 (memo lookups and the budget)

Reviewed: merges `a9be972a0` (SW-2285, `same_stuck_trees` no longer records
pairs equal by their arguments) and `f881683f4` (SW-2288, `TreeMemo::known`
and `ShapeMemo::contains` charge a budget step per layer, `docs/core.md`).
I read the code only. Nothing was built or run.

## Summary

Both changes are sound. Neither can change what the kernel accepts. Every
budget error raised in a lookup reaches the caller through `?`, and the
elaborator treats `E-RESOURCE` as fatal everywhere except inside
`Budget::limited`. That function is the deliberate exception: a search's own
cap runs out and the search reports that this candidate failed. So the new
charges can change what `rewrite` and `match` elaborate to. Here that is
intended (the slow-check example), but `docs/core.md` says the lookup
"never changes an answer", which is too strong.

Two findings are worth a lane. First, SW-2285 re-opened an exponential
shape: nested calls of one definition whose arguments repeat a pair that is
equal by its arguments, such as `f n a a`. That shape was never linear on
the glued-call paths. Second, the likely root cause of SW-2285's slow
lookups is still there: `shape_hash` hashes every glued `Value::Call` the
same, so pairs that differ only inside glued calls all land in one bucket.

Top recommendations:

1. Hash a glued call by its definition and spine in `shape_hash`. Then
   restore recording pairs found equal by their arguments (F2, then F1).
2. Let the kernel's address-keyed `CallMemo` remember "equal by arguments"
   as well as "different", so the glued `f n a a` chain is linear too (F1).
3. Correct `docs/core.md`: the SW-395 sentence no longer covers pairs equal
   by their arguments, and a lookup's charge can change a capped search's
   outcome (F3, F4).
4. Add a unit test that a charged lookup fails with `E-RESOURCE` under a
   small budget, and a test for the `f n a a` chain (F7).
5. Make the uncharged `identical` unable to turn an error into "different"
   by its types, not by `unwrap_or(false)` (F6).

| # | Severity | Confidence | Where | Finding | Size |
|---|---|---|---|---|---|
| F1 | medium | medium | `crates/core/src/value.rs:3809-3816`, `:3233-3246` | Calls nested with a repeated argument pair that is equal by arguments take 2ⁿ comparisons again | M |
| F2 | medium | medium | `crates/core/src/value.rs` `shape_hash` (`Value::Refl \| Value::Call(..) => {}`) | All glued calls hash the same, so buckets collect pairs and each lookup walks them all (now charged) | S–M |
| F3 | low–medium | high | `docs/core.md:239` (`≡`), `crates/core/src/budget.rs:533` `limited` | "Never changes an answer" isn't true where a search cap converts running out into "candidate failed" | S |
| F4 | low | high | `docs/core.md:239` | The SW-395 sentence still says every pair found equal is answered at once | S |
| F5 | low | medium | `crates/core/src/value.rs` `same_closure_layer`, `same_layer` | One step per layer doesn't bound time for closure layers (`free_variables`), long `Chars` or big `Nat` | S |
| F6 | low | high | `crates/core/src/value.rs:4544-4546` | `identical` maps an error to `false`; unreachable today, but it's a "different" fallback in waiting | S |
| F7 | low | high | tests | Neither lane added a test; the charge and the F1 shape are both untested | S–M |
| F8 | low | high | `crates/core/src/reference.rs:900-920` | The reference still records pairs equal by their arguments, so on F1's shape it is linear where the machine isn't | (with F1) |

## Details

**F1. A repeated argument pair that is equal by arguments is compared again
at every level, so the chain costs 2ⁿ.** SW-2285 removed `memo.record(true)`
from the argument path of `same_stuck_trees`. That keeps the chain linear
when the inner pair is *different* (SW-2269's `pred (pred (… a))`, where the
different-record answers the tree's scrutinee). It doesn't when the inner
pair is *equal by its arguments* and appears twice. Take a non-recursive `f
(n: Nat) (x: Nat) (y: Nat)` that matches on `n`, two helpers `p1` and `p2`
written alike (equal by their trees, D1091), and

    a₀ = p1 n            b₀ = p2 n
    aₖ = f n aₖ₋₁ aₖ₋₁    bₖ = f n bₖ₋₁ bₖ₋₁

Comparing `aₙ` with `bₙ` (unglued: the kernel checking a type, or
`STITCHWORT_GLUE=0`) goes through the same-definition arm. The arguments
are `(aₙ₋₁, bₙ₋₁)` twice. Each opens its own `same_stuck_trees`, misses the
memo (nothing was recorded, since it was equal by arguments), and compares
its own arguments twice. `a₀` against `b₀` is recorded, because it was
equal by its trees, so the bottom costs O(1), but the total is 2ⁿ lookups.
At n = 30 that is about 10⁹ lookups, each hashing and walking a bucket:
`E-RESOURCE` at the default budget, or minutes. Between SW-2269 and SW-2285
this was linear.

On the glued paths it was never linear. The kernel's conv shortcut for two
`Value::Call`s (`value.rs:3233`) records only `Differ::Arguments` or
`Differ::Values`. A pair found equal by `same_spines` returns `true` without
a record, so `f n aₖ₋₁ aₖ₋₁` as glued calls repeats the same doubling. The
elaborator's `CallMemo` (a `ShapeMemo`) remembers only "different" too. So
this is a gap that SW-2269 happened to close on one path and SW-2285
re-opened. It isn't a regression against the state before SW-2269.

Where it comes from: a stuck value that uses a `let`-bound or shared stuck
call twice (`max t t`, `t && t`, a pair of the same subterm), nested.
AoC's 287 namespaces don't show it. Nothing there nests duplicated stuck
calls of one definition deeply.

Recommended (M, Opus: kernel conversion): after F2, restore the
equal-by-arguments record in `same_stuck_trees`. The record is safe, since
"equal" is kept as solutions are added, within an epoch. Then add an "equal"
answer to the kernel's address-keyed `CallMemo`. The kernel has no
metavariables, and the key is two unfolding-cell addresses kept alive by
the record, so the lookup is O(1) and needs no charge. For the elaborator's
`ShapeMemo`, an "equal" record would need the epoch in its key, as
`TreeMemo` has. Consider that separately. Test: the chain above at n = 30,
both glued and unglued, finishing in milliseconds.

**F2. `shape_hash` gives every glued call the same hash, so pairs pile up
under one key.** `Value::Call` hashes only its discriminant ("hashes as
just a call, since `identical` takes two with the same unfolding cell as
identical"). But `identical` compares two calls with *different* cells by
definition and spine (`same_layer`, `value.rs:4701`). So `f (g x)` against
`f (h y)`, with `g x` and `h y` glued, files under the same `MemoKey` as
every other `f`-against-`f` pair whose arguments are glued calls. Each
lookup walks all of them. The slow-check example, whose values are mostly
glued `inner`/`settle`/`step` calls, fits that pattern. I think this, not
the number of records as such, is what SW-2285 hit, but I haven't
measured it.

After SW-2288 the walk is charged, so it can't hang. But it is quadratic
in the number of colliding pairs recorded in one outermost comparison. Under
`rewrite`'s 10⁶-step search cap or the 10⁵-step as-written and motive caps,
a candidate that used to fit, slowly, can now run out and be reported as
failed (see F3). A thousand colliding records is enough to use the 10⁶ cap.

Hashing a call by its definition and its spine's parts is consistent with
`identical`. Two copies sharing a cell share their spine too: the cell is
made with the call, and `project_call` (`value.rs:2097`), the one place
that rebuilds a call from another, makes a new cell. And a finer key can
only cost a miss, never a wrong answer. The spine's parts are cached by
address in `ShapeCache`, so the extra hashing is paid once per shared part
per outermost comparison. Recommended (S–M, with F1's lane).

**F3. A lookup's charge can change an elaboration outcome, not only cause
`E-RESOURCE`.** Every caller propagates the lookup's error with `?`:
`same_stuck_trees` from conv (`value.rs:3437`, `3480`) and from the unifier
(`unify.rs:1633`, `1691`), and `known_different` in `run`
(`unify.rs:268`). In the elaborator, `undo::fatal` treats `E-RESOURCE` as
fatal in `transaction` and `attempt`. `recoverable` covers only "too large
to show" with the budget not exhausted, and a work run-out sets
`exhausted`, so it never applies here. But `Budget::limited` clears a
run-out of its own cap and returns `Ok(None)`. Its callers then report that
the candidate failed:

- `rewrite.rs:644` `by_hypothesis`: tries the next hypothesis with
  `remaining = 0`, so all of them fail.
- `rewrite.rs:1777` `holds_by_computing`: answers `false`.
- `rewrite/under.rs:340`: answers `None`.
- `matching/as_written.rs:175`, `:213`, `:482`: `Outcome::Failed`.
- `matching.rs:1153` (motive checks): `Unchecked`, then `fail`.

So under a cap, SW-2288's charges can turn a rewrite that used to apply
into "no match", or a `match` as written into the unconfirmed or failed
path. For the slow-check example that is the intent. The kernel's answers
are unaffected: it runs no `limited` region. This predates the lanes (any
charged step can do it), but `docs/core.md`'s new sentence, "a lookup can
run out of budget (`E-RESOURCE`) but never changes an answer", reads as if
it couldn't happen. Recommended (S): say that the comparison's answer never
changes, but that inside an elaborator search with its own step cap a
lookup's cost counts toward that cap like any other step.

**F4. `docs/core.md`'s SW-395 sentence is out of date.** "Within one such
comparison, a pair of calls already found equal is answered at once
(SW-395)" is still true of pairs found equal by their trees, which is the
SW-395 chain, but not of pairs found equal by their arguments (SW-2285).
The `≡` paragraph doesn't mention SW-2285. Recommended (S): add "(by their
trees; a pair equal by its arguments isn't remembered, SW-2285)", or drop it
if F1 restores the record.

**F5. "A step per layer" doesn't bound the time of every layer.** Three
layers cost more than a step's worth of time:

- `same_layer`'s `Chars` arm compares two slices in full for one step.
- The `Nat` arm compares big numbers word by word for one step.
- `same_closure_layer` calls `free_variables(&a.body)`, which walks the
  whole body term (`subterms`), and it does so even when the two bodies
  are the same `Rc` and only the environments are compared.

So a lookup that walks many recorded closures with one large body costs
O(body) time each and only a step or two of budget. That is the same kind
of gap SW-2288 closed, at a smaller scale. Recommended (S): charge the
closure layer by its free-variable count, or cache `free_variables` per
body `Rc`. Charge `Chars` and `Nat` by length/words, as
`Budget::number_words` already does.

**F6. `identical` turns an error into "different".**
`identical_within(first, g, None).unwrap_or(false)` can't fail today,
because nothing is charged when `charge` is `None`. But it is exactly the
pattern D2543 forbids ("limits fail, never choose"), one edit away: someone
passing a charge through this wrapper would silently get "different".
Recommended (S): make the charge a type parameter (a `FnMut() -> Result<(),
E>`, with `E = Infallible` for the uncharged wrapper), or `expect` with a
reason.

**F7. Neither lane added a test.** The reject example
`as-written-unconfirmed-slow-check.sw` covers SW-2285 and SW-2288 end to
end, by expecting `E-RESOURCE`. Nothing checks these three things:

- a lookup over a bucket of many pairs fails with `E-RESOURCE` under a small
  `limited` cap,
- the same lookup gives the same answer under a large one,
- F1's chain stays linear.

Recommended (S–M): unit tests in `value.rs`'s test module beside
`conv_inside_an_open_unification_remembers_nothing_as_different`.

**F8. The reference and the machine differ in cost on F1's shape.**
`reference.rs` keys its record by the quoted pair and still records every
answer, including equal by arguments, so it is linear on the `f n a a`
chain. The machine is exponential there. Their answers agree, because a
memo only saves work. But a differential or validator run on such a value
would see the machine run out where the reference finishes. Fixing F1
removes the difference. I agree with SW-2288 that the reference needs no
charge for its lookups: `quote` charges the machine budget, and the
`format!` and hash that follow are proportional to it.

## Checked and sound

- **Error propagation.** Every caller of `TreeMemo::known`,
  `ShapeMemo::contains` and `known_different` uses `?`. I found no
  `unwrap_or`, `.ok()` or `Err(_) =>` on these paths. The `Err(_)` arms in
  `unify.rs` (row faults, zonk) are unrelated. A failed lookup drops its
  `TreeMemo`, which decrements `open` and `unifying` (`Drop`), so the
  thread-local memo stays consistent after an error.
- **Re-entrancy.** `known` holds `TREE_MEMO.borrow()` across `budget.step()`,
  and `contains` holds `call_memo.borrow()` across it. `step`'s slow path
  calls only the deadline check and `CANCEL_HOOK`, a plain `fn() -> bool`.
  Neither touches either memo, so no `RefCell` panic.
- **Determinism.** Buckets are `Vec`s walked in insertion order, and maps are
  only indexed, never iterated, so the steps charged are the same on every
  run.
- **SW-2269's linearity for differing chains.** It still holds. In
  `pred (pred (… a))` against `… b`, level k's arguments compare the level
  k−1 pair, which is found different and recorded (`settled`: conv with no
  open unification, or unify with no unknown and eta on). The tree's
  scrutinee is then that pair again, a hit. The different-record alone is
  enough for this shape. The exceptions are as documented: conv inside an
  open unification, and unification under `NO_ETA`, record no "different",
  so both are still 2ⁿ there (SW-2273's test covers the first).
- **SW-2288's `identical_charged`.** It passes `g = None` (no look-through
  of solved metavariables), as the old lookups did. That matches
  `shape_hash`, which doesn't look through them either.
- **`shortcuts_disabled`.** That path is unchanged: nothing is looked up
  or charged.
- **The kernel's own `CallMemo`** (`value.rs:3147`) is keyed by unfolding
  cell addresses, so its lookup is O(1) and rightly uncharged. Its
  addresses are pinned by the values it holds.
- **Glued, unglued and reference.** All three compute the same relation. A
  memo can only skip work, and every hit is a pair `identical` to one
  already answered. Glued and unglued differ only in how many pairs collide
  (F2) and so in steps used. The reference is discussed under F8.
- **Budget scale at the default.** Default work is 10¹⁰ steps
  (`Limits::for_stack`). To run out on lookups alone, a check must walk
  about 10¹⁰ layers, which before SW-2288 would have been tens of seconds
  of uncharged work. So a check that passed in reasonable time can't newly
  fail at the default. The exposure is the elaborator's search caps (F2,
  F3).
- **`docs/core.md`'s last sentence** ("the elaborator's `CallMemo` lookups
  are charged the same way") is accurate. It means the `ShapeMemo`-based
  memo in `unify.rs`, not the kernel's address-keyed `CallMemo` of the same
  name.

## Earlier reviews

- `docs/research/rust-codebase-review.md` (1 Nov) has no findings about the
  tree memo, `identical` or the memo budget.
- `docs/reviews/SW-2272-different-memo.md`:
  - F1 (`settled` relying on arm order) is fixed. The same-definition arm
    now passes `!may_mention_meta(s1) && !may_mention_meta(s2)` itself
    (`unify.rs:1640`).
  - F2 (tests for when "different" mustn't be remembered) is partly
    covered by SW-2273's conv test.
  - F3 (two "remember different" mechanisms, easy to confuse) is still
    open, and there are now three: the kernel's address-keyed `CallMemo`,
    the elaborator's `CallMemo` over `ShapeMemo`, and `TreeMemo`.

## Calls I made

- I rated F1 medium, not high. It is a slowdown (`E-RESOURCE` or minutes),
  never a wrong answer, and the glued paths always had it.
- I treated the `limited` conversion (F3) as existing design, not as a
  defect of these lanes. Only the documentation claim is theirs.

## Tickets to file

- **Lane A (Opus, about 60–90 min): memo keys and the equal record.** F2:
  hash `Value::Call` by definition and spine. F1: restore the
  equal-by-arguments record in `same_stuck_trees`, and add "equal" to the
  kernel's `CallMemo`. F8 follows from F1. Tests for F1's chain, glued and
  unglued. Update `docs/core.md`'s `≡` paragraph (F4). Kernel conversion,
  so Opus.
- **Lane B (Sonnet, about 30–45 min): budget accounting tidy-ups.** F3's
  `docs/core.md` wording. F6: an infallible `identical`. F5: charge
  closure layers by free variables, and `Chars`/`Nat` by size. F7's unit
  tests for a charged lookup under a small and a large cap.

No D questions.
