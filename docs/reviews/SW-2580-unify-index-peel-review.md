# SW-2580 review: `peel_succs` in index unification, capped note readback

Opus review (D2364) of `lane/SW-2580`, commit `26a99cc82`, 10 Nov 2026.

## Verdict

**Approve.** `peel_succs` is sound, and as far as I can find it gives the
same outcome as the one-`Succ`-per-step loop on every input: the same
solutions in the same order, the same conflict constraint and the same
stuck constraint and reason. Only the budget use is lower. No bugs found.
There are two low-severity notes on (2) and one nit on the docs.

## Why the equivalence holds

Soundness doesn't depend on the equivalence. Every peel is injectivity on
`Succ`, which is valid at `Nat : Type`, and the final pair goes through the
normal rules. Even if the outcomes differed, nothing unsound could come out.
The equivalence matters for determinism and completeness. It holds because
of these facts:

- **Where it runs.** Only after deletion (conv false), solution (neither
  side flexible), the type-former, `Eq`, non-data and `Prop` checks, and
  only at the builtin `Nat`. So at the top it replaces exactly the
  injectivity step the old code would take.
- **Skipped points.** The old loop checks the rules at points the new one
  skips, and none of them can fire there:
  (a) inside one batch (`Nat`/`NatAdd` with counts reduced by `j <
  shared`; a `Ctor` side caps `shared` at 1, so it has no such points), and
  (b) between batches, after a force, while both sides still start with
  `Succ`.
  At these points:
  - Solution needs a flexible variable, and a `Succ`-headed value isn't one.
  - The type former, `Eq`, `Prop` and `TypesDiffer` checks can't fire: the
    type is `Nat`, and `Succ`'s one field has `k = 0`.
  - Deletion would need `conv(u, v)` true where `conv(Succ u, Succ v)` was
    false. `conv` compares numbers by their `k + x` views
    (`native::compare[_lazily]`, value.rs ~3546), and `view(Succ u) = 1 +
    view(u)`. So that's congruent, and its contrapositive carries the
    top-level "false" down every skipped point.
  - The folded and `reread_sum` checks run before the number case only on
    the values themselves. A `Nat`, `NatAdd` or `Ctor Succ` value is neither.
- **Forcing.** `force` is the identity on `Nat`, `NatAdd` and `Ctor`
  (`needs_forcing` is true only for `Call` and solved metas), so the old
  loop's forces at the (a) points did nothing. At the end of a batch the
  new code forces exactly the value the old loop forced next: the field of
  a `Ctor`, or the base of `NatAdd(k, base)` once `k` is used up
  (`from_view(0, Some(base)) = base`, as `split_value(NatAdd(1, base))`
  gives). It forces nothing the old loop didn't, and in the same order.
- **Final pair.** It's identical to the old loop's.
  `nat_value(n - shared)` equals `shared` steps of `split`, and
  `from_view(k - shared, base)` equals `shared` steps of `split_value`. The
  pushed entry is the one the old loop pushed last: `ctors[1].fields`, with
  an empty base, which is `Nat`'s empty parameter list. The `shared`
  intermediate entries the old loop left all had `solved == 1`. They were
  only popped, and substitution into them had no effect.
- **Constraint order.** Unchanged. The peel stays inside one binder's chain,
  and the outer entries are untouched.

Edge cases checked:

- **Zero.** `Nat(0)`, `Ctor Zero` and `NatAdd` with base `Zero` count as 0,
  so nothing is peeled and `constructor()` gives the conflict as before.
- **`NatAdd(0, x)`.** It never comes from `from_view` or `ctor`. If it
  existed, the count is 0 so nothing is peeled, and the old path is taken.
- **Mixed forms.** `k + x` against `Succ (Succ y)` peels 1, then 1 again,
  giving `NatAdd(k-2, x)` against `y`. Numerals against `k + x` with
  different `k`: `min` peels the smaller count, and the result is `x`
  (forced) against a number, or two `NatAdd`s with one count left.
- **Unsolved metas or variables under the `Succ`s.** These are leaf bases.
  The peel stops at them, and the final pair is handled by solution or
  stuck exactly as before.
- **Bignums.** The subtraction can't underflow, since `shared = min` of the
  two counts, and `BigUint` has no overflow. `fields[0]` is reached only
  when the count is greater than 0, which needs `Ctor(nat, 1, [_])`.
- **Termination.** There is one budget step per batch, and each batch
  removes at least one `Succ`. A lazily built `Succ` chain made of `Call`s
  still costs one step per layer, as before. So it's no faster than before,
  but no slower either.

## Findings

1. **Low (docs nit): docs/core.md, "no other rule can apply in between".**
   The statement is true, but the reason the claim rests on goes unstated:
   deletion in between would need conversion to tell `u` and `v` equal
   where it told `Succ u` and `Succ v` apart, and conversion compares
   numbers by their `k + x` forms. Half a sentence saying so would let a
   later change to `conv` on numbers see what depends on it. Otherwise
   accurate: what the kernel accepts is unchanged, apart from cases that
   used to run out of budget.

2. **Low: `with_opaque_notes` can drop the "is opaque" note.** When a side
   reads back past 200k nodes, `quote_for_note` returns `None`, and that
   side's opaque definitions are no longer scanned. If an opaque
   definition inside the big side is why `rfl` failed, its note is lost.
   It's the same kind of loss as the other capped notes, and acceptable for
   a side that big. A possible follow-up is to scan the folded readback
   (`quote_shown`) when the normal one is capped. It would need care,
   since folded keeps every call, not just the opaque ones. Not blocking.

3. **Info: none of the new caps degrades to "gives `…`".** Each
   `quote_for_note` call site (opaque, unused-equation, hidden/proof
   differences, `Eq.cong`, match-equation, alike-updates, branch notes)
   and `first_difference_note` *omits* its note when it is capped. None
   prints `…`. The `…` in the new snapshot
   `refl-note-huge-parser-unfolding.snap` (Note 1, "computing both sides
   gives `…` and …") comes from `show_unfolded`, which has been capped
   since SW-2569. That is SW-2598's case. That snapshot will change when
   SW-2598 lands, and should: the example exists for the memory blow-up,
   not that text. In this example `first_difference_note` is now silent,
   which is also what makes the message thin. SW-2598 may want the
   difference note to work from the capped (partial) readback rather than
   nothing.

4. **Info: uncapped readbacks remain.** `quote_shown` (folded) is still
   uncapped in `differ_only_in_hidden`, `differ_only_in_proofs` and
   `with_alike_updates_note`, and so is `quote(&lhs)` for the hypothesis
   needle in `with_unused_equation_notes`. Folded readback is small for the
   cases seen, so I don't know of any input that blows them up. Worth
   adding them if the fuzzer finds one.

## Tests

`task test:one -- huge_numbers_lose_their_shared_succs_at_once`: passed
(0.05 s, run by this review). The test covers numeral against numeral
(conflict), numeral against `Succ (Succ x)` and `Succ x` against a numeral
(solutions `2^128 - 2` and `2^128 - 1`), and `k + x` against a numeral
(conflict). Not covered, but argued above: `NatAdd` against `NatAdd`, and a
`Ctor Succ` field that forces to a compact number.
