# Review: SW-3055, the native shortcut for `Nat.divFuel` on a number with an unknown

**Reviewed:** branch `lane/SW-3055` at `39b6c55f7` against `main` (`git diff main...lane/SW-3055`).
**By:** Fable, 13 Nov 2026. **Checked with:** the lane's release CLI and, for comparison, the main
checkout's (`12fd6ab1e`, which doesn't have the rule); three named tests. No suites were run.

## Verdict

**Merge after fixes.** The rule is sound: it computes exactly what the definition's steps compute,
up to conversion, on every case tried (1,260 generated cases and the edge cases below). Two things
must be fixed before merging: an existing test now fails, and `docs/core.md` isn't updated. One
claim in the brief is wrong and needs the orchestrator's eye: **hashes can change** (shown below).

## What the change does

`divFuel (kf + f) (k + m) d`, for a number `d ≥ 1`, becomes
`q + divFuel ((kf − q) + f) ((k − q·d) + m) d` with `q = min(kf, k / d)`, in one step, when `q ≥ 1`.
The machine does it with a new `Outcome::Succs`, `Control::UnfoldAfterSuccs` and `Frame::AddNat`;
the reference evaluator does it by recursion.

## 1. Soundness

**The rule is the definition's steps.** One step of the definition is
`divFuel (Succ f) n d = divStep (leq d n) f n d`. With `d` a number ≥ 1 and `n = k + m`, `k ≥ d`:

- `leq d (k + m)` takes off `d` shared `Succ`s and reaches `leq 0 …`, which is `True` without
  looking at the rest (`Nat.leq`'s first clause);
- `divStep True f n (Succ d')` is `Succ (divFuel f (n − d) d)`;
- `(k + m) − d` takes off `d` shared `Succ`s and reaches `((k − d) + m) − 0`, which is
  `(k − d) + m` by `Nat.sub`'s first clause, also when `k = d` and what's left is a bare unknown
  (`m − 0 = m` is `rfl`, checked).

So each step holds for every `f` and `m`, including when they are the same unknown or unsolved
metavariables, and `q` of them give the rule. It stops exactly where the definition does: when the
fuel's known part is used up (`kf = q`: then `divFuel f …` is stuck on `f`, or is `0` for a closed
fuel) or when fewer than `d` known `Succ`s are left on the numerator (the next `leq` is stuck).
After one `Succs` the rule can't fire again on the rest, so there is at most one `AddNat` frame per
call and one level of recursion in the reference.

**Checked by running** (`rfl` theorems, lane binary; the same file without the 2^128 cases also
checks on main's binary, which has no rule, so the right-hand sides are the definition's own
results):

| Case | Statement proved by `rfl` |
|---|---|
| one step, all unknown | `divFuel (Succ f) n d = divStep (leq d n) f n d` |
| the real `/` shape, fuel and numerator the same unknown | `(v + 5) / 2 = 2 + divStep (leq 2 (v + 1)) (v + 2) (v + 1) 2` |
| numerator divides exactly | `divFuel (f + 4) (m + 4) 2 = 2 + divStep (leq 2 m) (f + 1) m 2` |
| fuel runs out, closed | `divFuel 2 (m + 10) 2 = 2` |
| fuel runs out, open | `divFuel (f + 2) (m + 10) 2 = 2 + divFuel f (m + 6) 2` |
| `d = 0` (rule doesn't apply) | `divFuel (f + 2) (m + 10) 0 = 0` |
| `d = 1` | `divFuel (f + 7) (m + 3) 1 = 3 + divStep (leq 1 m) (f + 3) m 1` |
| closed numerator, open fuel | `divFuel (f + 3) 10 2 = 3 + divFuel f 4 2`; `divFuel (f + 9) 10 3 = 3` |
| `k < d` (`q = 0`) | `divFuel (f + 9) (m + 2) 3 = divStep (leq 1 m) (f + 8) (m + 2) 3` |
| `Succ` constructors, not `+` | `divFuel (Succ (Succ (Succ f))) (Succ⁵ m) 2 = 2 + divFuel (Succ f) (Succ m) 2` |
| open divisor (rule doesn't apply) | `divFuel (f + 3) (m + 9) (d + 2) = divStep (leq d (m + 7)) (f + 2) (m + 9) (d + 2)` |
| 2^128 | `(v + 2^128) / 2 = 2^127 + divStep (leq 2 v) (v + (2^127 − 1)) v 2`, and `% 2` |

Four deliberately wrong variants (fuel off by one, count off by one, rest off by one, wrong closed
answer) are all refused on both binaries. A generated grid, `divFuel (F + kf) (M + k) d` against
the rule's formula for `kf` 0–6, `k` 0–8, `d` 0–4 and bases (f, m), (f, closed), (closed, m),
(v, v), 1,260 theorems, checks on both binaries: on main that shows the formula is what the
definition computes, on the lane that the code implements the formula.

**Conversion.** It can't equate more than before: the result is convertible with the definition's
in every case, and numbers are compared by their `k + base` views, which treat `q + x` and `q`
`Succ` constructors around `x` alike. I found nothing it fails to equate that it equated before.

**The value's shape does change**, though, which the lane didn't notice. The definition's steps
build `q` `Succ` constructors around the stuck rest (`Value::Ctor`); the rule builds the compact
`q + rest` (`Value::NatAdd`). Same number, convertible, but a different value, shown differently
and read back as a different term when `q ≥ 2`. That is the cause of the two findings below
(B1, S1).

## 2. Agreement between evaluators

- **Machine and reference** both handle `Succs`, with the same arithmetic
  (`view_with` then `from_view`); `value.rs:1382`, `value.rs:1812`, `value.rs:2573`,
  `reference.rs:446`. Every `match` on `Outcome`, `Control` and `Frame` is exhaustive, so nothing
  else was missed, and `Frame` still fits its 64-byte assertion (it compiled).
- **Other evaluators** (`crates/rt`, the JS backend, `crates/native`) run `DivFuel` only on closed
  numbers through their own code; they never call `native::run`, so `Succs` can't reach them. The
  kernel and the elaborator share the machine.
- **Tests.** No test compares the two evaluators, or natives on against off, on this rule:
  `shortcuts_with_unknowns_agree_with_the_definitions`
  (`crates/driver/tests/elaboration/natives.rs:335`) lists `Add`, `Sub`, `Leq`, `EqNat`, `Mul`,
  not `DivFuel`. The only coverage is the new example, when the differential sweep's sample
  happens to include it. See S2.

## 3. Hashes

The brief expected none to change. **They can.** A read-back of a quotient with two or more known
steps and a stuck rest used to be `Succ (Succ (… rest))` and is now `Nat.add q rest`
(`native::nat_add_term`; for `q = 1` it is `Succ rest` either way). Where such a read-back is kept
in an elaborated term, the declaration's hash moves. Measured, main's binary against the lane's:

```
theorem d (x: Nat) (p: Nat → Prop)
    (h: p (Succ (Succ (Succ (Nat.divStep (Nat.leq 3 x) (x + 5) x 3))))): p ((x + 9) / 3) :=
  match big: Nat.leq 3 x with
    | True => h
    | False => h
```

`H.d` is `dbcb8003…` on main and `f4d79ee7…` on the lane, and `H.d.%match1` moves too. The
controls with one known step (`(x + 5) / 3`) and none (`(x + 2) / 3`) have the same hashes on
both, so the difference is this rule and not other merges. Holes solved by unification didn't
move in my probes (unification already builds the compact form on main).

This isn't a soundness problem and, by D2303, not a reason against the change. It does mean:
the verifier must expect hash-snapshot changes in any example with such a read-back and restage
them, rather than treat them as a surprise; and `core.md` can't say "read-back and hashes are as
without it", as it does for `Nat.mul`. `Nat.add`'s own shortcut already behaves this way
(`(3 + x) + y` natively is `3 + (x + y)`, compact), so the precedent exists. The library's pins
still hold (`pinned_hashes::every_binding_by_hash_applies_to_the_library` passes on the lane).

## Findings

### Blockers

**B1. An existing test fails.** `division::a_stuck_step_of_division_is_shown_as_division`
(`crates/driver/tests/elaboration/division.rs:103`) expects
`Succ (Nat.divStep (1 <= x) (x + 3) (x + 2) 3)` for `(x + 5) / 3` and now gets
`Nat.divStep (1 <= x) (x + 3) (x + 2) 3 + 1`. Run on the lane: 1 failed. This is the shape change
above reaching messages and goals: `(x + 9) / 3` used to print as
`Succ (Succ (Succ (Nat.divStep (3 <= x) (x + 5) x 3)))` and prints as
`Nat.divStep (3 <= x) (x + 5) x 3 + 3`. The new form is consistent with how every other
arithmetic result prints (`x + k`) and is the only one possible for 2^127 steps, so I'd accept it
and update the test and its comment (lines 101–102). It is a user-visible change to goal text,
so the orchestrator should record the call.

**B2. `docs/core.md` isn't updated** (D3210: a kernel reduction change updates the spec in the
same lane). Draft below.

### Should fix

**S1. Say that hashes can move, and check.** As section 3. The lane's report and the brief both
assume evaluation-only; the commit should say otherwise, and the verifier should run the hash
snapshots expecting possible changes.

**S2. Add targeted tests** in `crates/driver/tests/elaboration/natives.rs`, beside the others:
- `DivFuel` in the natives-on against natives-off comparison (`conv` of the two results), over a
  grid of `kf`, `k`, `d` (0 and 1 included), with the fuel and numerator bases both open, one
  closed, and the same variable, as `k + x` and as `Succ` constructors;
- the same grid through `reference::eval` against the machine, normal forms equal
  (`nat_add_rule.rs` has the pattern), since the reference's `Succs` arm has no direct test;
- one case at 2^128 that asserts it finishes in few steps.

**S3. Charge for the big-number arithmetic** (`native.rs:963`–`975`). `&k / &divisor` and
`&q * &divisor` on numbers past a machine word aren't charged to the budget; the closed path
(`run`, `native.rs:1072`) and `Mul`'s shortcut (`native.rs:936`) both call
`budget.number_words` first. `(x + 2^(2^24)) / 3` is a long division the step limit doesn't see.
Add `g.machine.budget.number_words(|| number_words(Native::DivFuel, &[kf.clone(), k.clone(), divisor.clone()]))?`
before dividing.

**S4. The rule looks further than its comment says** (`native.rs:955`–`962`). The comment says
"the fuel's head is looked at first", as `Mul` does, but `view(fuel)` walks and forces the whole
fuel before `d` or `n` is looked at. With a divisor that isn't a number, or `k < d`, the case
tree would never have forced the fuel beyond its first `Succ`. This is not unsound (forcing a
total term changes no value) but it can spend budget the definition wouldn't. In `n / d` the fuel
is `n` itself, which `leq` forces anyway, so it only matters for direct `divFuel` calls. Reorder:
check the fuel's head is a `Succ` (as `Mul` does), then `as_nat(d)`, then `view(n)` and return
`None` if `k < d`, and only then view the fuel. Use `view_keeping` for the fuel, as `Mul` does,
so a glued call in the fuel's base stays the call the case tree would have bound.

### Notes

**N1. `AddNat` forces the rest** (`value.rs:1812`). With gluing on, the rest's `divStep` call
comes back as a glued call and `view_with` forces it at once, a nested machine run one level
deep. It is bounded (the rest is stuck after at most one step), and other natives already force
inside `unfold_now`, so this is fine; the doc comment on `Outcome::Succs` explains why.

**N2. Process.** The commit is co-authored by Sonnet; D2506 sends kernel evaluation changes to
Opus. The code is careful and small, but the two blockers are the kind of thing D2506 is for.

**N3. The fuzz repros.** `docs/reviews/repros/fuzz-elab-25c3-22779.sw` (added by the lane) and
`fuzz-elab-25b1-3237.sw` each have one declaration that doesn't parse (they are the fuzzer's
mutants, kept as found); the check reports that one error and finishes in 0.25 s at 110 MB on the
lane (measured). I did not rerun them on main to see the 2 GB again.

## 4. Paragraph for `docs/core.md`

In "Numbers with unknowns" (line 373), after the `Nat.mul` sentences and before "Unlike R3 and R4
below":

> `Nat.divFuel` takes several steps at once when its divisor is a number `d ≥ 1`, its fuel is
> `kf + f` with `kf > 0`, and its numerator is `k + m` with `k ≥ d` (`f` and `m` anything, numbers
> included, as long as the three aren't all numbers, which is the plain native):
> `divFuel (kf + f) (k + m) d` is `q + divFuel ((kf − q) + f) ((k − q·d) + m) d` for
> `q = min(kf, k / d)`. Each of those `q` steps of the definition has a comparison that computes
> to `True` whatever `m` is (`Nat.leq d (k' + m)` with `k' ≥ d`) and a subtraction that takes `d`
> off the known part, so the rule is the definition's own steps, and it stops where they do: when
> the known fuel is used up, or fewer than `d` known `Succ`s are left and the next comparison is
> stuck. The rest is then evaluated as any call is. The result is kept as the compact `q + rest`,
> where the definition's steps build `q` `Succ` constructors around the rest: the same number,
> equal in every comparison, but read back as the term `q + rest` rather than `Succ (Succ … rest)`
> when `q ≥ 2` (and printed `rest + q`), so a declaration that keeps such a read-back has a
> different hash from the one it would have without the rule. One step at a time,
> `(x + 2^128) / 2` took 2^127 steps (SW-3055). With a divisor of 0 or one that isn't a number, or
> a fuel with no known `Succ`, it does nothing and the case tree runs. Like `Nat.mul`'s, it's a
> native's shortcut, so it's off with the natives, and it is bound to `Nat.divFuel` by that
> definition's pin, which covers `Nat.divStep`, `Nat.leq` and `Nat.sub`.

And in "Native implementations" (line 375), "Otherwise they unfold as usual" should read
"Otherwise they unfold as usual, apart from the shortcuts above".

## 5. The 25bb case

**Agreed: a different cause.** `docs/reviews/repros/fuzz-elab-25bb-20155.sw` has no division. It
is `innerN`, a `decreasing` function, applied to 2^128 under `Succ`, the same definition and
shape as SW-2639's case. On the lane's binary it still ends with `E-RESOURCE` ("recursed more
deeply than allowed") after 4.2 s at a peak of 3.32 GB (measured), which matches SW-2639's
measured 3.31 GB for `innerN 2^128` to the second figure. That is the proof chain each level of a
`decreasing` function holds, which D3474's fresh-check encoding addresses; nothing in this lane
touches it.

## Tests run

- `division::an_open_dividend_has_a_small_normal_form`: pass.
- `division::a_stuck_step_of_division_is_shown_as_division`: **fail** (B1).
- `pinned_hashes::every_binding_by_hash_applies_to_the_library`: pass.
- CLI checks of the repro files described above, on the lane's and main's release binaries.

Not run: the hash-stability snapshots, the differential sweep, the examples suite (the
verifier's).
