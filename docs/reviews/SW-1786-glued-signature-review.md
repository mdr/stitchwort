# SW-1786: review of SW-1779 (glued signature check, folded mentions, glued head)

Independent Opus review of `lane/SW-1779`, commit f322bb73d, required by
D2364 because it changes the kernel. Write-up under review:
`docs/reviews/SW-1779-exponential-forcing.md`.

## Verdict

**Merge.** All three fixes are sound and answer-preserving, apart from
fix 1's intended narrowing (fewer ignorable arguments), which is on the
conservative side and is the direction `bounded-readback.md` §2.2 already
names as safe. The regression test is meaningful: it fails with each of the
three fixes reverted on its own. Two stale comments should be updated; they
can go in the merge or a follow-up, and don't block it.

## Fix 2: `declare_def` checks the signature glued

### What could change

Gluing changes only what evaluation returns for a definition applied to
all its arguments: a `Value::Call` instead of running its case tree
(`unfold_now`, `value.rs`). Everything else that decides how a call
evaluates (opacity via `hidden`, `folds` for theorems and dictionaries,
natives, `erases_result`, `folds_mul`) is tested before the gluing branch
and doesn't read `glue`. So inside `check_type` the only difference is that
some values are calls where they were unfoldings. The places a signature
check can observe that:

| Where | Glued effect | Changes the result? |
|---|---|---|
| `conv` (every `check` against an expected type) | calls compared by arguments first, then by unfolding (`CallMemo`, D483) | No: the rule the kernel already trusts for every body; it only answers "equal" where unfolding would |
| `force` before a shape test (`check_type`'s `Sort`, `infer_j`'s `Eq`, `Pi` heads) | the call is forced; its unfolding never has a call at the top | No |
| `Term::Eq(None, …)`: inferred type read back with `quote` into the checked term | `quote` (`Readback::Unfolded`) forces every call, so it writes the normal form | No: the same normal form as from the unglued value; this is the only read-back into a checked term, so hashes don't move |
| `sort_of`'s fallback: `quote_kept` then `check_type` | the call is read back as `f a…` and its type inferred | No: only the sort is kept; `f a…` is well typed wherever the value was |
| `check_case`, `substitute`, `Unchanged` | glued paths | Not reached: `case_only_in_tree(ty, false)` refuses `case` in a type |
| Budget | fewer steps in the doubling cases; in principle more where `conv` compares two calls' large, different arguments before unfolding | Only in the rejecting direction (D2543: limits fail), and the same trade the kernel already makes for bodies |
| Diagnostics (`cx.show`) | glued values print folded | Messages only, and better |

So the set of signatures accepted changes only by budget, and the checked
term (`ty`, which `push_def` stores and the hash covers) is the same term.
The prelude and example hash snapshots confirm that empirically (below).

### Does a glued value escape?

No. The glued values are made in `cx` from `ty`'s subterms and from
other definitions' `ty_value`s, which are unglued and contain no calls (a
closure applied under gluing builds fresh values; it doesn't write into
the closure). A call's `Unfolding` cell is written only on the `Call`
value that owns it, and every call made here is fresh (`Rc::default()`)
and dropped with `cx`. Nothing persistent holds a call: `push_def`
re-evaluates the checked term after `glue` is restored, so
`Def::ty_value` is unglued as before; the check cache and hashes take
terms, not values. The E-NOT-A-PROP path's `cx.eval(&ty)` also runs after
`glue` is put back. The transparency set is empty throughout, so a cached
unfolding can't carry an opaque body anywhere.

### Consistency with D483 and `admit_group`

The same save, set, restore pattern around one call, inside
`in_kernel_modes`, as `admit_group` uses for bodies. Kernel errors are
values, so the restore always runs (as there). D2294 still holds: the
kernel sets the mode itself and never inherits the caller's.

Comparisons that assume unglued values: I looked for any routine that
pattern-matches a value without forcing it first. `Unchanged::look`
handles `Call` and checks `glue`, but isn't reached from a type. `quote`'s
`Unfolded` visit forces first (and has `unreachable!` for a call after
the force). Nothing else in the signature path matches on shape without
`force` or `force_ref`.

### Counterexample?

I found none, and I don't think there is one. Every observation of a call
is either a force (which gives the unfolding, the very value unglued
evaluation would have made at that point, up to nested calls) or `conv`
(D483's rule), and the one read-back into the checked term unfolds fully.
Pending definitions in a group have no body, so they are neutral in both
modes. The only behavioural difference left is step counts.

### Follow-ups (not blocking)

- **Stale comments.** `crates/core/src/check.rs:1584` ("Outside a body
  (types, `declare_def`) there are no calls, and these read back as
  `quote`") and the doc of `Machine::glue` (`crates/core/src/machine.rs:26`,
  "turns it on only to check a definition's body") are no longer true.
  `admit_group`'s comment at `check.rs:1776` says `Def::ty_value` is "made
  unglued by `declare_def`"; it is `push_def` now, and still true.
- **`retype_def`** (`check.rs:1924`) checks a type the same way as
  `declare_def` but still unglued. Not a soundness question; a signature
  that is fast to declare could still be slow to retype. Data parameter,
  index and field types (`check.rs:2259`, `:2282`, `:2565`) are unglued
  too. Worth a small ticket if a case turns up; I wouldn't change them on
  this branch.

## Fix 1: `ignorable_arguments` reads back folded

- **Direction.** A call's unfolding is its definition's closed body
  applied to its arguments, so every variable the unfolding mentions is in
  the arguments (`force_solved` replaces solved metavariables, and an
  unsolved one's spine is read the same way in both forms). The folded
  form's mentions are a superset; more mentioned means fewer ignorable.
  `ignorable` only lets `solve` (`unify.rs`) accept a non-variable argument
  in an `auto` proof's spine, and the kernel checks every solution, so
  fewer is never unsound; at worst a contrived program loses SW-323's
  permission and its `auto` argument goes to search, or fails.
- One case goes the other way relative to *before*, not relative to the
  truth: where the unfolded read-back ran out of budget, the function
  returned `None` (nothing ignorable); the folded one now succeeds and
  gives a conservative answer. That is still never more than the unfolded
  form would allow.
- **Fit with bounded-readback.md.** §2.2 lists this site and says the
  as-written form is "safe only where 'mentions' is the conservative
  answer (`check.rs:3889`: fewer ignorable arguments)". So this is the
  site where D2541's "search what you see" applies without a check, and no
  limit switches an answer (D2543). Stage 4's shared `mentions` reader
  would answer exactly instead (opening only calls that could drop a
  variable); this fix is a sound step on the way and doesn't conflict
  with it.
- **Real code.** I spot-checked with the hash snapshots (below), which
  cover std and the example sample; they would move if any `auto`
  solution in them changed. I didn't rerun aoc (a whole-aoc run needs
  Matt's OK); the lane's node-count comparison over 11,491 declarations is
  the right measure, and I have no reason to doubt it.

## Fix 3: `interfaces::locals` looks at the head glued first

`force` never returns a call at the top, in either mode. For every head
shape (`Data`, `Pi`, `Sort`, `Eq`, constructors, numbers, and `Neutral`
on a variable, an unsolved metavariable, a hidden or folded definition, or
a quotient), the decision of what the head is doesn't read `glue`, as
listed under fix 2; gluing only leaves calls nested below it. So the
glued head is an interface exactly when the unglued one is, and the same
locals are skipped. A resource error can only become rarer (fewer steps).

One side effect, which the lane notes: the glued force caches the
unfolding in the call's shared cell, and the unglued force that follows
for an interface-typed local reads that cache (`force_now`), so the
candidate's `arg` can now hold nested calls where it was fully unglued
before. That happens only for a local whose type is itself a call of a
definition that unfolds to an interface (an alias), and only if the cell
wasn't filled already. `arg` is read back with `quote` (unfolded, the same
term) and compared by `conv`, which handles calls in either mode. No
change in output. The double force could be avoided by keeping the glued
result, but that would hand search glued arguments as a rule, which
D2535 avoids; the lane's choice is right.

## The regression test

`a_doubling_hypothesis_is_never_unfolded_in_full`
(`crates/driver/tests/resources.rs`): `P40` under a 5 M-step work limit,
with a hypothesis of it in a signature and an `auto` argument decided by
search in its scope. Each fix covers one of the three places, so the
test is meaningful only if each is needed. I reverted each fix on its own
and ran it:

| Reverted | Result |
|---|---|
| none | PASS, 0.22 s |
| fix 2 (`core/src/check.rs`) | FAIL, E-RESOURCE while checking `f` |
| fix 1 (`elab/src/check.rs`) | FAIL, E-RESOURCE while checking `f` |
| fix 3 (`elab/src/interfaces.rs`) | FAIL, E-RESOURCE while checking `f` |

So it fails with any one fix missing, and the reverts were restored
(`git status` clean).

## What I ran

- `task test:one -- a_doubling_hypothesis_is_never_unfolded_in_full`:
  pass.
- The same test with each fix reverted in turn (`cargo nextest run
  --release -p stitchwort-driver --test resources a_doubling`): three
  failures, as above.
- `cargo nextest run --release -p stitchwort-driver --test hash_stability
  prelude examples` (default sample): 3 passed (prelude 13 s, examples
  17 s), so std's declaration and definition hashes, which cover every
  checked signature, are unchanged.

Not run: aoc or rogue checks, the merge or daily tiers.
