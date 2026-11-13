# SW-3174 (conversion and `check_app` take less stack per nesting level): kernel review

Reviewed: commit `959a00539` on `lane/SW-3174`, by reading
`git diff main...HEAD -- crates/core crates/driver/tests` against the old
code, plus `crates/web/build.rs`. Paper review: nothing was built or run.
Line numbers are the lane's worktree at `8b87c7fdc`.

## Verdict: SOUND

The kernel says "equal" for the same pairs of values, and accepts and
rejects the same terms with the same error codes, messages, visit counts
and step counts, with one class of exception, all in the "no answer"
direction:

- **Intended:** terms and comparisons that ran out of native stack
  (`E-RESOURCE`) now go further. Nested stuck calls compare about 1.75
  times deeper under the same guard, and applications nested in argument
  position check at any depth. No type error becomes an acceptance, and no
  "different" becomes "equal".

No fix is needed for soundness. Findings, most important first:

| # | Severity | Finding |
|---|---|---|
| 1 | Low to medium (playground robustness, not soundness) | The 320 KiB WebAssembly guard counts linear-memory stack, and is safe only while V8's own call stack lasts longer. That ratio was measured for the printer, the evaluator and the parser, never for conversion, and this lane changes it for conversion (a boxed memo and out-of-line helpers take linear-memory bytes away without taking calls away). Not measured in the browser. See below. |
| 2 | Low | Three walks outside the kernel recurse once per nested application argument with no guard (`rt/src/hoist.rs:85`, `js/src/lib.rs:3519`, `elab/src/closing.rs:1118` and `:1140`). The kernel's own recursion used to bound what they were handed; now only the termination walk does for bodies, and nothing does for types. Section 3. |
| 3 | Low | Test gaps: no test rejects through the new `Waiting` path, and none takes the "expected type needed forcing" branch there. |
| 4 | Low | `nested_stuck_calls_compare_under_the_playground_guard` pins a native frame size (180 levels in 320 KiB); it will fail on a toolchain or profile change that grows frames, for no kernel reason. |
| 5 | Note | `Waiting` holds about 150 bytes of heap per nesting level, uncounted by any budget; linear in the term, so acceptable. |
| 6 | Note | `docs/core.md` needs one sentence (section 4). |

### Finding 1 in full: the playground's guard and conversion

`crates/web/build.rs:8`-`:36` explains that in WebAssembly the guard
measures the stack in linear memory, where only values whose address is
taken live, while each call also uses the engine's own stack, which
overflows as a `RangeError` the compiler can't recover from. 320 KiB was
chosen from where V8 overflowed with the guard lifted: 500-550 KiB in the
printer, 620-680 in the evaluator, 790-1050 in the parser and elaborator.
Each figure belongs to one recursion, because it depends on how many
linear-memory bytes that recursion uses per engine frame.

Conversion's figure was never measured. This lane lowers its
linear-memory bytes per level (2.3 to 1.3 KiB natively), so 320 KiB is
now about 245 levels of nested stuck calls where it was 140. What a level
costs the engine may have gone down too (`conv_step`'s large frame is no
longer live during the recursion) or not (`TreeMemo` moved to the heap,
which removes linear-memory bytes only; a level now passes through
`recurse` and `stuck_same` or `same_spines`, each a call). If the engine
runs out before 245 levels, a comparison that used to end in `E-RESOURCE`
restarts the playground's worker instead. That is a crash in the
playground, not a wrong answer anywhere, and the lane's own note says
"not yet measured in the browser". It should be measured (ticket 1)
before the guard is relied on for this recursion; the same goes for the
frames SW-3132 and SW-3133 changed.

## 1. Soundness

### Conversion (`value.rs`)

`conv_with` (`value.rs:3632`) still pops one task, charges one
`budget.step()`, and returns `false` on the first pair that differs. What
changed is that `conv_step` (`value.rs:3868`) returns `Step::Recurse(kind)`
at the six places where it used to call `same_spines` or
`same_stuck_trees` itself, `recurse` (`value.rs:4147`) makes that call, and
if the pair is still unsettled `conv_step` is called again with a `Stage`.

I checked each of the six against the old code:

| Kind | Old code, in `conv_step` | New | Same? |
|---|---|---|---|
| `Calls` (two glued calls of one definition, memo has no entry) | `same_spines` true: return `true`. False: `memo.record(Arguments)`, fall through to the folded rule | `recurse`: true is `Answer(true)`; false records `Arguments` (`value.rs:4165`) and resumes at `Stage::Folded` | Yes. The `Calls` block is guarded by `from == Stage::Calls` (`value.rs:3880`), so on resuming it is skipped, memo and all; the memo is read once and written once, with the same key and value. `Differ::Values` still returns `false` at once; `Differ::Arguments` still falls through without a recursion |
| `Folded` (two folded calls of one definition) | `is_folded(a) ‖ is_folded(b)`, same `Def` heads, `same_spines` true: return `true`. Otherwise `unfold_folded` both | `recurse`: true is `Answer(true)`, false resumes at `Stage::Unfold`; a folded pair that isn't two calls of one definition sets `from = Unfold` in place (`value.rs:3897`-`3905`) | Yes. `unfold_folded` runs exactly when the old code ran it: only if `is_folded` held for a side. `is_folded` is evaluated once per pair, as before (the first call returns before reaching it when it stops at `Calls`; a resume at `Unfold` skips it) |
| `Sealed` | value of the match arm: `same_spines` | `Answer(same_spines)` | Yes |
| `StuckSame` | `same_stuck_trees` with the argument comparison | `stuck_same` (`value.rs:4211`), the old closure moved verbatim | Yes. `def_head(h1)` became `Some(f)` from `def_spines`; `opens_by_tree` only holds for `Head::Def`, so they are the same value |
| `Underapplied` | `same = def_head(h1).map(same_spines).unwrap_or(false); same ‖ push_eta` | head is a definition: `recurse` does `same_spines ‖ push_eta`; otherwise `push_eta` directly in `conv_step` | Yes |
| `StuckDifferent` | `same_stuck_trees` with `|_| Ok(false)` | `stuck_different` (`value.rs:4256`) | Yes |

The questions in the brief:

- **A resumed stage skipping a check.** The stages only move forward
  (`Calls`, then `Folded`, then `Unfold`), and each resume enters
  `conv_step` at exactly the statement after the one the old code would
  have fallen through from. Nothing below the folded rule is guarded by
  `from`, so every later rule (sum re-reading, numbers, compact text, the
  structural match) runs on a resumed pair as it did. After `Unfold` no
  `Recurse` that resumes can be returned, so the inner loop ends.
- **A memo entry for an unsettled pair.** The only `CallMemo` write that
  moved is `Differ::Arguments`, still written only after `same_spines`
  returned `Ok(false)`; an error returns before it. `same_spines`' own
  write of `Differ::Values` is untouched. `TreeMemo` is boxed, and
  `enter`, `known`, the argument comparison, the tree comparison and
  `record` run in the old order (`value.rs:4566`); a pair equal by its
  arguments is still not recorded, and an error still drops the memo
  without recording.
- **A `Recurse` result misread.** Every `Resume::Answer` is the value the
  old expression had; `Sealed`, `StuckSame` and `StuckDifferent` can only
  answer, as before. `def_spines` (`value.rs:4196`) is only reached with
  two `Neutral(Head::Def)` values: `Folded` matches them by pattern,
  `Sealed` and `Underapplied` have `h1 == h2` and `def_head(h1)` is
  `Some`, `StuckSame` has `opens_by_tree` on both.
- **An early return turned into a fall-through.** Every old
  `return Ok(x)` is `return Ok(Step::Answer(x))`. The neutral arm now
  returns from every branch rather than yielding the match's value, which
  is the same thing since nothing followed the match.
- **`take()` leaving `Value::Refl` behind** (`value.rs:3830`). Each
  `take` is in an expression that pushes and then returns
  `Step::Answer` in the same statement or the next; no path takes a value
  and then goes on to compare it or returns `Recurse`. I checked the six
  sites (unfold, the two sum re-reads, the two compact-text arms, the
  call arm). `a2.unwrap_or(take(a))` takes `a` even when `a2` is `Some`,
  which is harmless for the same reason. So `recurse` never sees a
  placeholder, and a placeholder `Refl` is never compared with a real
  `Refl`.

`same_stuck_trees` keeps its signature and behaviour for the elaborator's
unifier (`crates/elab/src/unify.rs:1881`, `:1939`); `tree(a)` and `tree(b)`
are still built only after the arguments failed.

### `check_app` (`check.rs:545`)

The loop does, per spine, what `check` + old `check_app` + `infer_spine`
did, and a nested application argument is entered by pushing a `Waiting`
and left by popping it.

- **Expected type forced or compared at a different point.** For a nested
  argument: `nesting` (`check`'s), `force_type(dom)`, `nesting`
  (`check_app`'s), then `start_spine` (the spine's further `nesting`s and
  `infer(head)`), all before the outer spine goes on
  (`check.rs:565`-`571`). That is the old order. `force_ref` returns
  `Borrowed` only for the very value it was given (`value.rs:866`), so
  `forced: None` means "compare against the original", which the loop
  finds again as `outer.dom` or `expected` (`check.rs:587`). The
  comparison and the mismatch error get the forced type when there is
  one, as before, in the same argument order (`found_as_expected`,
  `check.rs:648`).
- **An argument checked against the wrong domain after resuming.** `dom`
  and `cod` are computed by `function_type` from the outer spine's `f_ty`
  before the push and stored in the `Waiting`; the inner spine never sees
  the outer `f_ty` (moved into `function_type`), and on the pop the outer
  `f_ty` becomes `result_type(cod, checked)` with the *checked* inner
  term, as the old `check(cx, a, &dom)` then `result_type(cx, &cod, &a)`
  did. The next outer argument's domain therefore comes from the codomain
  applied to the checked inner argument.
- **`Waiting` resumed in the wrong order.** `waiting` is a stack, pushed
  only when entering an argument and popped only when the spine in hand
  has no applications left (`apps.len() == base`). `apps` is one stack
  shared by all spines; an inner spine's applications lie above
  `inner_base`, and it pops exactly down to it, so on resuming the outer
  spine `apps[outer_base..]` is what it had left. `apps.pop()` yields the
  application nearest the head first, the order `infer_spine` iterates
  (`args.iter().rev()`).
- **An error path leaving `Waiting` non-empty and continuing.** Every
  fallible call in the loop is followed by `?`, which leaves the function;
  the only `Ok` exit is the `return Ok(checked)` when `waiting` is empty
  (`check.rs:595`). There is no `catch`-like handling in the loop.
- **Implicitness.** `icit` is read from the `App` node and used both for
  `function_type` and for the rebuilt application, for the nested case
  through `Waiting.icit`.

`infer_spine` (`check.rs:277`) is the old loop with the arguments read
from the `App` nodes rather than copied; `push_apps` counts the same
visits (none for the first application).

## 2. Same behaviour

- **Rule order in conversion:** unchanged, by the table above.
- **Steps:** one `budget.step()` per task popped, in `conv_with`; a
  resume doesn't charge again, and the old code didn't charge between
  the rules either. `codomains` is the old arm moved out.
- **Memo reads and writes:** `CallMemo::get` once per pair of glued
  calls, `record(Arguments)` at the same moment; `TreeMemo` unchanged.
- **Visits:** `nesting` is called the same number of times in the same
  order relative to forcing, inference and comparison, so `total_visits`
  is unchanged and an exhausted budget fails at the same call with the
  same pass name.
- **Order of errors:** within a spine, head first, then arguments first
  to last, each argument's own errors before its comparison with its
  domain, then the outer spine's next argument. Unchanged.
- **Checked term and hashes:** the rebuilt term is `app_icit(f, checked,
  icit)` at every level, as before.
- **Drop order** of values differs in places (a compared pair now lives
  until the end of the loop iteration); dropping has no budget or
  semantic effect.
- **What does differ:** where native stack runs out. That is the purpose.

## 3. The depth limit

### Is it acceptable for the kernel?

Yes. The kernel never had a depth limit of its own: `Budget::nesting`
(`budget.rs:743`) counts a visit and compares the native stack pointer
with a floor, and nothing else. How deep a term could nest was a property
of the build (frame sizes, the stack given), about 250 levels under the
playground's guard and far more natively, not of the language.
`docs/core.md` defines `E-RESOURCE` as "no answer, rather than a wrong
one", so removing one way of running out changes no answer. The loop still
counts a visit per application, so the work limit and cancellation still
stop it, and it uses heap in proportion to the term it was handed
(finding 5).

Two things do change for a very deep term, and are worth knowing:

- **A definition's body is still bounded, by the termination checker.**
  `admit_group` runs `termination::check_group` on every checked body
  (`check.rs:2595`), and its walker recurses once per application argument
  under its own guard (`termination.rs:386`, `:411`-`:424`). So a body
  nested past what that walk can follow is still refused with
  `E-RESOURCE`, now naming the termination checker ("the termination check
  is inconclusive, so `g` isn't accepted", `termination.rs:1025`) where it
  named the type checker. The driver test shows exactly this at 1,000,000
  levels. Between the old limit and the walker's, bodies that were refused
  are now admitted.
- **A type is not bounded by anything.** `declare_def`, data declarations
  and the other `check_type` callers have no recursive walk over
  application arguments after the check, so an application nested to any
  depth inside a declared type is admitted (the type is then evaluated by
  the machine, which is a loop).

Source text can't get there: the parser stops somewhere below 100,000
levels (`nesting.rs`, the parsing tests) and
the elaborator's own guard comes first (`web/stress.html`'s "an expression
nested 5,000 deep" still expects a resource error, from the elaborator).
Only terms the elaborator builds in a loop, or a caller of the kernel's
API, can be deeper than the elaborator could recurse.

### Later passes over checked terms

The search was for functions that recurse on the Rust stack once per
level of an application's argument, over a checked term, with neither
`Budget::nesting`, a work list nor a depth cap. (Part of it was done by a
search agent; I read the three unguarded walks below and the kernel-side
entries myself.) Two facts frame the list: `Budget::step` compares the
stack pointer with the floor just as `nesting` does (`budget.rs:704`), so
anything that takes a step per level is guarded; and both guards work only
inside an operation (the floor is 0 outside one).

**Unguarded, and they follow application arguments:**

| Where | What it does | Reached on | Shape that recurses |
|---|---|---|---|
| `crates/rt/src/hoist.rs:85` `runtime_closed`, with `runtime_closed_app` at `:70` | Whether a call reads no variable at run time | A run body, from `SigMaps::closed_map` (`hoist.rs:44`), called by `rt/src/lower.rs:894` and `js/src/lib.rs:4403` before lowering goes down into the arguments, so `Lowerer::expr`'s guard hasn't seen them yet | Every non-erased argument of a call of a definition, and constructor fields; only when the outer call returns a `SigMap` |
| `crates/js/src/lib.rs:3519` `self_call_under_add` | Whether a term is a self-call under `Succ`s and `Nat.add`s | The tail leaves of a self-recursive definition in JavaScript generation (`tail_add`, `lib.rs:3457`) | Both arguments of `Nat.add`, and `Succ`'s field: `a + (b + (c + …))` |
| `crates/elab/src/closing.rs:1118` `defs_named` and `:1140` `named` (through `inner_defs`, `:1081`) | Count the definitions a lemma's conclusion names, for the "what closes this `?`" search | A candidate theorem's checked **type** | Explicit application arguments, both sides of an equation, constructor and data arguments |

The first two walk bodies, which the termination walk still bounds, so
they are exposed only if their frames are larger than that walk's by more
than the room the guard leaves below its floor. The third walks types,
which nothing bounds now: a theorem whose statement holds an argument
nested deeply enough is admitted and then overflows the stack when the
search considers it. None can be reached from source text today (the
elaborator's guard comes first); each needs a term built in a loop.

**Unguarded, but not exposed by this change:**

- `core/src/termination.rs:641` `Walker::rebuilt`, `core/src/check.rs:4197`
  and `:4235` (`not_positive`, `not_positive_nested`) and `:4362`
  (`stored_only`): they recurse only through constructor or data
  arguments, each level of which `check` still takes a guarded frame for.
- `core/src/reference.rs` (`eval` at `:185`, `expand_term`, `quote`,
  `conv_in`): recursive with no stack guard, but the reference evaluator
  is only in test and dev builds, and only evaluates what a test hands it.
  `validate_inert`, which does run on every admitted group in those
  builds, uses a work list (`reference.rs:1270`, `:1382`).
- `Term`'s derived `Debug` (`term.rs:160`): tests and two debugging paths
  only. `Term` has no derived `PartialEq`, `Hash` or serialisation, its
  `Clone` is shallow, and its `Drop` is a work list (`term.rs:235`).
- The runtime's passes over its own lowered code (`rt/src/opt.rs:401`
  `size`, `rt/src/code.rs:819`, the `codec` writer, `ir::Expr`'s derived
  `Clone`, `Debug` and `Drop`): bounded by how deep `Lowerer::expr`'s
  guard (`rt/src/lower.rs:757`) let lowering go, as before.

**Guarded or iterative (what else was looked at):**

- Kernel, around the check: `admissible` (`check.rs:3931`) and
  `Term::mentions` use `Term::subterms`, a work list (`term.rs:705`,
  `:717`); `case_only_in_tree` (`check.rs:4101`) is a work list;
  `termination::Walker::walk` has `nesting` (`termination.rs:386`);
  `inert::offences` is a work list (`inert.rs:186`); `has_lift_leaf`,
  `count_lams`, `peel_lams` are loops; hashing is a work list
  (`hash.rs:680`) with `nesting` per declaration, and the pins go through
  it; `determined.rs` walks are loops.
- Terms and values: `map_vars_with`, so `shift` and `instantiate`, and
  `rewrite_up` have `nesting` (`term.rs:555`, `:637`); `eval` is the
  machine (`value.rs:825`); `quote_as` is a work list with a step per
  value (`value.rs:3190`); `conv_with`'s recursion takes a step per task;
  `stuck_on_variable` (`value.rs:4436`) recurses per stuck call but
  through `force`, which takes steps.
- Printer: `nesting("printer")`, or `…` where it can't reach (the driver
  test covers both).
- Elaborator after the kernel call: `saturate` and `check_tailrec` have
  `nesting`; `refl_tree` for opaque definitions has `nesting`; the check
  cache writes with a work list and reads a flat table
  (`elab/src/cache/codec.rs:272`, `:528`, `:618`).
- Driver: declaration hashes and axiom tracking go through `hash` and
  `subterms`; `live/term_diff` checks `stack_exhausted`.
- Runtime and JavaScript: `Lowerer::expr` (`rt/src/lower.rs:757`),
  `specialise::simp` (`:401`, `:611`) and the JavaScript generator
  (`js/src/lib.rs:3004`, `:3354`, `:4164`) have `nesting`; `sums`, `trmc`
  and `reuse` skip bodies past `MAX_NESTING`; `clauses`, `fusion` and
  `elab/src/shown.rs` have depth caps; `erasure::reachable` uses
  `subterms`.

Not looked at: the `lsp` and `web` crates, and the elaborator's passes
that run before the kernel is called (they never see a term the kernel
has accepted that the elaborator couldn't itself build).

## 4. `docs/core.md`

The lane doesn't touch `docs/core.md`, and D3210 asks for it when what the
kernel accepts changes. Nothing in the spec is now false: it promises only
that running out is `E-RESOURCE`. Two additions would record what this
lane and SW-3133 established, so that later work doesn't undo it:

1. In the "Evaluation budget" row of the table at the top (`core.md:16`),
   or beside the `E-RESOURCE` row (`core.md:670`): that the kernel sets no
   depth limit of its own. Long spines and applications nested in argument
   position are checked in a loop; other nesting (lambdas, `let`s,
   constructor fields, case trees, types inside types) and conversion of
   calls nested in arguments recurse on the native stack under a guard, so
   where a deep term runs out depends on the build and is never part of
   what is accepted or equal.
2. The obligation that follows: every pass that walks a term the kernel
   has checked must be a loop or guarded with `Budget::nesting`, since the
   kernel's own recursion no longer bounds what such a pass is handed. For
   bodies, the termination walk is at present the pass that bounds depth.

The "Glued calls" and "Conversion" paragraphs (`core.md:267`, `:269`)
describe rules, not frames, and the rules are unchanged, so they need
nothing.

## Recommended tickets

1. **Measure the conversion recursion in the browser** (finding 1). With
   `STITCHWORT_STACK_PROBE` and the guard lifted, add to `web/stress.html`
   a case that compares deeply nested stuck calls (`not (not (… x))`
   against itself, the lane's kernel test as source) and one of nested
   glued calls, and record where V8 overflows in linear-memory KiB, as
   `crates/web/build.rs` records for the printer, evaluator and parser. If
   it is under about 500 KiB, lower the guard or give `conv_with` a depth
   count. SW-3132 and SW-3133 changed frames the same way and are also
   "not yet measured in the browser".
2. **Tests through `Waiting`** (finding 3), each small, in
   `crates/core/tests/it/kernel.rs`:
   - `f (g x)` with `g x` of the wrong type is `E-TYPE-MISMATCH`, and the
     same two levels down (`f (f (g x))`), so the comparison after a pop
     is covered;
   - `h (g x) y` where `h : (n: Nat) → Args n → Nat`: `y` is accepted at
     `Args (g x)` and refused otherwise, so the domain after resuming is
     the codomain applied to the checked inner argument;
   - an inner application checked against a domain that needs forcing (a
     glued call that unfolds to the type), accepted and refused, so the
     `forced: Some` branch of the `Waiting` path is covered;
   - an implicit nested argument (`f [g x]`), so `Waiting.icit` is.
3. **`docs/core.md`**: the two additions of section 4. Small enough to do
   in this lane before merging.
4. **Guard the three unguarded walks** (finding 2): `runtime_closed`
   (`rt/src/hoist.rs:85`), `self_call_under_add` (`js/src/lib.rs:3519`)
   and `defs_named`/`named` (`elab/src/closing.rs:1118`, `:1140`). The
   last two only count or test, so `Term::subterms` or a depth cap that
   answers "no" does; `runtime_closed` can answer "not closed" past a
   cap. A test for each with a term built directly, as
   `deep_terms_in_later_passes` does. Worth adding to that test as well:
   a deep application inside a declared *type*, which no pass bounds now.
5. **Make the frame-size test less brittle** (finding 4). The 10,000
   deep `check_app` test doesn't depend on frame size and is fine. The
   180-level conversion test passes only while a level takes under about
   1.7 KiB natively in the test profile; say in its doc comment what to do
   when a toolchain or profile change trips it (lower the count, or
   measure again), so nobody reads the failure as a kernel regression.
