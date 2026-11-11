# SW-2805 review: open goals as kernel assumptions, stage 2

Paper review (no builds, no tests) of commit `3ddb8e306` (merged as
`b4b2e0161`), per D2364. Design: `docs/proposals/using-unfinished-proofs.md`
(stage 2); F2 from `docs/reviews/SW-2804-assumptions-review.md`; owner names
from `docs/reviews/SW-2822-assumptions-followups-review.md`. Line numbers
are at `b4b2e0161`.

## Verdicts

| # | Question | Verdict |
|---|----------|---------|
| 1 | F2: nothing that relies on an open goal counts as finished | **MUST-FIX** (M1: `check --counterexamples`); SHOULD-FIX (S1: reliance is tracked by bookkeeping windows, not read off the terms) |
| 2 | The assumption's type is the goal correctly closed over its context | OK, with NOTEs |
| 3 | Retry reuse, label collisions, fallbacks | OK (collisions only fall back or share an identical constant); NOTEs on owner names |
| 4 | "Can't be checked until the goal is filled" | SHOULD-FIX (S2: too broad; hides real errors). Nothing becomes finished, so no MUST-FIX |
| 5 | Other | SHOULD-FIX (S3: no memo in the reliance walk); NOTEs |

The kernel side is sound by construction: every term with an assumption
goes through the kernel, and a wrong assumption type can at worst make an
owner fail to check or make a user check against a stronger premise.
Neither can make anything *finished*, provided F2 holds. So F2 is where the
risk is, and it is where the findings are.

## 1. F2

### What holds

The commit marks reliers unfinished through the elaborator's table, so
every gate that reads `Elaborator::is_unfinished` (`crates/elab/src/lib.rs:805`)
sees them:

- `check`'s goal count and exit status: goals stay `Severity::Goal`
  diagnostics; the relying items get `Status::Unfinished`
  (`crates/elab/src/module.rs:452-459`).
- `audit` asks `relies_on_goal` on every `Final` theorem itself
  (`crates/driver/src/audit.rs:206`): term-based, so it doesn't depend on
  the bookkeeping. Good.
- `test`: `run_selected` (`crates/driver/src/test_run.rs:431-436`) and now
  `lower_tests` (`:360`) skip unfinished tests. A test def is created
  inside its component's window, so `mark_relying` marks it.
- `run` (`crates/driver/src/run.rs:184`), `build`/`extract` exports
  (`crates/driver/src/driver.rs:927`; `build` also refuses while any goal is
  open, `crates/cli/src/main.rs:4029`, `:4072`), the web playground (`load`
  fails with goals, `crates/web/src/lib.rs:694-707`), `axioms`
  (`crates/cli/src/main.rs:2453`), `eval`/REPL (direct mentions,
  `crates/elab/src/lib.rs:1041`, `:1123`, `:1163`; `?` typed in is never
  assumed because `decl.owner` is cleared before `lift`, so `assume_goals`
  returns at `assume.rs:97-99`).
- Check cache, this run and later ones: `mark_relying` inserts into
  `unfinished_defs`, so `unfinished_count()` grows and the namespace isn't
  written (`crates/elab/src/cache/mod.rs:689-705`); and a namespace with a
  goal also has a `Goal` diagnostic. Across runs, a namespace's key chains
  its dependencies' keys (`cache/mod.rs:613-628`), so adding a `?` to `A`
  changes the key of every namespace using `A`; a stale "finished" entry
  can't be replayed over a newly assumed dependency.
- Other namespaces and projects: `relied_on` walks terms across
  namespaces, and the floor only skips definitions below it.
- The LSP and JSON outputs: neither reads `State` directly (the index JSON
  has no status; `audit --json` uses `audit::Status`).
- The floor (`assume.rs:50-55`, `:255-266`): checked before each new
  assumption is made, so a rewind that removed the first assumption always
  gives a fresh floor. I couldn't construct a stale floor that skips a
  relier.

### M1 (MUST-FIX): `check --counterexamples` calls a relying theorem "checked"

`crates/driver/src/counterexample.rs:206-213` passes `state == State::Final`
as `checked`. Before stage 2, a wholly-`?` theorem (or one using a `?`
lemma) was abandoned to `Failed` (`crates/core/src/check.rs:3554-3560`), so
`checked = false`. Now it is `Final`, so `checked = true`, and
`crates/cli/src/main.rs:1649-1661` prints `!` and "this theorem checked, so
an axiom it uses, the compiler or the search is wrong; please report it"
for a false statement left as `?`. That is the case the proposal names: a
false goal (a misstated exercise) assumed. `check --counterexamples` runs
whatever the goal count (`main.rs:1588-1597`).

Fix: `checked = state == Final && !self.elab.is_unfinished(id)` (or
`relies_on_goal`, as `audit` does). A test: a wholly-`?` false theorem under
`check --counterexamples` reports `✗` with no "this theorem checked" line.

### S1 (SHOULD-FIX): reliance is marked by component windows, not read off the terms

`mark_relying` (`assume.rs:273-302`) marks the defs of the component's items
and the defs/datas created from `defs_before` until it runs
(`module.rs:452`). Final defs that rely on an assumption but fall outside
that are never marked, and every gate except `audit` then takes them as
finished:

1. **After the window.** `derive_pending_ord` (`module.rs:517-524`) runs
   after `mark_relying` and before the next component takes its
   `defs_before` (`module.rs:410-411`), so an `Ord` instance derived there
   for a data type that relies on an assumption (a field type mentioning a
   relying definition) is never marked.
2. **Failed components.** `relying` is computed only when `!failed`. A
   failed component whose errors were all turned into `E-UNFINISHED`
   (`blame_failed_dependency`, see S2) goes through `mark_unfinished`
   (`module.rs:776-800`), which marks only non-`Final` defs. A `Final`
   relying def in that window (a lifted `%match` helper admitted before
   the owner failed, a member defined before a later step failed) stays
   unmarked.
3. **Data types in `eval`.** The `eval`/REPL gate checks `Term::Def` only.
   A relying data type is marked in `unfinished_datas`, but nothing reads
   it there; before stage 2 the kernel refused the non-final type instead.

None of these is user-named in the common cases I found (the instance and
`%match` helpers are internal; a failed item's name doesn't resolve to the
def), so I haven't made this a MUST-FIX. It is the shape the SW-2804 review
warned about, though: correctness depends on every way of making a final
definition going through a window. The robust form is to make
`Elaborator::is_unfinished` read reliance off the terms (as `audit` already
does), memoised per def (S3), with the table only as a cache. Then `axioms`,
`run`, `test`, `build` and `eval` are structural, like `audit`. At least,
call `mark_relying` for failed components too, and move it after
`derive_pending_ord`.

The floor's assumption (everything below `min(module.first_def, first
assumption)` was final when the first assumption was made, `assume.rs:255`)
holds for the paths I found: needs load before the module's own
declarations (`module.rs:379`), and `ensure_equations` only makes
equations for library definitions (`equations.rs:5959`). It would be
sturdier as "the first def that isn't `Final` or `Failed` when the first
assumption is made", which needs no reasoning about module boundaries.

## 2. The assumption's type

`goal_type` (`assume.rs:146-230`) is right as far as I can check:

- Only the variables the hole's meta is applied to (`goals.rs:388-399`, the
  same `own` test that builds the hole term) are candidates, so the
  solution `λ x₁…xₖ. a x_order` (`assume.rs:122-130`) has exactly the
  meta's arity, and the `Var(k-1-i)` indexing matches binder order.
- The `Π` telescope is ordered by dependency, and `under` (`:199-214`)
  turns each placed level into the right index. A type that mentions a
  level not yet placed, or not applied at all, gives `Err` → `None` →
  fallback, never a wrong binding.
- All reader variables are kept (with their hypotheses); a `%`-variable is
  kept only if the goal or a kept type mentions it, transitively
  (`:171-183`). Dropping an unused `%rec` only makes the assumed
  statement stronger, which is sound for an assumption and is the statement
  the reader sees.
- Unknowns: `zonk_keeping(..., &|_| false)` fails on any unsolved meta, so
  an unknown anywhere gives `None`. A goal mentioning a non-final
  declaration is refused by the kernel's `admissible`
  (`check.rs:2437-2439`) before anything is added.

The kernel checks the owner against the assumption's type, so a mis-built
type can't make it accept something false; it could only make an owner
fail (a spurious error) if the type weren't convertible with the expected
type at the hole. It is the quoted `target` the hole was checked against,
so that would need an elaborator/kernel conversion mismatch, which would
show up elsewhere too.

NOTES:

- N1. An unknown in the type of a `%`-variable the goal doesn't need still
  makes the goal fall back: `types` zonks every applied variable
  (`:156-159`), and `needs` calls `levels_in(...)?` for each (`:163-166`).
  Only the kept ones need to be zonkable.
- N2. A hole whose goal mentions a hole later in source order (`⟨?, ?⟩`
  with the second earlier, say) falls back: the holes are assumed in source
  order, once. A second pass over the ones left would catch it.
- N3. Goals are printed after `assume_goals` (`flush_goals` from
  `clear_metas`), so a goal whose context mentions an earlier hole now shows
  that hole's assumption (`Ns.t.?1 n`) where it showed `?` before.

## 3. Retry reuse and fallbacks

A label is `(unit.path(decl.owner[0]), n)` with `n` the hole's rank among the
attempt's pending goals by span (`assume.rs:96-117`). Pending goals are
dropped at every `clear_metas` (`flush_goals`, `goals.rs:696-698`) and on
undone sub-attempts (`goals.rs:658-660`), so a retry numbers its own holes
from 1 and never reads a stale meta.

On a label already held (`assumption_for`, `:236-251`): reused if the closed
types are convertible, otherwise `None` and the goal falls back. Either
way no `E-MALFORMED` reaches the user, and one label is still one constant,
so the hashing argument from SW-2804 holds. Two distinct holes that collide
with convertible types share one constant: sound (they assume the same
closed proposition), only reported under one owner. Collisions I checked:

- Retries with local definitions admitted (`with_local_retries`,
  `lib.rs:2552-2570`): the intended reuse.
- LSP rechecks: a rewind truncates the kernel, freeing the labels
  (SW-2822 F3). A REPL redefinition with a changed goal falls back, as
  `docs/core.md` says.
- Duplicate test names, field defaults (`defaults.rs:267`) and partial
  definitions (`partial.rs:493`): fall back or share, never unsound.

NOTES (for stage 3's reporting, which names the goal by its label):

- N4. `decreasing` definitions are labelled under the step's key
  (`decreasing.rs:1433`, `with_local_retries(&step_key, ...)`), so the owner
  is `f.%step`-like, not the reader's `f`.
- N5. A test's key already includes its root (`lib.rs:1401-1405`), and
  `assume_goals` passes it through `unit.path` again (`assume.rs:100`);
  check that this doesn't double the namespace.
- N6. Orphaned assumptions from a failed first attempt stay in the kernel.
  Harmless (they only lower the floor and the namespace already has a
  goal), but stage 3 should list goals from the module's goals, not by
  scanning assumptions.

## 4. "Can't be checked until the goal is filled"

`waits_on_goal` (`lib.rs:383-392`) makes any message that shows a call of
an unfinished non-theorem definition count as "mentions a failed one"
(`pretty.rs:3253`). `blame_failed_dependency` (`module.rs:802-848`) then
turns every error of the component (except unknown names) into
`E-UNFINISHED`, which isn't reported, whenever the component depends on a
same-module item that is `Failed` or `Unfinished`, and a relying item is
now `Unfinished`.

**S2 (SHOULD-FIX).** That is broader than "stuck on the goal". If `double`
relies on a `?` only in a proof argument and computes normally, then
`theorem t: double 2 = 5 := rfl`, or a type mismatch whose message shows
`double 2`, has its real error silently made "unfinished". Under
`check: open-goals: warn`, `check` exits 0 with that error never shown.

It doesn't let anything *pass* in the F2 sense: `t` is marked unfinished
(`module.rs:469`), `audit` fails it, and before stage 2 `t` wasn't checked
at all. So this is a lost benefit of stage 2 (the guide now promises "a
mistake in them shows now", `docs/guide/10-proofs.md:114`), not a
soundness hole. Narrowing it: count a mention only when the shown term,
evaluated, is stuck on an assumption (its normal form has a `Term::Def`
whose `assumption()` is set), not when it merely calls a relying
definition.

NOTE N7. The rule fires only for dependencies in the same module (the
`failed` list comes from module items). The same `rfl` on `half 1`, with
`half` in another namespace, is reported as a real error, and fails `check`
even under `warn`. That is safe, but inconsistent.

## 5. Other

**S3 (SHOULD-FIX, performance).** `relied_on` has no memo. With one early
`?` (in `Aoc.Common` or `sf/Basics`), every later component's
`mark_relying` walks its whole dependency cone above the floor, and data
types are never skipped (the skip is `Decl::Def` only, `assume.rs:77`).
`audit` does the same walk per theorem (`audit.rs:206`). And
`mark_relying` scans all of `module.def_items` per component
(`assume.rs:280-283`), which is quadratic in a module once any assumption
exists. Memoise "relies on nothing" and "relies on {…}" per `Decl`
(invalidated by a rewind, or keyed by a kernel generation). That is also
what S1's structural `is_unfinished` needs. I haven't measured this; a
`sf/` timing before and after would settle it.

NOTES:

- N8. Over-marking: `mark_relying` marks every def of the window if *any*
  relies (`:284-300`). So a non-relying component in whose window a waiting
  instance that relies is checked becomes `Unfinished`: its tests are
  skipped ("uses a declaration") and it isn't cached. That is safe, but
  mislabelled; marking per def fixes it.
- N9. `derive_ord.rs:112` requires the `DecEq` instance to be
  `Status::Checked`, so a relying `DecEq` now gives the reason "didn't
  check" for the missing `Ord`, where "isn't finished" would be right.
- N10. `docs/syntax.md:1649` ("a mistake in the main theorem is reported
  now") and the guide's wording depend on S2.

## Must-fixes

- **M1**: `crates/driver/src/counterexample.rs:211-213`: a relying theorem is
  `checked`, so `check --counterexamples` prints "this theorem checked ...
  please report it" for a false `?` statement. One-line fix, plus a test.
