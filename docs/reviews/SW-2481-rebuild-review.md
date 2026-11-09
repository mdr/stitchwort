# SW-2481 review: `Rebuild` (case refinement keeps sharing)

Reviewer: Opus, independent (paper lane: read and reason only, nothing
built or run). Branch `lane/SW-2481`, commit b3132a27c. 9 Nov 2026.

## Verdict

**Merge after fixes.** I found no soundness bug: as far as I can trace it,
`Rebuild` gives the same value as `eval(ρ, quote(v))` (or `quote_folded`),
node for node, and its `clean` answer is the same as `Unchanged::check`.
Two performance regressions need fixing first. Both come from the same
cause: work that the old path skipped or bounded now runs unbounded. One of
them partly undoes SW-1106 for glued calls.

| # | Finding | Severity | Confidence |
|---|---------|----------|------------|
| F1 | Clean parts that are read back whole (glued calls) are still read back and evaluated when the whole value turns out clean | Medium (perf; the SW-1106 regression) | High (mechanism); magnitude unmeasured |
| F2 | Variable applications aren't memoised by spine address, so shared spines (DAGs) are walked as trees: exponential where `Unchanged` was linear | Medium (hang/OOM) | High (mechanism); medium that real code reaches it |
| F3 | No budget step in the `Rebuild` walk, so it can't be interrupted, and step counts and size-limit errors change | Low | High |
| F4 | `Eq`/`Data` DAGs are walked as trees (same as `Unchanged` before) | Low, already there | High |
| F5 | No test compares `Rebuild` with `eval ∘ quote` directly | Low (test gap) | n/a |

`docs/core.md` needs no change. The kernel accepts the same terms, by the
same rules; only how a refined context is computed has changed.

## Soundness: does `Rebuild` equal readback then eval?

I checked each node that is built directly against `quote_as`/`visit`
(value.rs ~2930–3240) and `eval_step`/`fields`/`Frame::EqParts`
(value.rs ~1500–1870):

- **Forcing.** `quote_as` starts each node with `force_solved` (folded)
  or `force` (unfolded). `needs_forcing` is true only for `Call` and
  solved `Meta` heads, so for `Sort`/`Nat`/`Refl`/`Data`/`Ctor`/`Eq` and
  `Var`-headed neutrals, forcing does nothing. Calls and metas go to
  `read_back`. Correct.
- **Variables.** `Term::Var(level-1-l)` evaluates to `ρ[l]` (with
  `level == ρ.len()`). `Rebuild` returns `ρ[l]`, or `v` itself when it's
  the same level with the same `Apart`. That is the same structure: the
  `same` test compares `known` exactly, not through `Head::eq`, which
  ignores it. `l ≥ ρ.len()` goes to `read_back`, as before.
- **Variable applications.** `quote` gives `App(...App(Var, a1')...)`.
  `eval` gives `apply_step(ρ[l], a_i)`, and with `ρ[l]` a plain variable
  of level `< ρ.len()`, that is never `ERASED` (`usize::MAX - 1`), never a
  `Def` head and never a call. So it is `Neutral(Var(l2,k2), [App(a_i'',
  icit_i)])`, which is what `build` makes, with the same icits. `J`/`Proj`
  spines and `ρ[l]` non-variable (`l == x`) go to `read_back`. When the
  value put in for `x` is itself a variable (determined.rs:254), `x`'s
  applications are built directly with `clean_var(x) == false`, which is
  right.
- **Constructors.** Readback is `Term::ctor` (no smart constructor); eval
  is `fields` → `native::ctor` on each field evaluated alone. `ctor()`
  calls `native::ctor` exactly when it would change something (Zero, Succ
  of `Nat`/`NatAdd`); otherwise it builds `Value::Ctor`. `native::ctor`
  never makes `Chars`, so lists stay lists. `succ_of_call` copies
  `has_call_base` for the unfolded readback (it's only `Succ` that
  matters, since `Nat` has two constructors).
- **`Data`, `Eq`, `Sort`, `Nat`, `Refl`.** All structural on both sides.
- **No binders.** `Rebuild` never goes under a binder: `Pi`/`Lam` go to
  `read_back` whole. So there's no level shifting to get wrong.
- **Erasure.** `start` falls back to a whole `read_back` when erasure is
  active. That covers `fields`' placeholders, `AppErased` and `ERASED`.
- **Metavariables, glued calls, compact lists, `NatAdd`, quotient forms,
  `Def` heads.** All go to `read_back`, exactly as before but per part.
  Each part's readback is evaluated in the same `ρ`, and `fields`/
  `apply`/`EqParts` evaluate parts independently. So the result is the
  same. Sharing the unfolding cache across branches (check_case now
  shares one goal value) is safe: `Kept::fits` checks the meta epoch and
  modes.

**Address-keyed memo.** Every key is the address of a `Values` reached
structurally (constructor fields, data args, `Eq` parts, spine args) from
the `values` slice. That slice stays borrowed for the whole life of the
`Rebuild` (`values.iter().map(...)` in each entry point), and those
structures are immutable `Rc`s, not interior cells, so no key's
allocation can be freed and reused while it's in the map. A memo entry
holds only the fields' rebuild. The node's own `(d, c)` and the number
check are applied per node in `ctor()`, so two constructors sharing one
`Values` are handled correctly. Empty `Values` that might share a static
allocation always memo to "unchanged, clean", which is correct for any of
them.

**`Unchanged`.** A value is accepted only if every node `Unchanged::look`
visits is accepted. `Rebuild` takes the conjunction over the same nodes.
Variables and variable applications use `clean_var`, which is `look`'s own
test. Constructors exclude `Zero`/`Succ`-of-number on the *old* fields, as
`look` does. `Sort`/`Nat`/`Refl` count as clean, and everything else goes
to `Unchanged::check` itself. Running `check` on parts one at a time is
safe: it clears `added` on entry and takes back what it added when it
fails, so `seen` only ever holds sequences found clean. Any occurrence of
`x` forces `clean = false` all the way up (`clean_var(x)` is false,
`check` rejects it, and every `Build` takes the `all`). So I see no way to
get a wrong "unchanged". The kernel uses these functions directly:
check.rs:1183 (via `unify` → `solve` → `substitute`), check.rs:1207–1212
and 1322–1326, and determined.rs. A wrong "unchanged" there would leave
`x` in a refined type and could let an ill-typed branch through. I don't
see a path to one.

**Work list.** `start` uses a work list throughout. `read_back` uses
`quote_as`/`eval`, which are also work lists. Dropping deep `Values` is
iterative (SW-2482). I see no recursion depth problem.

## F1: clean glued calls are read back anyway (medium)

`visit`'s fallback (check.rs:1637) calls `read_back` (check.rs:1760),
which works out `clean` *and then always* runs `quote_folded` + `eval`.
`Rebuild::substitute` throws that result away when the whole value is
clean. The old code ran `Unchanged::check` first and did no readback for a
clean value. `Unchanged`'s own doc (check.rs ~1855) says this is the point
for glued calls: "Keeping it is what saves the work: written out, such a
call is its whole result."

Inputs that should show it (not run):

- A context with `let xs := List.replicate 160000 0` (glued, steps at
  once), then any `match` on another variable. Each refinement now writes
  out and evaluates the 160 000-element list. Before, it kept the call.
- Many hypotheses whose types hold a glued call with a large evaluated
  argument (`h_i : sum bigList = n_i`). Each one's call is now read back
  separately, with no sharing across hypotheses. Before, `Unchanged`
  looked at `bigList`'s fields once, by address.

**Fix (recommended):** in `read_back`, when `self.unchanged` is `Some` and
`check(v)` is true, return `Rebuilt { new: v.clone(), changed: false,
clean: true }` without reading back. The only possible difference from the
old path is when some *ancestor* turns out unclean: the rebuilt value then
keeps a call that steps at once as the call, not its unfolding. That is
exactly the exception `Unchanged`'s doc already argues is fine. `conv`
agrees, and `quote_folded` forces such a call, so terms and hashes are the
same; only `quote_shown` display can differ. If Matt or the author want
the node-for-node property kept strictly, the other way is to mark clean
read-back parts as pending and read them back only in a `Build` whose node
comes out unclean. That's more code, for a display-only difference.

## F2: variable applications aren't memoised (medium)

`Unchanged::push_spine` dedupes spines by address. `Rebuild` memoises only
constructor fields: the var-applied arm (check.rs:1619) visits every
argument every time. A value whose sharing goes through spines is walked
as a tree, and nothing charges the budget (F3).

Suspected failing input (not run). The elaborator puts a `let`'s value in
`env` (elab check.rs:464–471), so the `t_i` share spines:

```
example (f : Nat → Nat → Nat) (x : Nat) (b : Bool) : True :=
  let t1 := f x x
  let t2 := f t1 t1
  -- … each t(k+1) := f tk tk …
  let t40 := f t39 t39
  match b with
  | true => trivial
  | false => trivial
```

Refining on `b` substitutes into `env` (lib.rs:4832 → `substitute_in`).
The old path: `Unchanged` is linear (40 spines) and keeps every entry. The
new path: about 2⁴⁰ visits. Matching on `x` instead is worse. Before,
`quote_folded` hit the size limit and stopped with a resource error. Now
`Rebuild` builds about 2⁴⁰ nodes without a budget check (OOM or hang).

**Fix:** memoise variable applications by spine address too, with the
same "only if shared" test (`Spine` needs an `is_shared`; key by the
`Rc<Elims>` pointer, non-empty spines only). Then the walk is linear in
the size of the stored DAG, like `Unchanged`.

## F3: budget (low)

- `Rebuild` charges no `budget.step()` for the nodes it builds directly,
  so a deadline can't interrupt a long walk. Add `g.machine.budget.step()?`
  per `Visit`. That puts back roughly what `quote_as` charged for the same
  nodes.
- Size limits now apply per read-back part, not per whole value. So some
  values that used to fail with `ResourceError::Size` now succeed, and
  `set_too_large(root_def)` can name an inner call rather than the whole
  value's. Neither is a soundness problem (fewer resource failures, no new
  acceptances under unlimited resources). But step counts, and so any
  verdict near a budget, change. Worth a line in the commit or ticket.

## F4: `Eq` and `Data` DAGs (low, already there)

`Eq` parts (`Shared`) and `Data` args aren't memoised. Neither did
`Unchanged` dedupe them, so a clean `Eq(a, a, a)` nested n deep was
already 3ⁿ in `Unchanged::check`. The new code keeps that cost and adds
building. Optional follow-up: memoise `Shared` by `Rc` address as well.
`Data` args are a `Vec`, so they can't be deduped by address. File as a
backlog ticket rather than block on it.

## F5: no direct equivalence test (low)

The claim "same value, node for node, as `eval(ρ, quote(v))`" carries the
soundness argument, but nothing tests it. A unit test (or a debug-only
check in a test build) that runs `Rebuild` and `eval ∘ quote_folded` over
the context values from a few existing examples, and compares them
structurally (including `Apart` and constructor-vs-`Nat` shape), would
catch a future change to `quote`/`eval` that `Rebuild` doesn't copy. The
code now has two copies of the readback/eval rules for these nodes, and
nothing ties them together. Good candidates: the new
`fin-table-deep.sw`, a `Nat` case (Zero/Succ to numbers), a glued `Succ`
of a call (unfolded), and a number case's `Apart` default arm.

## Elaborator callers

- **`check_case` (families.rs:471).** It used to evaluate `goal_term`
  once per branch, in `cx.env`, which `saved_env` restores to the same
  `env` each time. Now it rereads the goal once and clones it. That's the
  same value except where a meta solved inside a branch and not taken
  back is now forced lazily instead of inlined. The two are equivalent,
  and the unfolding cache is epoch-guarded. Correct. The `goal_term` in
  lib.rs now moves below the indexed branch, used only by the non-indexed
  path. Fine.
- **`enter` (families.rs:705–736).** The batched `reread` of
  `[env, types, goal, params, indices, result]` at one level, and the
  batched `substitute_folded` of `[env[..base], types[..base], goal]`,
  split back in the same order and lengths. `Rebuild` is a pure function
  of each value, so batching changes only sharing. Correct.
- **`unify_index::solve`.** One `substitute` over everything, then
  `scope.env[y] = t`, same as before. Correct.

## Decisions for Matt

None required. If F1 is fixed as recommended, the "node-for-node
identical to the old path" claim weakens to "identical except that a
glued call that steps at once, inside a value that changes, may stay a
call", which is the exception `Unchanged` already allows. The author or
orchestrator should say so in the doc comment on `Rebuild` (check.rs
~1470–1500).

## Suggested tickets

- F4: memoise `Eq`'s `Shared` parts by address in `Rebuild` and
  `Unchanged` (backlog).
- F5, if not done in this lane: an equivalence test for `Rebuild`
  against `eval ∘ quote`.
- A regression example for SW-1106 itself: nothing in the repo uses the
  `List.replicate 160000` case `Unchanged`'s doc cites (`git grep 160000`
  finds only the comment). That is why F1 got through.
