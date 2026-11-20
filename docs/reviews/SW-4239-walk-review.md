# Review of the walk step, W1 (SW-4239), for W2 (SW-4354)

Opus paper review, 20 Nov 2026. Branch `lane/SW-4239` (4 commits, 5b13a61ba..a18e1e4d8), 39 files, +3106/−38. Read against `docs/reviews/SW-4238-walk-step-review.md` (§3, §4) and D3696/D3700. Nothing was built or run; every claim below is from reading the code, and line numbers are `crates/elab/src/walk.rs` on the branch unless another file is named.

## Verdict

**Merge after named fixes.** There is no soundness hole. Every term the walk returns either comes from `check` on syntax the walk wrote, from the ordinary proof `match` (`generalised_named`), or is a trivial closer (`()`, a hypothesis variable after `unify`, `Refl` after `conv_now`), and the kernel re-checks the whole declaration as it does any other. The fixes are about the design's own rule, "two candidates is an error, never a choice", which the code keeps in the four tiers but breaks in four other places, and about one bug that W4 will hit on its first tagged function. All are small.

## Must fix before merging

1. **Family precedence in a bind (`bind_step`, 1810-1821; `choose`, 1421-1571).** `ordered` is built as if order mattered (the goal's relation, then the then-lemmas' first relations, then every other loaded family), but `choose` only asks `families.contains(..)`. So in a `Gives` walk, a call of a function with `@[walk]` lemmas in both `Gives` and `ReadsIn` (or `ReadsAt`) fails with "two lemmas fit this call among the registered lemmas". The same happens in tier 3 with `nextGives` and `nextReads` hypotheses. That is the end state the design wants ("one lemma per function and family"), so W4 meets it as soon as it tags a function's `gives` and `reads` lemmas. Tail calls don't have the bug, since they pass only `[family.relation]`. **Change:** inside each tier, try the families in rank order (the goal's relation; then the then-lemmas' first relations, such as `Reads0`; then the rest) and take the first rank that has any fit. Two fits within one rank stay an error. Add one accept case: a function with both a `Gives` and a `ReadsIn` `@[walk]` lemma, called in a bind.

2. **One `@[walk.done]`, one `@[walk.weaken]`, and one `@[walk.bind]` per first relation, in each family (`register_walk`, 341-358; `families`, 521-540).** Registration checks uniqueness only for `@[walk]`. `families` keeps the lowest-`DefId` done or weaken lemma (`family.done.or(Some(id))`), and `bind_step`'s `.find(..)` takes the first then-lemma for a relation. `DefId` order follows load order, and std loads lazily, so a second tagged done-lemma would be picked by load order, silently. **Change:** in `register_walk`, raise `E-WALK-LEMMA` for a second done or weaken lemma of the same relation, and for a second bind lemma with the same (relation, first-premise relation), naming the first, as the `@[walk]` arm already does. Add a reject example.

3. **Two "first hypothesis that unifies" loops that can fix unknowns.** The design's rule (SW-4238 §3.3) is that a premise is filled only when its type is fully known after matching, or when exactly one candidate fits.
   - `fit_type`, 1293-1303: for each proposition premise, the most recent hypothesis that unifies is taken (`break`). That choice can fix lemma unknowns which then become `Param::Value`/`Param::Known` arguments in the proof.
   - `leaf`, 2204-2216: "a hypothesis that is the goal, fixing what the goal leaves open". Where the goal still has an unknown, the most recent hypothesis that unifies decides it.

   Both are deterministic for a given context, but they are choices, and adding or reordering a hypothesis changes the proof: the brittleness §3.9 warned about. **Change:** where the type has an unknown in it, try every candidate under a `Snapshot` and use one only if it is the only one that unifies. Otherwise leave the unknown (fit), or wait or stop (leaf). Where the goal is closed, keeping the first is fine: any proof of a closed proposition will do. The value-argument loop (1314-1337) already does this right and is the model.

4. **Registered lemmas and families from namespaces the walk can't see.** `walk_tags` holds every tagged theorem elaborated so far in the session, and tier 4 (1512-1548) and `families` read all of it. A walk in namespace A can therefore find a `@[walk]` lemma, or a family, from a namespace B that A doesn't import, if B happened to be checked first, so the result depends on check order (full check, `--only`, the editor, cache hits). Tier 4 then applies it by full name, which resolves without an import (syntax.md, "A qualified name"). The cache key of A doesn't cover B, so the second-order risk is a stale cache entry. This is the project-side form of SW-4238 §3.11's gap. **Change:** keep only lemmas declared in std, in the walk's own namespace, or in a namespace it imports (transitively). Add a two-namespace accept test where the non-imported lemma is ignored.

5. **A bracket item that doesn't elaborate is silently ignored (`fit_expr`, 1395-1409).** A non-fatal error from `infer` means "doesn't fit", so `byWalking [givesBumpp]` (a typo), or `unfold` applied to something that isn't a name, gives no error about the item. The walk goes on to the registry and may succeed with a different lemma, or stop with "no lemma for this call", which points the wrong way. **Change:** in `start`, infer each `Item::Lemma` once and report its error as it stands. Keep the per-call `fit_expr` as now. An unknown name after `unfold` should also be `E-UNKNOWN-NAME` (see follow-up 4).

6. **Tests for the two rules the review is about.**
   - `examples/reject/walk-two-lemmas.sw` tests only `E-WALK-LEMMA` at registration. Add one where two *hypotheses* fit a call (tier 3), and one where two bracket items do (tier 1). These are the "never a choice" rule at walk time, which nothing exercises.
   - Bar 4 ("every expansion checks") is a claim in the ticket, with no test behind it. `--expand-walk` builds text by matching on the display (`condition_text`; `Param::Known`'s `shown`) and re-indents by counting brackets (`render`), so it is the most fragile code in the lane. Add one CLI test that expands a copy of `examples/accept/walk.sw` and checks the result, snapshotting the text and the trace.

7. **Small cleanups.** Leftovers that look like clippy workarounds: `let _ = call;` (662), `let _ = node;` and the unused `node` parameter of `applied` (1644), `let _ = i;` (1888; loop over `explicit.len() - 2` instead), `walks_before` (1995, 2013), `is_var` (2093, 2097). `applied` has two doc summaries (1591-1595). `split`'s doc says the equation is named "when the scrutinee isn't a variable", but it always is. `state/tables.rs`'s comment still says `@[walk.then]`.

## Follow-ups to file

1. **`check --only` and `@[walk]` lemmas** (before W4). `--only` keeps a theorem only if a kept declaration *writes* its name. A walk uses registered and family lemmas without writing them, so `check --only T` can skip the `@[walk]` lemma T needs, and the walk then fails where a full check passes. It fails rather than passing wrongly, but proof lanes use `--only` all the time. Treat walk-tagged theorems as needed by any kept walk (`names_and_proofs` in `module.rs` already adds `omega`'s names for this reason).
2. **Std's walk index** (SW-4238 §3.11; in W1's scope, not done). Today it is harmless: std tags only family lemmas, each in the file that defines its relation. Until the index exists, the rule should be written down where std lemmas are tagged: no `@[walk]` call lemma in std outside its relation's file.
3. **The expansion's text.** It takes conditions and known values from the compiler's display (`(n.decLessEq limit).holds`; `condition_text` rewrites `(T.%decide a b).holds` only when `a` and `b` are single words). `render` counts brackets inside string literals. `write_walk_expansions` writes back any source with a walk, falling back to a path relative to the working folder, which for a library file would create a stray file: write project files only. The end state is printing from terms with a printer that guarantees re-parsing, or quoting source spans where the split comes from a written `if`/`match`.
4. **Resolve `unfold f` to a definition at the start of the walk.** Today `unfolds` (1194) matches by name suffix (`unfold full` matches every `….full`), an unknown name does nothing, and `unfold` of the theorem's own function would be unfolded at the recursive call instead of using the theorem (SW-4238 §3.3: "never unfolded").
5. **Check time.** `by_arithmetic` (2310) shrinks the fact list by running `arithmetic` up to n+1 times at every leaf, on every check, only to make the expansion's text shorter: do that only when expansions are asked for. `families(cx)` is recomputed at every step and inside `thunk_index` for every hypothesis tried. Tier 4 and `register_walk` scan all of `walk_tags` (quadratic at load once some thousand lemmas are tagged). Index by (relation, head). This is for W6, or sooner if bar 2 slips.
6. **`session.walks` grows without bound.** Each check of a walk (retries included) appends nodes, and they are never taken back. That is fine for one `check`, but a leak in a long editor session. Clear it at the end of each declaration unless expansions are being recorded.
7. **Error place.** `E-WALK` always labels the `byWalking` word. The place text gives the function and the splits taken, but not which call in a straight-line body (two `look()` calls read the same). Add the binders passed (`in lookTwice, after first`). This is the design's "its place in the program, the path taken".
8. **`generated` treats a binder named `x` as the compiler's** (1684). A user's hypothesis `x` is then skipped by the leaf closer, value filling and the conjunct facts. Mark compiler binders by kind, not by name.
9. **The self-hosted formatter's parser** (`tools/fmt`) doesn't know `byWalking`, and `tools/fmt/src/Syntax/ParseWalk.sw` now uses it. That needs settling before the switch-over to the self-hosted formatter (D3573), along with editor highlighting.
10. **An unused bracket item** (one that fit no call) could warn, as Lean's unused-simp-argument linter does. It helps brittleness (§3.9).
11. **`split`'s goal is not checked against the node's goal.** `step` passes the refolded `goal` (built from `unfold_once` and `Reduced` steps) to `split`, and returns the term as if it had type `expected`, without `conv_now(goal, expected)`. It is correct by construction (each step is a definitional unfolding), and the kernel would catch a mistake, but as an internal error rather than `E-WALK`. A one-line check would turn a future bug into a clear message. The branch goals themselves are checked (`planned_goal`, 748).
12. **Split `walk.rs`** (see "Code health"), ideally before W3 adds the two-run families.

## The nine questions

### 1. Soundness

There is no way past the kernel.

- **Terms.** `check_written` elaborates syntax the walk wrote, with names resolved through the normal scope. `split` uses the elaborator's proof `match`. The leaf closers return `Term::Ctor(Trivial)` on `Unit`, `Term::Var` after `unify(hypothesis, goal)`, `Term::Refl` after `conv_now(l, r)`, or `cases`' and `arithmetic`'s own terms. `Param::Known` values are local definitions (`bind_local`), which are substituted where they are used (`Ctx::local`), so nothing dangles after `cx.reset(mark)`. The kernel re-checks the declaration from scratch (core.md, row 1).
- **Unchecked conversion.** There is one, `split`'s refolded goal (follow-up 11). Branch goals are checked by `conv_now` (748). Neither can make a false statement pass, since the kernel would refuse it.
- **Cache.** `walk_tags` is a new table, encoded, replayed and rewound like `rule_sets`; format 36 → 37 is right. Walk *results* are never cached apart from their declaration's checked term. `--expand-walk` turns the cache off, as `--expand-repeatedly` does.
- **Fallbacks.** No path takes the goal on trust. "Waits" goes through `tactic_or_wait`, which re-runs the walk later. A `then t` failure is an error, not a fallback.
- **Stand-ins:** below (question 5).

The one soundness-adjacent risk is the cache key for a lemma taken from a namespace the walk's namespace doesn't import (must-fix 4).

### 2. Determinism, and "two at a tier is an error"

- **The four tiers keep the rule.** Brackets (1444), hypotheses (1493) and the registry (1530) collect every fit and stop at two; the theorem itself is a single candidate. Hash-map order doesn't matter, since all fits are collected.
- **Where the rule is broken:** the premise and leaf hypothesis loops (must-fix 3); done, weaken and bind lemmas chosen by `DefId` order (must-fix 2); the family-rank bug (must-fix 1), which errs rather than chooses but turns on which families happen to be loaded; and visibility (must-fix 4).
- **Retries.** Each run of `start` files a new `CallInfo`. A place checked again clears its trace and replaces its text, so the expansion and the path cap see the chain as it stands. A run that fails while the goal still has an unknown is queued and re-run (`tactic_or_wait`), so a "two fit" seen under an unknown waits rather than failing. The outcome is the last run's, which is as deterministic as the elaborator's own retrying. Retries can't change the pick except by making more of the goal known, which is the point of them.
- **Hypothesis order** matters only in the loops of must-fix 3.

### 3. Generality

Met. `walk.rs` names no family. The only std-flavoured text is `condition_text`'s display rewrite (`%decide`, `.holds`), which is about `Decidable`, not `Parse`. Families come from `@[walk.bind]`, `@[walk.done]` and `@[walk.weaken]`. The bridge (`givesAfter0`'s `Reads0`) is read off the bind lemma's first premise. The equation names (`branchN`) and binder names come from the program or from the lemma's own binders.

### 4. The checker change

It can't change any existing program. It isn't a move: `check_special` gains an arm that matches only `Expr::Walk`, a new variant, placed before the forcing so that the family is read off the goal as written. The parser makes `Expr::Walk` only for the word `byWalking` immediately followed by `[` at the start of a term, and nothing on `main` writes that (checked by grep; the only hits are the board). `infer` on a walk is a clear `E-WALK` (`no_goal`). The other new `Expr::Walk` arms (autobind, nav, numbers, proof_chain, spans, `has_nested`, `take_children`, `names_and_proofs`) only add traversal.

### 5. Stand-ins registering `@[walk]`

Safe. A stand-in is filed only for a declaration that failed, whose error has already been reported. A walk that uses it refers to it by name through the scope (`var(name)` → `Global::Def(stand-in)`), so the using declaration relies on the stand-in like any other use, and nothing relying on one is reported finished (core.md, assumptions). This mirrors `@[reading]`. What the walk gains is fewer cascading errors. One wrinkle: if a later, correct lemma for the same function is tagged, it gets `E-WALK-LEMMA` against the broken one. That is noise only while the first is broken.

### 6. Error quality

- **`E-WALK-LEMMA`:** good. It names the function and the first lemma, labels both attributes, and gives the cure.
- **`E-WALK`:** meets bar 3 as written. Each reject names the construct or call (the call itself in a note), shows the goal there, and gives the fix where there is one: brackets, `@[walk]` or `unfold f`; make the split a function; `then t` or expand.
- **Weak points:**
  - The label is always the walk word, and the place doesn't tell two calls of one function apart (follow-up 7).
  - A step that fails to check wraps the inner error into a note as `CODE: message`, losing its labels.
  - A misspelled bracket item says nothing (must-fix 5).
  - The two-lemmas-at-walk-time message is good but untested (must-fix 6).

### 7. Docs

guide 10-proofs.md, syntax.md and proving-guide.md match the code, with these gaps:

- **syntax.md: premises.** It says a lemma's "other arguments are what the call fixes, or the one hypothesis of their type". The code also fills premises by the first hypothesis that unifies, which must-fix 3 removes. After the fix the text is right.
- **syntax.md: family limits.** It doesn't say that a family has one done, one weaken and one bind lemma per first relation (must-fix 2 makes that true). It should also say that `then t` is checked once at each leaf, with errors naming the path, as SW-4238 §3.8 asked so that it reads like D3694's or-patterns. The place text does name the path.
- **proving-guide.md.** It advises leaving `[j := …]`-style lemmas (`readsAtAfterLeft`) to a hand proof, but the ticket says the walk reads `j` off the code there. One of the two is out of date; the lane should say which.
- **Guide example.** It is the accept example's `capped`. That's fine, and it is checked by the snippet mechanism.

### 8. The bars (SW-4238 §4)

Most bars are W4's. What W1 shows:

| Bar | Evidence on the branch | Judgement |
|---|---|---|
| 1, lines | 3 pilot walks; the section went from 204 to 186 lines, nearly all of it `givesCommaListFrom` (20 → 1); `readsParenOn` not shorter | Encouraging on one theorem; it is W4's to measure |
| 2, check time | `ParseWalk --no-cache` 21.6 s against 22.2 s, one run each | A file total with 3 walks in it says little about the walks themselves; W4 should time per theorem (`--timings`) |
| 3, rejects | missing lemma, false leaf, handle, path cap: each names the call or construct and shows the goal; "two lemmas" only at registration | Met, except walk-time two-fit (must-fix 6) |
| 4, expansions check | claimed ("every expansion tried re-checks"), no test | Needs the test (must-fix 6) |
| 5-7 | not W1's | n/a |
| W1 scope list | binds, the four tiers, `unfold`, splits with the cap, values, weaken, closers, names, `E-WALK`, attributes, `--expand-walk` and the trace, a failed walk expanded with `?`, guide, syntax.md, examples: all present. **Std's index entries: missing** (follow-up 2) | |

### 9. Code health

At 2,478 lines `walk.rs` is long but readable, and the module doc is a good map. Before W3 adds the two-run families (which will roughly double the stepping code), split it into a `walk/` module along seams that already exist:

- `walk/registry.rs`: `register_walk`, `Shape`/`statement`, `Family`/`families`, `thunk_index`, about 250 lines, and the place where the index of follow-up 5 would go;
- `walk/expand.rs`: `Walks::{splits, expansion, flatten}`, `atomic`, `render`, `expand_file`, `trace_line`, `condition_text`, about 350 lines;
- `walk/leaf.rs`: `leaf`, `by_arithmetic`, `conjunct_facts`, about 220 lines;
- `walk.rs`: `start`, `go_on`, `step`, `classify`, `case_tree`, `choose`/`fit_*`, `bind_step`/`done_step`/`tail_call`/`split`.

Simplifications worth doing then:

- `split`'s tuple parameter and `bind_step`'s `too_many_arguments` both want a small `Here { node, info, family }` struct.
- `families` should be computed once per walk and kept on `CallInfo` (with must-fix 2 it can also be checked once).
- The resume-by-node-id design, with the session-wide node table referenced from synthetic `Expr::Walk { resume }`, is sound and fits the elaborator's queueing. Its one cost is follow-up 6.

None of this blocks the merge. The cleanups in must-fix 7 do.
