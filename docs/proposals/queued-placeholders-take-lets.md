# Queued checks' placeholders and `let` variables

**Status:** design note, 22 November 2026 (SW-4596, an Opus paper lane).
Nothing is built and nothing was run: every claim is from reading the code
and the history at `2cf512b94`. The recommendation in [§7](#7-recommendation)
is for Matt to decide.

How claims are marked:

- **[read]**: read in the code or commit named;
- **[inferred]**: follows from what was read, but no test was run to show it;
- **[estimated]**: my judgement; a lane should measure it.

## In plain words

When a check has to wait (a `match` whose type isn't known yet, a literal
whose type is still open), the elaborator puts a *placeholder* where its
term will go and comes back later. The placeholder is an unknown applied to
the variables in scope, so its eventual term can mention them. It is not
applied to `let` variables. So when the waiting check's term mentions a
`let` (`check n`, after `let check := ...`), the term can't say "`check`";
it says what `check` *is*, the whole lambda, pasted in. Later, zonking tries
to recognise the pasted value and put the name back. Three fixes tonight
(SW-4565, SW-4573, SW-4588) taught that recognition new cases, and one case
(`beyond` in `Float.Theory.roundsToInfinity`) still isn't recognised.

Lifted `match` helpers don't have this problem: their unknown *is* applied
to the `let`s in scope, so their call passes `check` itself.

The proposal is to treat placeholders the same way: apply them to the
`let`s too, and tell unification it may ignore those arguments. Then a
waiting check's term names the `let` directly and nothing needs folding
back. That removes the annotation machinery the three fixes built, and the
kernel sees `check n` instead of a lambda applied to `n`.

One finding changes the framing: the brief's diagnosis for `beyond` (the
inner zonk running with no lets) is probably not the cause. `beyond` is a
`let` *with a type*, whose value is elaborated as a bare lambda; the fold
SW-4565 added only fires for a value elaborated as an *annotated* lambda
(an untyped `let`). See [§2.4](#24-why-beyond-is-still-pasted).

## 1. How the two mechanisms differ today

### 1.1 Lifted helpers: lets in the spine

`lift::spine` (`crates/elab/src/lift.rs:225`) gives a helper's frozen
unknown the variables a case split hasn't replaced, *and* every `let` in
scope [read]:

```rust
(0..env.len())
    .filter(|&l| is_var(&env[l], l) || lets.get(l).is_some_and(Option::is_some))
```

The frozen unknown is never solved by unification (its solution is the
call, made at lifting), so it doesn't matter that a `let` slot's argument
is a value rather than a variable. The call `?m n check` passes `check` as
written, and lifting re-creates the `let`s inside the helper
(`with_lets`, `unrefine_body`). This came with "Day 20 fixes: lifted
matches take let values" (`03653f8ee`, 28 Oct 2026) [read].

### 1.2 Queued checks: variables only

A queued item's placeholder is `cx.fresh_meta_of(&ty)`
(`queue.rs:514`), the general unknown-maker in `check.rs:1210`, which
applies the unknown only to slots that are their own variable [read]. A
`let` slot holds its value, never a variable of its own
(docs/proposals/let.md §6.1 rule 1), so it is left out. That was
deliberate and correct for ordinary unknowns: unification solves
`?m x y = rhs` only when every argument is a distinct variable (`solve`,
`unify.rs:3094`, returns `false` at the first argument that isn't one)
[read], and the let note's audit (§A.3) leaned on exactly this to argue that
no solution can mention a `let` variable.

Placeholders inherited this because they *are* ordinary unknowns: D2016
keeps them solvable by unification (the postponement prototype found 14 of
135 fills where unification had solved the placeholder first, and freezing
them broke one example and four AoC proofs; postponement.md §1) [read].

When the item's check returns, `fill` (`queue.rs:1513`) records its term as
a call of the placeholder (`placeholder_call`, `queue.rs:1294`), in the
placeholder's own variables, so zonking can substitute arguments into it
(`zonk_call`, `unify.rs:4216`) instead of reading the solution back. A
`let` variable in the term has no variable of the placeholder to become, so
`placeholder_call` replaces it by the `let`'s value (postponement.md §5,
"A placeholder's term mentioning a `let`'s or a split variable").

### 1.3 The fold back, and what it has needed

Zonking folds a `let`'s value back to its variable inside the `let`'s scope
(`zonk_let`, `refold`, `unify.rs:4510`, `:3792`). The fold is syntactic, so
it has had to learn each form a pasted value can take:

| When | Ticket | Problem | Patch |
|---|---|---|---|
| 8 Nov | SW-2439 | A pasted lambda applied to an argument reached the kernel as a bare redex, `(%arg0 => …) (1, Circle 4)`: E-CANNOT-INFER | Annotate the lambda where it is applied; zonking drops the annotation once folded (`replace_annotating_heads`, `unannotate_let_heads`) |
| 17 Nov | SW-3887 | Folding is by syntax, so `Refl`, `[]` and lambdas were folded into `let`s of the wrong type | Fold only forms whose type they fix (`worth_folding`): lambdas no longer fold |
| 22 Nov | SW-4565 | So an annotated lambda pasted from a placeholder's call no longer folded: `(λ…) b` where `check b` was meant | `zonk_let` also folds the value *as elaborated* when that is an `Ann` |
| 22 Nov | SW-4573 | Same, inside a lifted local function | `around()` in lift.rs offers the annotated value too |
| 22 Nov | SW-4588 | A lambda pasted where it is passed on (`?m n check`), not applied, went in bare, and ended up applied in a decision's proposition: kernel E-CANNOT-INFER | `placeholder_call` annotates a lambda value wherever it occurs, using the `let`'s value as elaborated; 134 std hashes moved |

Every row is the same root: a value is written where its name was, and a
later pass has to guess the name back.

## 2. What still goes wrong

### 2.1 The brief's case

`Float.Theory.roundsToInfinity` (`crates/elab/src/std/Float/Theory.sw:420`)
has `let beyond: 9218868437227405312 ≤ p → … := hp => …`, used inside two
nested `match`es inside another `let`'s lambda. After SW-4588 the term
holds `beyond`'s lambda pasted and annotated, not `beyond` [read: the
SW-4588 commit message says so].

### 2.2 The inner zonk with no lets

`zonk_call` zonks a queued check's recorded call in the call's own
variables with no `let`s (`zonk_in(g, n, call, keep, &[])`,
`unify.rs:4245`), then substitutes the arguments, then refolds the result
with the real `lets` (`refold(out)`) [read]. Folding inside the call can't
help anyway: the call's variables are the placeholder's spine, and no `let`
is among them, so there is no variable to fold *to*. The outer refold,
after substitution, sees everything the inner call pasted, at the right
level. So the empty `lets` there loses nothing that matters [inferred].

### 2.3 What `zonk_let` folds

For each `let`, `zonk_let` folds the normal forms of its value that fix
their type (a lambda never does, since SW-3887), plus, since SW-4565, the
value as elaborated *if that is an annotation* [read, `unify.rs:4529-4541`].

### 2.4 Why `beyond` is still pasted

- An untyped `let check := (r: List Nat) => …` is elaborated by inferring
  the value: an inferred lambda is `Ann(λ…, T)`. `placeholder_call` pastes
  that same `Ann`, and `zonk_let` folds it. This is SW-4588's test, and it
  passes [read].
- A typed `let beyond: T := hp => …` is elaborated by *checking* the value
  against `T` (`effects.rs`, `Expr::Let` with `Some(ty)`: `check(cx, value,
  &ty)`), which gives a bare `λ…` [read]. `placeholder_call` wraps it as
  `Ann(λ…, T)` itself (`queue.rs:1339-1342`), but `zonk_let` offers the
  extra form only when the value is already an `Ann`, and the bare lambda's
  normal forms aren't folded. So nothing matches, and `beyond` stays pasted,
  annotated [inferred].

So I expect the same thing with a typed `let` lambda through a *single*
queued `match`; the nesting is probably incidental. A lane can confirm this
with one example file before anything else (§8, step 0). If it holds, a
two-line fix in `zonk_let` (also offer `Ann(v, A)` when `v` is a lambda)
closes `beyond` within today's design.

## 3. The change: placeholders take the `let`s

1. A queued item's placeholder is applied to `lift::spine`'s variables: the
   plain ones and the `let`s in scope, in context order. (A new
   `Ctx::fresh_placeholder`; `fresh_meta` itself is unchanged, since
   ordinary unknowns must stay patterns.) A literal's closed placeholder
   (D2126) stays applied to nothing.
2. The unknown records which of its arguments are `let` positions, and
   unification never needs them to be variables: `solve` skips them, as it
   skips `ignorable` positions today (SW-323, SW-3890), and builds the
   solution without them. Skipping must come *before* forcing the argument:
   a deferred `let`'s value (`?d _ x₀ … xₙ`) is computed when forced, and a
   long list in `main` is deferred precisely so that this never happens
   (let.md §A.3). It should be a mark of its own, not the existing
   `ignorable` mask, because the flex-flex rule prefers to leave an
   ignorable unknown unsolved (SW-3890, `unify.rs:2021`), which would undo
   D2016's "placeholders are solved first" in those pairs.
3. `placeholder_call` maps a `let` variable to the placeholder's argument
   for it, as it maps plain variables. Its value-pasting path remains only
   for variables a case split replaced (by constructor terms, which fold
   back as they always have, or are read back).

Ignoring a `let` position is a correct solution, not only an allowed one:
every occurrence of the placeholder has the `let`'s own variable at that
position (it is only ever applied syntactically, and lifting re-creates the
`let` with the same value), so the argument there is always the `let`'s
value, which the solution already uses wherever `rhs` does [inferred].

## 4. What it would change

### 4.1 Terms

The declaration's term, as the elaborator writes it, holds `?p x check`
where it held `?p x`. Zonking substitutes `check` (the variable, at the use
site) into the recorded call, so the result says `check n`, never the
lambda. This is the path of nearly every queued check's term: the term the
check returned, written where the placeholder stood [inferred].

What doesn't change: a placeholder met *inside a value* that is later
quoted (an expected type, a motive) quotes its `let` argument as the
`let`'s value, because values don't know `let`s (rule 1). Zonking then
substitutes that value into the call, and refolding treats it as it does
today. Those occurrences are in types, where a pasted value is harmless to
the kernel; but the fold-back machinery isn't made unnecessary everywhere
[inferred].

### 4.2 Hashes

A declaration's hash changes where today's term differs from "the
variable": wherever the fold missed (`beyond`), and wherever SW-3887 stopped
folding a value whose form doesn't fix its type (a `let xs: List Nat :=
[]` pasted as `[]`, a lambda) through a placeholder. Where the fold
succeeds today, the result is already the variable and the hash stays.
SW-4588 moved 134 std hashes and six example snapshots while only changing
annotations and refolds, so I expect tens to low hundreds of std hashes
and a handful of example snapshots, mostly in Float.Theory and the
let-lambda examples [estimated]. Under D2303 this is not a cost, but the
lane re-records all of `hash_stability` (prelude, examples, projects).

### 4.3 Code that becomes dead

[inferred, each to be confirmed by the lane with a counter or
`debug_assert!` over the hash tests before deleting]:

- `placeholder_call`'s `let` branch: the annotated-lambda construction
  (SW-2439, SW-4588), the `lambda` helper, and the `annotated` flag in
  `lifted_calls`' entries.
- `unannotate_let_heads` in `zonk_call` (SW-2439's other half).
- `zonk_let`'s extra `Ann` form (SW-4565): annotated `let` values enter
  solutions only through placeholders' pasted values; unification's own
  solutions are read back from values and never hold one.
- The `Ann` form in lift.rs's `around()` (SW-4573), for the same reason.
- The `read back` counter's `let` case (postponement.md §5): a `let` is
  always in the placeholder's variables now; split variables remain.

Not dead: `refold` and `worth_folding` stay, for unknowns solved by
unification (an implicit argument, a decision procedure: `decLessEq (n + 1)
2` after `let m := n + 1`), for the quoted occurrences of §4.1, and for
lifting's helpers.

### 4.4 What the kernel sees

The kernel's `let` is transparent: in `b`, `x` evaluates to `v`'s value
(docs/core.md, `Let`). So `check n` with `check: T := λ…` is inferred from
the context's `check: T`, and anywhere the proof needs the value, the
kernel unfolds `check` itself (ζ). The kernel already checks exactly such
terms whenever a user writes `check n` outside a `match`. Nothing about the
kernel changes, and there is no `docs/core.md` update [read, core.md
`Let`].

## 5. Costs

- **Arity.** Each queued placeholder gains one argument per `let` in scope.
  Most declarations have a handful of `let`s; long `main` blocks and AoC
  days have tens. The argument is a variable in the term and an `Rc` clone
  of the `let`'s value in the evaluated neutral [estimated: a few percent
  more elaborator nodes for placeholders in let-heavy files, nothing
  elsewhere].
- **Solving.** `solve` loops over a longer spine and skips the `let`
  positions without forcing them. Flex-flex pairs of the same placeholder
  compare the `let` arguments pairwise, normally the same value, so
  pointer-equal or cheap [estimated: negligible].
- **Quoting.** A placeholder neutral quoted for an error message, a type
  read back or a motive now writes its `let` arguments as their values. For
  a cheap value that is a small stuck term; for a deferred one it is the
  `?d` application, written without computing [read: `define`'s deferral]
  [estimated: small; this is the cost to watch].
- **Savings.** `placeholder_call` no longer quotes each `let` value its term
  mentions (`cx.quote_folded(&cx.env[level])`) and builds no annotations,
  and zonking has fewer folds to find. For a large `let` used in a waiting
  check this is the larger effect [estimated].
- **Step counts.** Net: within ±2% of evaluation steps on any one
  declaration, and unchanged for declarations with no `let` in scope of a
  queued check [estimated]. The lane measures it (§8).

## 6. Risks

- **Conversion that needs the value.** Unification still sees the value:
  the `let` argument evaluates to it, and nothing the solver compares stops
  being the value. The kernel unfolds `check` by ζ as needed (§4.4). No
  comparison should lose information [inferred].
- **Dependent `let`s.** `let n := 3; let v: Vec n := …` puts both in the
  spine, in context order. Values never mention a `let` variable (rule 1),
  so the placeholder's recorded type (`Meta::ty` with its arity) needs no
  `let` binder to depend on; lifting re-creates dependent `let`s in order
  already, for helpers, and a placeholder lifted into a helper rides on the
  same code [inferred]. The lane's tests include one.
- **Pruning.** When a placeholder occurs inside another unknown's solution
  and that unknown can't see a variable the `let`'s value mentions,
  renaming prunes the argument and solves the placeholder with a pruned
  copy. The placeholder keeps its recorded call (`lifted_calls` is keyed by
  the placeholder and checked against the argument count at the use site),
  so its zonk is unchanged [inferred]. Rare: a `let`'s value mentions only
  variables older than the `let`.
- **Unification behaviour.** The new mark changes nothing for positions
  that are variables, and only allows what was refused before (a solution
  ignoring a value argument). Messages that print a placeholder applied to
  its arguments (`?5 b b` in postponement.md stage 3) would print the
  `let`s too; `queue_item`'s display only names spine arguments already
  [read], so the lane checks the stuck-report wording on one example.
- **Soundness.** None in the kernel, which re-checks every term and is
  unchanged. A mistake here shows up as a kernel rejection
  (E-CANNOT-INFER, a mismatch) or an elaboration that now fails, not as a
  false theorem accepted. The one claim that needs care is that ignoring a
  `let` position is a valid solution (§3), and the kernel would refuse a
  term built on a wrong one.

## 7. Recommendation

**Do it, after a one-file check of §2.4.** The end state is one mechanism
for both kinds of deferred term, the one helpers already use, and the
annotation-and-refold patches of SW-2439, SW-4565, SW-4573 and SW-4588
become dead code. The alternatives each patch one more symptom:

- **Make `zonk_call` know the `let`s** (the brief's suggestion): doesn't
  work as stated, because the call's variables don't include the `let`s, so
  inside the call there's nothing to fold to; the fold after substitution
  already happens (§2.2).
- **Teach `zonk_let` the typed-let form** (`Ann(v, A)` when `v` is a
  lambda): two lines, probably closes `beyond`, keeps the pasting and the
  fold-back's syntactic guessing, and the next form that slips through is
  another fix. Worth doing only if Matt says no to the change.
- **Freeze placeholders** like helpers' unknowns: then lets could join the
  spine with no unification change, but it reverses D2016, which broke one
  example and four AoC proofs in the prototype.

## 8. A first implementation lane

Opus (elaborator core: unification and the queue), expected about 90 min
of agent time [estimated from SW-4588's size].

0. Write `examples/accept/let-typed-lambda-prop-match.sw`: SW-4588's test
   with a typed `let` (`let check: List Nat → Prop := r => 3 ∈ r`) through
   one queued `match`, with its hash snapshot. If its term pastes the
   lambda today, §2.4 is confirmed; note the result on the ticket.
1. `Ctx::fresh_placeholder` (spine from `lift::spine`), used by
   `queue_item` and `queue_constraint`; a `Meta` mark for `let` positions,
   and `solve` / `solve_abstracting` / `prune` skipping them before forcing.
2. `placeholder_call` maps `let` variables to their arguments; delete the
   `let` branch, `annotated`, `unannotate_let_heads`, and (after a
   `debug_assert!` that they never fire over the tests below) SW-4565's and
   SW-4573's `Ann` forms.
3. Tests, by name, one at a time: the step 0 example, SW-4588's
   `let-lambda-prop-match`, SW-2439's fuzz case, the postponement tests
   SW-4565 and SW-4573 rely on (`a_decision_waits_for_a_field_in_its_proposition`
   and `a_lifted_let_lambda_folds_like_the_annotated_one`, both in
   `crates/driver/tests/elaboration/postponement.rs`), the let-lambda example kinds
   (`lambda-inferred`, `lambda-nested-arrows`, `postpone-let-lambda-*`,
   `postpone-decide-waiting-field`), a new example with dependent `let`s
   and a waiting check, and a new one with a deferred (large) `let` in scope
   of a queued literal, showing the value isn't computed. Then
   `task test:hashes ALL=1` (term-changing lanes re-record all of
   hash_stability), and a check of `Float.Theory` alone.
4. **Step-count measure:** `stitchwort check --no-cache --timings=all --only
   <decl> <namespace>` before and after, for
   `Float.Theory.roundsToInfinity`, `Aoc.Year2020.Day16.Proofs.runsNotes`
   (the `step_counts` test's subject), and the let-heavy examples above;
   plus the queue's `read back` and `solved first` counters
   (`STITCHWORT_TIMINGS`) on the same runs. A performance-log entry
   records the numbers (D3444). Over 5% more steps on any of them stops the
   lane for a look before merging.
5. Done when `beyond`'s term says `beyond (…)`, the dead code is gone, and
   the hashes are re-recorded.
