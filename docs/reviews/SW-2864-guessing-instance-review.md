# SW-2864 review: choosing a call's instance from the expected type

Paper review (Opus, 11 Nov 2026) of `lane/SW-2864` at d6e792317: no builds
or tests were run. Line numbers are in that commit.

The change adds `interfaces::unify_guessing_instance`
(`crates/elab/src/interfaces.rs:1771-1851`) as a fourth comparison in
`finish_application` (`crates/elab/src/check.rs:3307`). It is reached only
when the application has arguments waiting for the expected type
(`after_expected`) and the plain, solving-arguments and waiting comparisons
have all failed. If exactly one interface obligation made since the
application began is unsolved, it tries every valid instance of that
interface that has no parameters, each inside a snapshot that it then
restores. It commits only if exactly one fits.

## Verdicts

| # | Question | Verdict |
|---|----------|---------|
| 1 | Can it pick a wrong instance? | OK (with notes) |
| 2 | Are all trials undone? | OK (with one note) |
| 2b | Does it run the obligation in the right context? | **MUST-FIX** |
| 3 | Cost | NOTE (fine for now; follow-up suggested) |
| 4 | Error quality | SHOULD-FIX |
| 5 | Right fix, compared with keeping folded calls | Keep this direction; change the mechanism later (see below) |
| 6 | Example and aoc edit | OK |
| 7 | Other | SHOULD-FIX (comments/spec), NOTEs |

## 1. Coherence with normal resolution: OK

- The guess only chooses the type's **head**. The dictionary itself still
  comes from `interfaces::attempt` (`:1848`), the same resolution as usual.
  That includes step 4: a dictionary in scope for the head is preferred to
  the global instance. Global instances are keyed by `(interface, head)`, so
  each head has only one. For any head it tries, the guess gives the
  dictionary that resolution would give later.
- The head is committed only if exactly one candidate makes `ty` unify with
  `expected`. A trial that "fits" only because it solved an outer unknown
  (one below `metas_from`, inside `expected`) fits for every candidate. That
  gives several fits, so nothing is chosen. This is safe.
- The hash snapshot is good evidence: `sumsDiffer` (guessed), `typed`
  (`[a := Nat]`) and `operands` (`[x := a + a]`) all hash to `3ae4a159…`. So
  the guessed elaboration gives exactly the term that the explicit forms
  give.
- NOTE: "exactly one" means one among the candidates it tries. Those are
  only the instances without parameters (`:1803`). It leaves out instances
  with head variables (`Fin n`, `Mod n`, `Set k`) and those with
  prerequisites (`List a`, `Pair a b`, `Option a`), and local dictionaries
  are never candidates for the head. In principle, a type the guess can't
  see could be the intended one while one head it can see also fits. That
  needs two instances whose methods unfold to the same thing, such as a
  wrapper type's instance that reuses `Nat.decEq` on its field, with the
  unifier solving `?x : ?a` with a value of a different type. I found no
  such pair in std. The derived instances (`T.%decEq`) are matches on the
  constructor, so they don't unfold to another type's decider. The kernel
  re-checks the final term anyway, so the worst case is a confusing error,
  never an unsound acceptance.
- NOTE: the limitation users will see: `DecEq.trueOfNe (same => …)` against
  `(xs != ys) = True` on `List Nat`, `Fin n` or `Set k` operands still
  fails, because their instances have parameters. The doc comment should
  say so, or the follow-up in (5) should lift it.

## 2. Trials undone: OK

`undo::Snapshot::take`/`restore` (`:1811-1813`) covers the metavariables
and their trail, obligations, the queue and its resumption log, row
constraints, drafts, `meta_names`, `local_dictionaries` (cut by trail),
`operator_dictionaries`, goals, local types, steps, the span and context.
Restore runs before `fits?`, so it also happens when a trial errors. Two
things are not restored:

- `instance_steps` is not refunded, by design (`state/attempt.rs:104-109`).
  Each trial spends at least one step of `ob.tree`'s budget of 10,000, plus
  one for each local dictionary of the interface. That is negligible.
- `call_memo` is set by a guard on the outermost `unify::run`. Each trial's
  `cx.unify` is its own outermost run unless `finish_application` is itself
  nested inside a comparison, for example through queue resumption. In
  that case, pairs found different under a trial assignment would stay in
  the memo after restore. That exposure isn't new: every `undo::unify` has
  it. NOTE only.

Diagnostics: `attempt` builds its `Wait` and error diagnostics as values
and doesn't push them anywhere, so nothing leaks.

## 2b. MUST-FIX: the obligation is tried in the application's context, not its own

`guess_with` calls `attempt(cx, ob, …)` (`:1848`) and `cx.unify(arg, …)`
(`:1844`) with the application's `cx`. Every other caller of
`interfaces::attempt` first builds the obligation's own context:

```rust
let mut ob_cx = Ctx::from_parts(self, ob.env.clone(), ob.types.clone(), ob.names.clone(), ob.span);
```

(`auto.rs:143-151`, `interfaces.rs:1495-1506`). `attempt` evaluates
`ob.meta`, which is the metavariable applied to the obligation's context
variables as de Bruijn indices, with `cx.eval`, and it scans `locals(cx)`.

The obligations collected at `:1782-1793` are every unsolved interface
obligation with a metavariable `>= metas_from`. That covers more than the
call's own dictionaries ("the one dictionary this application made", says
the doc). It also includes those made while the application's other
arguments were checked: the `postponed` lambdas checked at the top of
`finish_application`, and any lambda nested inside an in-place argument,
such as `f (xs.map (x => x == y)) (z => …)` with `x`'s type still unknown.
Such an obligation lives in a deeper context. Evaluating its `ob.meta` in
the shallower `cx` takes `env[env.len() - 1 - ix]`
(`crates/core/src/value.rs:1486`), which underflows and panics. If the
context is the other way round, it reads the wrong variables without any
error. In both cases, a program that used to get a clean mismatch error can
now crash the elaborator or give a wrong guess.

Fix, either:

- (preferred) restrict the candidates to the application's own
  dictionaries. `own_dictionaries(&term)` already computes them
  (`check.rs:3326`). Pass them in, which also makes the doc comment true;
  or
- run `attempt`, and the `arg` unification, in
  `Ctx::from_parts(cx.e, ob.env, ob.types, ob.names, ob.span)`, keeping the
  snapshot on `cx` (they share `cx.e.attempt`).

Either way, add an accept or reject example where the call's own
dictionary is solved but a nested lambda's `==` dictionary is not, and
check that it gives the old mismatch error and doesn't panic.

## 3. Cost: NOTE

- It is reached only on a failing comparison in an application with
  `after_expected` arguments and exactly one unsolved dictionary. Before
  this change, that was always an error return.
- Candidates are the valid instances of that interface with no parameters.
  In std, `DecEq` has 11 (Nat, Int, Bool, Char, Text, Ordering, Unit,
  Float, SafeNat, SafeInt, Key), plus one derived `T.%instDecEq` for every
  type a program declares without parameters (`derive.rs`). An AoC day
  with `Aoc.Common` has a few dozen; `games/rogue` likely has 100 or more.
  `Show` has about 20 in std and `Ord` 18, plus derived ones. Each trial is
  an `arg` unification, an `attempt` (which scans the context's
  dictionaries) and a full `unify(ty, expected)`. The `heads` loop also
  iterates the whole instance table to filter it. In the worst case that
  is a few hundred comparisons, around tens of milliseconds (estimated),
  per failing application. This is acceptable on genuine errors.
- The one place it matters on successful elaborations is speculative
  checks that fail and fall back to another way. An example is
  `whole_test` (`check.rs:7260`), which pushes `Prop` into an
  `if`/`let`/`match`; there are about 33 `undo::attempt`/`transaction`
  sites. A failing first try there now pays for the trials. There is also a
  behaviour change: a first try that used to fail may now succeed by a
  guess and win over the fallback. That is plausible only for Bool-valued
  branches, and both ways give the same proposition there, so it's low
  risk. The verifier's examples run covers it; no action unless timings
  move.
- The fitting trial runs twice (trial, then commit). That's fine.

## 4. Error quality: SHOULD-FIX

- When nothing fits, or several do, it returns `false`. The state has been
  restored, so `first_error` or `cx.mismatch(expected, &ty)` is reported as
  before, with the unknowns shown unsolved. Good.
- But `fits?` (`:1814`) passes on any non-fatal error from a trial:
  `E-INSTANCE-AMBIGUOUS` (two local dictionaries for the trial head in
  scope), `E-INSTANCE-BUDGET`, the `E-INTERNAL` from `solve`, or an error
  from `unify`. That error then replaces the real mismatch. The message is
  about a type the user never wrote (an instance search for `Ordering`
  when they were comparing `Nat`s). Treat a non-fatal error in a trial as
  "doesn't fit" and pass on only `undo::fatal` ones, as
  `interfaces.rs:1506-1513` does.
- NOTE: the commit's `E-INTERNAL "a guessed instance stopped fitting"`
  (`:1825`) is inside `undo::attempt`, which turns non-fatal errors into
  `None`. So that diagnostic is never seen, and the call just returns
  `false`. Either drop the message or make it a `debug_assert!`, so the
  code doesn't suggest a check it doesn't make.

## 5. Is this the right fix? Keep inferring from the expected type; change how

The lane's alternative was to keep `DecEq.decide [Nat.instDecEq] x y` in
types instead of projecting it to `Nat.decEq x y`. That is a reversal of
§5.13's known-instance projection (`x + y` on `Nat` is `Nat.add x y`) and
of §5.10's rule that the term doesn't depend on when the dictionary was
found (`specialise_operators`). Judged by end state, with migration cost
ignored:

- It would make `?d.%decide ?x ?y =?= DecEq.decide inst (a + a) n` a
  first-order match, which solves this and the parameterised cases at once.
- But it changes every operator in every type and goal. `omega`, `ring`
  and the other recognisers read `Nat.add` and `Nat.decEq`, and so do
  lemmas stated with them. Extraction relies on the projected calls to run
  `Text.decEq` and similar natively (see the comment at `check.rs:3273`).
  Kernel conversion would also unfold a projection of a record on every
  operator. It is a language-design change, so it would need a proposal
  and Matt's decision, all for one inference gap. **Not recommended.**

The lane's direction, letting the expected type choose the instance, is
right. Its mechanism, trying every instance and keeping the one that
unifies, is the weak part: it costs O(instances), it misses parameterised
instances, and it decides by trial unification rather than by what the
expected type names. The end state I'd recommend is the
canonical-structures rule known from Coq. When the unifier meets a method
projection of an unsolved dictionary, `?d.%decide ?x ?y`, against a call
whose head constant `F` is the definition some instance gives for that
field (`Nat.decEq`, or `List.decEq` for `List.instDecEq`), it looks up
`(interface, field, F)` in an index built when instances are declared. If
exactly one instance has it, it solves `?d` with that instance (with fresh
unknowns and prerequisite obligations for its parameters) and continues.
This is the inverse of `specialise_operators`, so it is coherent with
§5.10 by construction. It needs no trials, so it has no cost on failure,
and it covers `List`, `Fin n`, `Set k` and the other parameterised types.
It belongs in the unifier, so it is core work for Opus.

**Recommendation:** merge this lane once the MUST-FIX (2b) and the
error-passing SHOULD-FIX (4) are done. It is small, safe once it is
confined to the call's own dictionaries, and the AoC proof reads better
with it. File the canonical-instance lookup as a follow-up that replaces
`unify_guessing_instance`.

## 6. The example and the aoc edit: OK

- `examples/accept/lambda-after-expected-instance.sw`: all four theorems
  state what their names say. `same : a + a = n` with `total : a + b = n`
  gives `a = b` by `omega`, which `differ` refutes. `DecEq.trueOfNe`'s
  signature (`std/Decidable/Decidable.sw:38`, `h: x ≠ y`) matches. `typed`
  and `operands` pin the old paths, and the matching hashes confirm the
  guess builds the same term. Suggest adding the reject or accept case
  from 2b.
- `aoc/.../Day09/Proofs/Window.sw:19`: it goes back to the
  `DecEq.trueOfNe` form that SW-2831 had to give up. The `let`'s stated
  type is unchanged, so `sumsToComplete` means the same thing. Its proof
  term (and so its hash, if a snapshot pins it) changes. The verifier's
  aoc check covers that.

## 7. Other

- SHOULD-FIX: the comment above the comparison chain (`check.rs:3291-3297`)
  explains the first three comparisons but not the new fourth. Add one
  line saying the expected type may choose the one unsolved dictionary's
  instance.
- SHOULD-FIX: this is a new instance-resolution rule. In §5.5, step 3
  says to wait while the type's head is unknown, and this rule now decides
  the head from the expected type. It should be recorded in
  `docs/proposals/interfaces.md` (or in "As built" under postponement) so
  that the spec matches the implementation.
- NOTE: the doc comment on `unify_guessing_instance` says "the one
  dictionary this application made". As written, the code takes any
  unsolved obligation from the application's arguments too (see 2b).
- NOTE: the trials iterate `tables.instances` in table order. The result
  doesn't depend on that order, because all candidates are tried and
  "exactly one" is required. Once 4 is fixed, no trial error can
  short-circuit the loop either.
