# Design note: proofs about named definitions

**Status:** investigation and design, 4 November 2026, for Matt's review.
Ticket SW-1218 (D2331). Nothing in the compiler or std changes. The files
beside this note check with the release build:
[`reads-then.sw`](proofs-about-definitions/reads-then.sw) (option C),
[`opaque-steps.sw`](proofs-about-definitions/opaque-steps.sw) (the probe in
§2.3) and [`bench.py`](proofs-about-definitions/bench.py), which writes the
test parsers of §1. Decisions D2340 to D2345 are in §7.

Evidence labels: **[measured]** means run with the release CLI in this
worktree on 4 November; **[checked]** means read in this repository's source
or in the cited page; **[remembered]** means from memory of the system or
paper, not re-read for this note; **[estimated]** means reasoned, not run.

The machine was loaded while measuring (one check used 43% of a core), so
times in milliseconds vary by 2× between runs. The `steps` column of
`STITCHWORT_TIMINGS=decls` (evaluation steps, `Budget::total_work`) is
deterministic, and the numbers below use it. On this machine about 10
million steps take a second of CPU.

## 0. In brief

- **The problem.** To prove `Parse.Reads line Written` (Day 2), the proof
  has to restate `line`'s body as `Parse.readsBind`'s `j`. With `_` there,
  checking fails. Then the proof unpacks the spec with a staircase of seven
  nested `match`es. The result is 39 lines for an 8-line parser, and it
  breaks when the parser changes.
- **Why `_` fails** (§2). It isn't a hard higher-order problem. Effectful
  code is elaborated to `Effect.bind`, so `readsBind`'s conclusion is
  `Effect.bind (p ()) j`. That is a first-order shape, and `line`'s body,
  unfolded one step, is `Effect.bind (Parse.nat ()) (low => …)`, the same
  shape. The unifier never looks at that one step. It either compares
  `Reads`'s arguments without solving anything, or runs both sides through
  the whole parse handler (`Parse.runFrom`) and compares what comes out.
  There an unknown `?p ()` blocks the handler on one side while the other
  side has computed on, and nothing can be solved. On top of that, each
  nested proof is checked before the expected type has been compared with
  the lemma's conclusion, so inner proofs fix the outer `?j` from their own
  shape first. **[measured]**
- **Why it's slow** (§1). Checking time grows exponentially with the number
  of steps, about 2.6 to 2.8 times per step **[measured]**: 0.2 million
  steps for a 2-step parser, 1.4 million for 4, 9.1 million for 6 and 74
  million for 8. Day 2's `readsLine` takes 20.5 million. Two causes, both
  in the elaborator, not in the parser lemmas:
  1. Comparing two handler runs compares each pair of `Effect.bind` calls by
     their arguments first and, when that fails, by their unfoldings. That
     unfolding makes more `bind` calls to compare the same way. Nothing is
     remembered, so the work triples with each step (5,300, 47,000 and
     422,000 `bind` comparisons for 4, 6 and 8 steps).
  2. A lambda argument whose check fails in place is checked again after
     the lemma's conclusion has been compared with the expected type. Nested
     proofs nest these retries: 16, 64 and 128 re-checks for 4, 6 and 7
     levels, 2ⁿ.
- **It is one case of a broader class** (§4): a lemma whose conclusion is
  about a composite program, applied to a program that has a name. Today
  this shows up only in parser proofs. Std's own `Reads.sw` restates the
  combinator's continuation in 42 of its 43 `readsBind`s, Day 16 restates
  `hexDigit`, Day 2 restates `line`. The rogue's proofs avoid it with a
  predicate that computes (`Effect.Always`).
- **Recommendation** (§6):
  - (A) Teach the unifier to unfold a definition by one step when it is
    compared with a call of a different definition, and to solve unknowns
    from the arguments then, as Lean's lazy delta reduction does.
  - (B) Compare a lemma's conclusion with the expected type before checking
    its proof arguments when the conclusion depends only on arguments
    written `_`.
  - (C) Now, in std, add `Parse.readsThen` and `Parse.readsDone`, a rule
    for sequencing that removes the `match` staircase.

  With A and B, Day 2's proof would be 13 lines with nothing of the
  parser restated, and should check in well under a second **[estimated]**.
  Drop SW-1219's error note: it tells people to copy the body, which is the
  thing to get rid of.

## 1. Measurements

### 1.1 How time grows

`bench.py N copy` writes a parser of N steps, alternating `Parse.nat()` and
`Parse.char '-'` and giving a record of the numbers. It also writes the
proof in `readsLine`'s shape: `readsWeaken` around nested `readsBind`s, the
body copied as the outer `j`, `_` everywhere else. All of these check
**[measured]**:

| steps | evaluation steps | ratio |
|---|---|---|
| 2 | 0.20 M | |
| 3 | 0.51 M | 2.6 |
| 4 | 1.38 M | 2.7 |
| 5 | 2.89 M | 2.1 |
| 6 | 9.05 M | 3.1 |
| 7 | 19.9 M | 2.2 |
| 8 | 73.1 M | 3.7 |
| 16 | killed after 3 min | |

At this rate 16 steps would take about 74 M × 2.7⁸ ≈ 2×10¹¹ steps, hours
**[estimated]**. Day 2's `readsLine` (8 steps, some heavier than `nat`)
takes **20.5 M** steps and 1.2 to 1.9 s of elaboration, in the project and in
file mode alike **[measured]**. (The brief's 4.6 s was on a busier
machine.) The kernel's share is 45 ms.

Two smaller findings from the same runs **[measured]**:

- A record as the parser's result checks, but a pair `(x0, x2)` or a list
  `[x0, x2]` makes the same 4-step proof fail at an inner `readsNat`. That
  is the brittleness Matt felt: whether `_` works depends on details far
  from the step that fails.
- `bench.py N under` (with `_` for `j` too) fails at every N.

### 1.2 Where the time goes

A `sample` of the 8-step check **[measured]** has 993 of 1,000 samples in
one comparison (`check::compare` → `unify::run`), at the top of the proof,
nested about ten deep in `same_arguments` → `unify` → `run`. Counting each
comparison of two calls of the same definition (a temporary trace, not
committed) gives **[measured]**:

| steps | `Effect.bind` pairs equal by arguments | `bind` pairs whose arguments differ (then unfolded) | `Parse.runFrom` pairs that differ |
|---|---|---|---|
| 4 | 3,317 | 1,977 | 150 |
| 6 | 29,794 | 17,275 | 354 |
| 8 | 267,951 | 153,621 | 646 |

The rule is `unify_step`'s first case (`crates/elab/src/unify.rs`). It
compares two calls of the same definition by their arguments. If that fails,
or would solve an unknown (`same_arguments_solving_nothing`), it compares
their unfoldings instead **[checked]**. Unfolding a `bind` whose first
argument is itself a `bind` gives new `bind` calls, which go through the
same rule. Every level pays for the arguments attempt and then for the
unfolding, and no pair is remembered. Only the helper comparison
`same_stuck_trees` has a memo **[checked]**. So the count triples per step.
The `match` staircase and `readsWeaken`'s final rewrite are a small part of
the cost: `readsThen` (option C), which has no staircase, takes 12.9 M for
the same parser.

The second cause shows once the first is out of the way. In `opaque-steps.sw`,
std's reading steps are opaque and every `_` is solved (§2.3), and the same
8-step proof takes 8.1 M steps. A 4-, 6- and 8-step version takes 0.59 M,
2.76 M and 12.1 M, and 16 steps doesn't finish in 170 s **[measured]**.
A temporary trace in `apply_args_postponing` (`crates/elab/src/check.rs`)
counts the lambdas that fail in place and are held for after the expected
type: 16, 64 and 128 for 4, 6 and 7 levels **[measured]**. A lambda whose
domain still has unknowns is checked in place first. If that fails, the
snapshot is restored and the lambda is checked again once the application's
type has been compared with the expected one (postponement.md §5.11)
**[checked]**. Each level of nesting doubles the work below it.

## 2. Why `_` can't be solved for `j`

### 2.1 What the two sides are

`Parse.readsBind`'s conclusion is `Parse.Reads (() => j (p())) (Parse.Then
first next)`. In computation mode, `j (p())` runs its effectful argument
first, so the term is `() => Effect.bind (p ()) (x => j x)` (docs/core.md,
"Computation mode") **[checked]**. `line`'s body is `Effect.bind
(Parse.nat ()) (low => Effect.bind (Parse.char '-') (_ => …))`. Matching
the two needs no higher-order unification: unfold `line ()` one step and
compare `bind` with `bind` argument by argument. `?p` is solved with `() =>
Parse.nat()` (its argument `()` has one value, so `solve` may ignore it) and
`?j` with the continuation, a variable pattern **[checked]**.

SW-1219's example (`examples/reject/not-unfolded-argument.sw` on its
branch) is different. `one(): Nat := Succ (Succ 0)` is pure, so `?j (?p ())`
really is an unknown applied to a non-variable. Solving it would mean
abstracting `p ()` out of `one`'s body, which has many solutions. No
unifier should guess there. The effectful case only looks like it because
both print as `j (p ())`.

### 2.2 What the unifier does instead

These steps come from a temporary trace on 2-step parsers, `t1` to `t9` in
the lane's scratchpad **[measured]**:

1. `readsWeaken line _ _ (readsBind Parse.nat _ _ _ readsNat (low => …))`:
   the outer `readsBind` is checked against `Reads line ?spec`.
2. Its last argument, the lambda, is checked in place before the outer
   conclusion has been compared with that expected type. Inside it, the
   inner `readsBind`'s conclusion `Reads (() => bind (?p₂ ()) ?j₂) …` is
   compared with `Reads (() => ?j low) …`. That solves the outer `?j` from
   the inner proof's shape: `?j := low => bind (?p₂ ()) ?j₂`.
3. The inner `Parse.readsChar '-'`, of type `Reads (() => Parse.char '-')
   …`, is then compared with `Reads ?p₂ ?first₂`. Two calls of `Reads`
   whose arguments match only by solving `?p₂`: by the rule above, they are
   compared by their unfoldings instead. `?p₂ ()` blocks the handler run on
   one side while the other has computed into `Parse.runFrom.%match1 …`.
   That fails, and is the error SW-1219 saw, at the inner argument.
4. The lambda is held, the snapshot restored, and the outer conclusion
   compared with `Reads line ?spec`. The expected type reaches the
   application unfolded. `check_inner` forces it, and `Reads`'s body is a
   function type, so it is a `Value::Pi`, not the call `Reads line ?spec`
   **[measured]**. So the comparison is between two handler runs again.
   With `p` given (`Parse.nat`), the two runs step in lock step through
   `nat`'s `span` and meet at `bind (k y) ?j` against `bind (k y) (low =>
   …)`, which solves `?j`. With `p` as `_`, the run is stuck on `?p ()` at
   once, and the comparison fails.
5. The lambda is checked again with `?j` known. Its inner `readsBind` meets
   steps 3 and 4 one level down. Whether its own `_`s are solved depends on
   whether the handler runs on both sides happen to stay in step: on
   whether the calls in the solution of `?j` are still folded as in the
   source. With the body copied as `j` they are. With `?j` solved from
   `line`'s unfolding they aren't, and the final comparison fails
   (`runFrom.%match1 …` against `runPure (foldComp … (bind (?p₂ ()) …))`).
   I didn't find the exact point where the folding is lost. That last
   detail is **[inferred]** from the trace, not pinned down.

So the copied body works because it hands every level a parser term with its
calls folded. The `_` fails because nothing ever compares `line` with
`bind (?p ()) ?j` one unfolding apart.

### 2.3 Two probes

- **Opaque steps** (`opaque-steps.sw`) **[measured]**. With opaque copies of
  `nat`, `char`, `satisfy`, `text` and `takeWhile1`, `line()` computes only
  as far as `Effect.bind (natO ()) (low => …)`. The opaque call stops it.
  That is exactly the shape the lemma wants, and Day 2's proof checks with
  `_` for every `p` and `j` (8.1 M steps). This shows that one step of
  unfolding is all that's missing. It is a probe, not a fix: it works only
  when every step is an opaque std leaf, not for a user's parser built from
  their own definitions.
- **Solving from arguments everywhere** **[measured]**. A one-line change
  lets `same_arguments` keep what it solves on every comparison, not only
  under `unify_solving_arguments`. Then `bench.py 8 under` (all `_`)
  checks, but at 47 M steps. Two std proofs stop checking: `Reads.sw:627`
  (`readsPickBy`'s `rfl`) and `Reads.sw:1712`. This is the hazard the
  folded-calls note warns of (§7, stage 2: solving from arguments can pick
  a different solution than the unfoldings would). Any such rule has to be
  aimed narrowly.

## 3. How other systems handle this

| System | Proofs about a named definition | Monadic or parser code |
|---|---|---|
| Lean 4 | `isDefEq` unfolds lazily: when two applications of different constants are compared, it unfolds the one with the greater definitional height by one step and compares again, arguments first ([type checking in Lean 4, "Definitional equality"](https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html)) **[checked]**. Higher-order pattern unification (Miller patterns), with a first-order approximation for `?f a =?= g b` that isn't a pattern **[remembered]**. Caches for defeq results within a check **[remembered]**. Explicit control by `unfold f`, `simp only [f]`, `show T`, `change T`, `delta` **[remembered]**. | `Std.Do` gives a monad a weakest-precondition interpretation (`wp⟦x⟧ Q`), and the `mvcgen` tactic turns a goal about a `do` block into pure verification conditions, with loop invariants from the user ([Lean reference, "The mvcgen tactic"](https://lean-lang.org/doc/reference/4.25.0/The--mvcgen--tactic/); [`Std.Do.WP`](https://lean-lang.org/doc/api/Std/Do/WP/Basic.html)) **[checked]**. No verified parser library in core that I know of **[remembered]**. |
| Rocq | `unfold f`, `change T`, `cbv delta [f]`; Ssreflect `rewrite /f`. `apply` unifies up to delta, with heuristics that can be slow or fail. Users unfold first and then `apply` the bind rule **[remembered]**. | Iris: `wp_bind` with an evaluation-context search, then rules per step **[remembered]**. Verified parsers: Narcissus derives encoder and decoder from a format, with proofs by construction (Delaware et al., ICFP 2019). RockSalt's x86 decoder is defined from a grammar with a denotation (Morrisett et al., PLDI 2012). Vermillion and CoStar are verified parser generators **[remembered]**. |
| Agda | Definitions unfold in conversion. Pattern unification. `rewrite` and `with` for the rest **[remembered]**. | Danielsson's *Total Parser Combinators* (ICFP 2010) indexes each parser by its language, so its semantics is part of its type and correctness is by construction. agdarsec guarantees totality only **[remembered]**, and total-parsers.md §2 checked both. |
| Idris 2 | Unification unfolds definitions, with `%inline` and `[reducible]`-style control. Elaborator reflection for custom tactics **[remembered]**. | `Text.Parser`'s `Grammar` is indexed by whether it consumes. No correctness proofs (total-parsers.md §2) **[checked there]**. |
| F\* | Specs live in types: an effectful function's type carries its weakest precondition (Dijkstra monads), and the checker computes the verification conditions of a body from those of its calls. `reify` exposes a computation to extrinsic proofs **[remembered]**; computation-values.md §4 **[checked there]**. | EverParse/LowParse: parser combinators whose types state that they parse and serialise a format, so every parser built from them comes with its proof **[remembered]**. |
| Dafny | A method's `requires` and `ensures` are checked at each call: its body is never restated, and functions unfold to a fuel limit (`{:fuel}`, `reveal` for opaque ones) **[remembered]**. | Parsers are verified as ordinary methods against their postconditions **[remembered]**. |

What the survey shows:

1. **Nobody restates a body.** The systems either unfold on demand inside
   unification (Lean, Rocq, Agda, Idris) or attach the spec to the
   definition, so a caller uses the spec and never looks inside (F\*,
   Dafny, EverParse, Total Parser Combinators).
2. **"Unfold one step, compare arguments, else unfold more" is the standard
   rule**, and Lean's lazy delta orders it by definitional height. Its costs
   are known too: exponential defeq checks, met with caches and transparency
   settings. That matches §1.2.
3. **Program verification frameworks generate the per-step obligations by
   machine** (`mvcgen`, Iris's `wp_*` tactics, F\*'s WP computation). The
   user writes only what doesn't follow from the code: invariants, the final
   implication.

## 4. Is it a broader class?

The class: **a lemma whose conclusion is about a composite program
(`() => j (p ())`, `f ∘ g`, `bind p k`), used for a program that has a
name**. Checking has to see through the name to the body's structure, by
one step of unfolding.

Where it shows up in the repo **[checked]**:

- **Std's `Parse/Reads.sw`:** 42 of its 43 `readsBind` uses pass `p` and
  `j` explicitly, restating the combinator's own code. For example, line 381
  restates `satisfy`'s `match found with | Some char => char | None =>
  Parse.expected what`, and line 433 restates `takeWhile1`'s.
- **AoC:** 2020 Day 2's `readsLine` (8 lines of body) and 2021 Day 16's
  `readsHexDigit` (`hexDigit`'s `satisfy` call and its `need`). 2021 Day 10
  needs none: its parser is one combinator call (`Parse.many token`), which
  the combinator's lemma matches by name. So the copying comes when a proof
  steps through a definition's *body*, not when the definition is a single
  call.
- **The rogue avoids it** by computing. `Effect.Always property c` is
  defined by recursion on the computation tree, so `Always P (generateLevel
  d)` computes to one function argument per roll, and
  `generatedLaidOut` takes 34 named arguments and checks in 0.12 s
  (games/rogue/PROOFS.md). `generateLevel` is opaque, and the theorem says
  `unfolding generateLevel`. It also uses `Effect.alwaysBind` where the
  computation is stuck.
- **Pure code doesn't meet it the same way.** `rfl` and `cases` compute,
  and `f.eqN` and `f.unfold` rewrite (proving-guide §3). A goal stuck on
  `f x` is handled by computing, not by matching a lemma's shape against
  `f`'s body.

So the class is general, but today only `Parse.Reads` and any future
predicate of the same kind meet it: a spec of effectful code stated through
its handler, with one lemma per combinator. `Fail` and `State` lemma
families would be next. The cause (no one-step unfolding when a call is
compared with a call of another definition) is in the unifier, so the fix
is general. The extra elaboration cost (the retry of nested lambdas, the
unremembered comparisons) is general too. It hits hardest here because a
parser proof nests one lambda per step and compares whole handler runs.

## 5. Options

Each option: the problem it removes, the change, what it should do, cost
and risk.

**A. One step of unfolding in unification (lazy delta).** When a call of
`f` is compared with a call of a different definition `g` (here `line ()`
against `Effect.bind (?p ()) ?j`), unfold the later-defined of the two by
one step, to its body with the arguments put in and its own calls still
folded. Then compare again, arguments first, and keep what that solves.
Only after that fails, compare their full unfoldings as now.

- *What it does:* every `_` in `readsLine` is solved, with nothing restated.
  The probe in §2.3 shows this one step is all that's missing
  **[measured]**. It also makes std's 42 restatements unnecessary. They can
  then go, a sweep.
- *Cost:* medium. `unify_step` gets a one-step unfolding for `Value::Call`:
  evaluating the definition's body on the arguments with gluing on already
  keeps inner calls folded **[inferred]**. It needs a height or definition
  order to pick the side, and the solving-from-arguments rule (§2.3) applied
  only in this new path.
- *Risk:* medium to high. It changes which solutions unification picks
  across every program. The global variant broke two std proofs
  **[measured]**. It needs the merge tier and a daily run, and a fuel or
  depth limit like Lean's. Lean's experience says it can also be slow
  without caches.

**B. Compare the conclusion first when the conclusion depends only on `_`.**
`propagate` already compares an application's result type with the
expected type before its arguments, unless the result type depends on
arguments written in the call (`written_result`). `readsBind`'s conclusion
depends on `p`, `j`, `first` and `next`, which are written `_`. Treat a
`_` there as the unknown it will be anyway, so the conclusion is compared
first and the proof arguments are checked once, against known types.

- *What it does:* removes the 2ⁿ retry. Each nested proof is checked once,
  against a goal that already knows its parser, and the inner proofs can no
  longer fix the outer `?j` from their own shape (§2.2, step 2). Estimated
  to take `opaque-steps.sw`'s 8.1 M steps to well under 1 M, and 16 steps
  from hours to under a second **[estimated]**.
- *Cost:* small to medium (`check.rs`: `written_result`, `propagate`).
- *Risk:* medium. It changes elaboration order where `_` arguments sit
  before proofs. Messages move. The merge tier would show the reach.

**C. A sequencing rule whose spec flows from the statement: `Parse.readsThen`
and `Parse.readsDone`** (std only). Written and checked in `reads-then.sw`
**[measured]**:

```
theorem readsThen (p: () → {Parse} a) (j: a → {Parse} b) (first: List Char → a → Prop) (spec: List Char → b → Prop)
    (readsFirst: Parse.Reads p first)
    (rest: (firstRead: List Char) → (v: a) → first firstRead v → Parse.Reads (() => j v) (read w => spec (firstRead ++ read) w)):
    Parse.Reads (() => j (p())) spec
```

- *What it does:* the spec comes from the theorem's statement, so each
  step's facts arrive as named parameters (`lowRead low lowDigits =>`,
  `dashRead u1 dash =>`), and the last step states the obligation once.
  Day 2's proof loses its `match` staircase and `readsWeaken`: 13 lines
  instead of 39, 12.9 M steps instead of 20.5 M **[measured]**. Today
  each step still names its parser (`Parse.nat`, `() => Parse.char '-'`).
  That is one short restatement per step, not the whole body. With A, those
  become `_` too.
- *Cost:* small: two lemmas of about 15 lines, already proved. Day 2 and
  Day 16 move to it.
- *Risk:* low. It adds lemmas and changes nothing else.

**D. An explicit "unfold" step in proofs**, as Lean's `unfold`/`show` and
Rocq's `change` do. Something like `unfold line in e`: check `e` against
the expected type with `line` replaced by its one-step body.

- *What it does:* the `_`s match by arguments under the visible body,
  explicitly and predictably. But it is one more construct to learn, and a
  proof through a parser built from the user's own definitions needs one
  `unfold` per definition.
- *Cost:* small to medium (a proof form beside `rewrite`).
- *Risk:* low, since it only affects proofs that use it.
- A is the same step done automatically. D is the fallback if A proves too
  risky.

**E. Make std's leaf parsers opaque** (the §2.3 probe, as a change).

- *What it does:* solves the `_`s today for parsers built only from std's
  leaves.
- *Cost:* small (each leaf's `Reads` lemma gets `unfolding`).
- *Risk:* it works only for std leaves, and it hides computation from
  every proof that runs a parser on a known string. Not recommended.

**F. A spec that computes, as `Effect.Always` does.** A `Parse.ReadsTree
spec c` defined by recursion on the computation, with one hypothesis per
read: span, next, literal.

- *What it does:* proofs like the rogue's, no unification needed.
- *Cost:* high. `mark` and `reset` need a model of positions, and the
  soundness lemma is a tree induction like `runFromThenOkTree`.
- *Risk:* it exposes how `nat` is built (`span`, then a `match` on the
  digits), not its spec, unless the steps are opaque. Not recommended.

**G. Parsers from a grammar** (Narcissus, Total Parser Combinators,
EverParse): the parser and its spec come from one description.

- *What it does:* no extrinsic parser proofs at all.
- *Cost:* a redesign of `Std.Parse`'s surface. total-parsers.md (D1710:
  not now) covers the neighbouring question.
- Out of scope.

**H. The completeness direction** ("well-formed text parses"). `Reads` is
soundness only (Reads.sw's header). The converse,
`Written line entry → line parses to entry`, would need its own rules per
combinator, a `Parses` predicate with a sequencing rule shaped like C.

- *Cost:* a std lane, larger than C. The rules for `many` and `takeWhile`
  need maximal munch: what follows mustn't pass.
- It meets the same unification problem, so it should come after A and B.
- Worth its own note when an AoC proof needs it.

**SW-1219** (branch `lane/SW-1219`, commit `be42733c`): a note on type
mismatches that tells the reader to copy the definition's body. It fires at
the inner argument, names `Reads` rather than `line`, and fires on a genuine
error too (`unify-bool-argument.snap`'s note names `double`) **[checked]**.
Its example is the pure case (§2.1), where no unifier should guess. Drop
it. Its example file can be the regression test for A's lane, as an
`accept` example once the effectful version checks, and a `reject` example
for the pure one, with a note that names the definition and doesn't advise
copying.

**The 4.6 s.** B removes the doubling and A removes the handler-run
comparisons (they become argument comparisons). Together they should make
`readsLine` linear in its steps **[estimated]**. A memo of call pairs found
equal or different within one outer comparison, like `same_stuck_trees`'s,
would make even the old path polynomial **[estimated]**. Lean keeps such
caches. That is a smaller, independent fix for the first cause in §1.2,
and it helps every proof that compares large unfolded computations.

## 6. Recommendation

1. **Now:** C. Add `Parse.readsThen` and `Parse.readsDone` to std, and move
   Day 2 and Day 16 to them. It is small and safe, and it removes the
   staircase whatever is decided about A.
2. **Next:** B, then A, each in its own lane: Opus, with an Opus review,
   since they change what elaborates. Measure with `bench.py` before and
   after. B first, because it is smaller, and because it makes A's effect
   readable: without B, A still pays the 2ⁿ retry. After A, sweep std's
   `Reads.sw` to `_`.
3. **If A's merge-tier run shows too much churn:** D instead, the explicit
   step.
4. **Drop SW-1219.**
5. **Later:** the completeness direction (H), as its own note.

## 7. Decisions for Matt

**D2340: add a sequencing rule to std now?**
- The problem: every parser proof ends in a staircase of `match … Witness …
  Both …`, 20 of Day 2's 39 lines.
- The change: two std lemmas, `Parse.readsThen` and `Parse.readsDone`
  (option C, already proved), with Day 2 and Day 16 moved to them.
- What it does: each step's facts become named parameters, and the
  staircase goes. Day 2's proof is 13 lines instead of 39, and its check
  takes 12.9 M steps instead of 20.5 M **[measured]**. Each step still names its
  parser call until D2341.
- **[rec: yes]** A small lane (Sonnet; Opus review, since it is a proof).

**D2341: let checking see one step into a definition (lazy delta)?**
- The problem: `_` can't be solved for the parser in `readsBind`, so proofs
  copy the parser's body.
- The change: when the unifier compares calls of two different definitions,
  unfold the later one by one step and compare by arguments, keeping what
  that solves, before comparing full unfoldings. This is what Lean does
  (option A).
- What it does: every `_` in parser proofs is solved, with nothing restated
  (shown by the opaque probe **[measured]**). Std's 42 restatements can go.
- The risk: it changes solutions program-wide. The naive version broke 2
  std proofs **[measured]**.
- **[rec: yes, after D2342]** Opus lane, merge tier plus a daily run.

**D2342: compare a lemma's conclusion first when it depends only on `_`?**
- The problem: nested proofs are checked twice per level, so parser proofs
  slow down 2× per step **[measured]**.
- The change: in `propagate`, treat `_` arguments as unknowns, so the
  conclusion is compared with the goal before the proofs are checked
  (option B).
- What it does: each nested proof is checked once. An 8-step proof should go
  from 8 to 74 M steps to under 1 M, and 16 steps from hours to under a
  second **[estimated]**.
- **[rec: yes, first]** Opus lane.

**D2343: remember compared call pairs within one comparison?**
- The problem: comparing two unfolded computations redoes the same `bind`
  comparisons, so the work triples per step **[measured]**.
- The change: a memo of call pairs found equal or different for the
  duration of one outer comparison, as `same_stuck_trees` already keeps.
- What it does: stops the exponential growth on that path. It helps
  wherever large unfoldings are compared, including after D2341.
- **[rec: yes, but after D2342 and D2341, and only if a profile still shows
  that path]**

**D2344: SW-1219's error note?**
- The problem: the note tells people to copy the body, fires on unrelated
  errors and names `Reads`, not `line`.
- The change: drop the branch, and keep its example as a test for D2341's
  lane.
- **[rec: drop]**

**D2345: the completeness direction ("well-formed text parses")?**
- The problem: `Reads` proves only that what a parser accepts is
  well-formed, not that it accepts everything well-formed.
- The change: a separate design note for `Parses` rules, after D2341.
- **[rec: backlog, not now]**

## 8. What I'm unsure of

- Where exactly, in §2.2 step 5, the folding of `?j`'s solution is lost.
  The trace shows the failing pair, not the step that unfolded it.
- The estimates for B. I didn't prototype it. The 2ⁿ count is measured,
  but how much of the remaining cost is the comparisons that A replaces is
  inferred.
- Whether A's one-step unfolding is cheap to build on Stitchwort's glued
  values (`Value::Call` keeps a whole-head-normal-form unfolding, not a
  one-step one). The probe suggests the shape is right, but not how much
  the unifier changes.
- The survey's [remembered] rows: I checked only Lean's lazy delta and
  `mvcgen` pages for this note.
