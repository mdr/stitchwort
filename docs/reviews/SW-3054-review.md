# SW-3054 review: derived `DecEq` decides through a named `T.%decide`

Branch `lane/SW-3054`, commit 0ba103f9e. Independent Opus review, read
only (no builds or tests run), 13 Nov 2026.

## Verdict

Nothing is wrong. The generated declaration is well typed and elaborated
in the right place. The behaviour it relies on ("kept folded") comes from
two documented rules, not from luck. Readings, JS extraction, pruning and
printing all still fit the new shape. Three findings below are worth
acting on. None blocks the merge.

## How the fix works

These are the two rules the fix depends on, so the findings can refer to
them.

1. **The known-instance projection** (`interfaces.rs:1588-1594`, interfaces
   §5.13, also `specialise_operators` at `interfaces.rs:1940+` and
   `method_call`). `x == y` becomes `<field> x y` only when the instance's
   `decide` field is a `Value::Neutral(Head::Def(_), _)`, meaning a
   definition, applied or not. Before this change the field was a lambda.
   Derived types therefore went through `DecEq.decide [T] ?d x y`. Once the
   dictionary was projected, that beta-reduced to
   `Decidable.holds {holds = T.%same x y, …}`. That call has a constructor
   argument, so `matches_at_once` was true, and it was shown and stored as
   `T.%same x y`. With `{ decide = T.%decide }` the projection gives
   `Decidable.holds [x = y] (T.%decide x y)`, the same shape as
   `Nat.decEq`.
2. **Folded calls, stage 3** (`value.rs:936-974`, `matches_at_once`). A
   glued call is written as its unfolding only when its case tree starts
   with a case on an argument that is already a constructor. `T.%decide`'s
   body is a record literal, with no case. So the `Decidable.holds` call
   keeps its decision argument folded. `unify.rs:2365-2440`
   (`same_field_calls`) then unifies `Decidable.holds [?x = ?y] (…)`
   against `Decidable.holds [r = s] (T.%decide r s)` through the
   proposition parameter, and this is what lets `DecEq.sound h` find `x`
   and `y`. It is the same rule that serves `Nat.decEq`, written for
   exactly this case ("Without it, `DecEq.sound e` … can't find `m` and
   `n`").

When both sides are constructors, `T.%same` still computes to `True` or
`False` (`readings-derived-eq.sw`'s `computes` test). When it is stuck,
including a record compared with a record literal (an `&&` chain on
neutrals), the call stays folded. So `match h: r == s` gives
`h : (r == s) = True`, the shape the user wrote.

## Checked and found right

- **Type of the generated declaration** (`derive.rs:1420-1431`). It is
  `with_params(Pi (%r %s : this) → Std.Decidable (%r = %s), true)`, the
  same `with_params(…, true)` that `T.%same`, `%sameSound` and
  `%sameComplete` use. So it has the same implicit type parameters,
  value-parameter heads and `[auto decEq…]` prerequisites, one per
  parameter that is a type and that fields use. Its equation binds only
  `%r %s`, as theirs do. Inside the body, `T.%same %r %s` and its proofs
  find their dictionaries among `%decide`'s own auto arguments, which is
  where the old instance lambda found them. The instance's type is
  unchanged.
- **Order** (`derive.rs:294-308`). The order is differs, tests, proofs,
  `%decide`, instance, readings. `%decide` mentions the tests and the
  proofs, and the instance mentions `%decide`. Each step runs through
  `and_then`, so if the proofs fail, `%decide` and the instance are skipped
  and the failure goes to `no_eq`, as before. If `%decide` checks and the
  instance doesn't, a stray `T.%decide` is left in the environment. That
  is harmless and already the case for `%same`.
- **Readings from SW-3044** (`derive.rs:1334-1393`). They are stated on
  `T.%same r s` and build their own inline decision annotation. They never
  mention the instance or `%decide`, so their statements and proofs don't
  change, and their hashes are unchanged in every updated snapshot. The reader
  (`reading.rs:764-806`) starts from `Decidable.holds [r = s]
  (T.%decide r s)`. Holds has no reading, and the decision computes to a
  record, so `stuck_decision` gives `None`. The reader then unfolds one
  step to `T.%same r s` and finds `%sameReads` there. That is the path it
  took before through the beta-reduced record. `readings-derived-eq.sw`
  still elaborates on the branch (its snapshot holds every theorem), which
  bears this out for a sum type, a record and a parameterised type.
- **Mutual, nested and parameterised types.** Mutual types are never
  derived (`derive.rs:9`). A nested type's containers (`T.%m1%…`) get
  their own `same` and proofs but no decision or instance. Only member 0
  gets `%decide`, so one is generated per type, never several. Recursive
  and container fields call `T.%same` and `T.%m1%same` directly, not `==`,
  so their terms don't change.
- **Name clashes.** No other deriver generates `{T}.%decide`.
  derive_ord's, derive_finite's, derive_show's and derive_decide's names
  are distinct. The only other `%decide` is the interface projection
  `Std.DecEq.%decide`, which `pretty.rs:2137-2153` matches by the method's
  full path, not its last segment. `reading.rs:776-780` leaves `%`-names
  out of the leaf note.
- **Printing.** `pretty.rs:1958-1980` (`decided_equation`) asks
  `goals.rs:342` for `eq_decision`. That goes through `decide_eq_of` and
  now returns `T.%decide`, so `Decidable.holds (T.%decide a b)` prints as
  `a == b`. Without a scope, `operation()` prints any
  `Decidable.holds [a = b] _` as `a == b`.
- **JS.** The forwarder analysis (`js/src/lib.rs:3160+`) sees `T.%decide`
  as its test, because a decision is stored as its `Bool`. The renamed
  assertions in `extract.rs:1871-1879` show a microtype's `%decide`
  aliasing the field's `decEq`. That also fixes SW-3053, whose test named
  the old `%decEq`.
- **rt simplifier.** `T.%decide` is a small non-recursive global, so
  `rt/opt.rs` inlines it.
- **Pruning.** `deceq-instance-after-pruning` only changes hashes, since
  dependencies come from terms. Nothing in pruning, hover or the check
  cache special-cases `%instDecEq`'s field shape or `%same`. The one
  `.%same` elsewhere (`decreasing/plain.rs:957`) is a decreasing
  function's twin and unrelated. `records.rs:186` checks only the
  instance's type. Check-cache keys include the compiler fingerprint
  (`driver.rs:1190-1255`), so stale cached terms can't mix with new ones.
- **Kernel.** The kernel doesn't glue, and it sees an ordinary
  non-recursive definition and an instance whose field is a constant.
  Definitional equality `(T.%decide r s).holds ≡ T.%same r s` is plain
  delta and projection. No kernel rule changes, so `docs/core.md` needs no
  update.
- **New example** `examples/accept/deceq-sound-in-match.sw`. I read the
  three theorems statement by statement, and each says what its name and
  comment claim. `notOnMonster` is `(player == monster.position) = False`
  under the stated hypotheses. `foundThere` is `found.position = position`
  from `monsterAt … = Some found`. `lookupBuilt` is lookup in a table
  built by `map`. The missing `[]` arms are impossible by computation
  (`None = Some _`, `cave ∈ []`). They cover a two-field record nested in
  a record (`Position` in `Monster`), a microtype (`Cave`), `rewrite` with
  `DecEq.sound`, and `DecEq.refl` inside `rewrite … at`.

## Findings

### Medium

**M1. The regression example covers only records. The other derived
shapes take different paths and are untested for this bug**
(`examples/accept/deceq-sound-in-match.sw`).

Before the fix, a sum type was broken the same way: the beta-reduced
record unfolded `r == s` to `T.%same r s`, stuck on a case. A
parameterised type also goes through the known-instance projection in a
different way. `T.%instDecEq [a] [d]` unfolds to a record whose field is
the partial application `T.%decide a d`, and `DecEq.sound` must then find
`[auto decEq: DecEq (Box a)]` by search after `same_field_calls` solves
`?x`, `?y` and the type.

Failure scenario: a later change to how a prerequisite instance unfolds
in `decide_eq_of` (`interfaces.rs:1587-1588`) puts parameterised types
back on the `DecEq.decide [T] ?d` path. `match h: c == d` on `Box a` then
gives `h` the `T.%same` form again, and `DecEq.sound h` fails. No example
would catch it: `readings-derived-eq.sw` uses `.read` on a parameter, not
`match h:` with `DecEq.sound`.

Recommendation: add two short theorems to the same example, under the
orchestrator's own judgement:

- a sum type: `type Dir = | North | Turn (by: Nat)`, with
  `match h: c == d with | True => DecEq.sound h`;
- a parameterised one: `Box (a: Type)` with `[auto decEq: DecEq a]`.

Optionally add a third case with `h.read` inside the `True` arm.

**M2. The comments name the wrong reason for "kept folded", and the rule
that actually holds it can be broken without anything failing**
(`derive.rs:1401-1409`, also the module doc at `derive.rs:73-76`).

The comment says the call stays folded because `%decide` is "a definition
of its own". Two things actually hold it:

- the instance field is a bare definition, which the known-instance
  projection requires: `Value::Neutral(Head::Def)`;
- `T.%decide`'s body does not start with a case, so `matches_at_once` is
  false (`value.rs:959`).

Failure scenario: someone later writes `%decide` with record patterns, or
generates it as a case tree on `%r` to share work with `%same`.
`Decidable.holds (T.%decide r s)` then "matches at once" whenever `r` is a
constructor or an eta record, and it would be written as its unfolding
again. With record eta, `T.%same`'s own case takes its branch on a
neutral, and `matches_at_once` on the `Decidable.holds` call looks through
calls that match at once. The bug comes back for literals and possibly
for records. That person would find nothing in the comment telling them
not to.

Suggest one sentence: "`T.%decide` must stay a single record, with no
case on `%r` or `%s`: a call that matches at once is written as its
unfolding (folded-calls stage 3), which is the bug this avoids."

The module-doc sentence at `derive.rs:73-77` also no longer parses after
the edit ("`r == s` is `(T.%decide r s).holds`, so `T.%same r s`, which on
two constructors computes …, the later ones run only once …"). Reword it,
for example: "`r == s` is `(T.%decide r s).holds`, whose test is
`T.%same r s`: on two constructors, their fields' tests joined by `&&`, …"

### Low

**L1. The fix holds only with glued elaboration.** Both
`same_field_calls` (`unify.rs:2381-2385`, `!g.machine.glue.get()`) and the
folded `Decidable.holds` call need gluing. Under `STITCHWORT_GLUE=0`
(`state/options.rs:108`) the new example would fail, as `Nat`'s
`DecEq.sound` uses already do. This was there before the change and the
switch exists only for comparison. Note it in case a glue-off sweep is
ever run over `examples/accept`.

**L2. Snapshots the lane left stale on purpose.** The ticket says every
other example with a derived `DecEq` gains a `%decide` line in its
`hash_stability` snapshot, and those are left for the verifier. The
verifier for this batch will see a wave of `hash_stability` failures that
are expected churn, not regressions. The orchestrator should regenerate
them as part of the merge (as with any hash churn, D2303) rather than read
them as breakage. Other lanes in the same batch with real hash changes
would be hidden in that churn, so it may be cleaner to merge this one on
its own.

**L3. Process.** The ticket records "whole aoc 'checked 291 namespaces'"
and a rogue check. A whole-project `aoc/` check is outside a lane's test
budget (CLAUDE.md, D3517) unless Matt allowed it for this run; the
ticket's "Fix sw 3054 tonight" doesn't say. I'm noting it for the
orchestrator, not counting it against the code.

## Does derive_decide.rs (SW-3038) have the same exposure?

No. A derived `Decidable` record's decision is the instance itself,
`T.%instDecidable p…`, a named global that is folded by name as a
dictionary. Its fields are already applied definitions
(`holds = T.%holds n`, `derive_decide.rs:471-500`), never a lambda. So
`if h: Ok n` or `Decidable.holds [Ok n] (Ok.%instDecidable n)` keeps the
decision as a folded call. `matches_at_once` doesn't unfold a folded
instance, and its readings are filed on `T.%holds`, which the reader
reaches by unfolding one step, as above.

There is no `==`-style projection there, so nothing produces a lambda to
beta-reduce. The one thing in common is M2's invariant: if
`T.%instDecidable` were ever generated with a case at its top, the same
"written as its unfolding" rule would apply. Nothing generates it that
way today.

## Findings worth filing

- M1: add sum-type and parameterised cases to `deceq-sound-in-match.sw`
  (small, Sonnet or DeepSeek).
- M2: comment fixes in `derive.rs` (one-line fixups, or fold into M1's
  lane).
