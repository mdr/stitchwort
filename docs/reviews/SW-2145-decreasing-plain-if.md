# SW-2145: review of merge `75c41e620` (SW-2029, a plain `if` in a `decreasing` body)

A review of stage 1 of `docs/proposals/decreasing-with-hypothesis.md`, by
reading only (no builds or runs). Read: `git show 75c41e620 -m
--first-parent`, all of `crates/elab/src/decreasing/plain.rs`, the
changed parts of `decreasing.rs` (`decreasing_step`, `decreasing_unfold`,
the pipeline around `plain_view`), `check.rs` (`check_if_in`,
`unused_proof_if`, `kept_if`, `tagged_if`), `logic.rs` (`tag_plain`,
`settle_tagged`), `lib.rs` (`finish`), `lift.rs` (where helpers are
settled), `equations.rs` (`decreasing_equations`, on-demand equations,
D2186's guard reading), `bind.rs` (`into_bool`, `comparison`), the cache's
`admit_replayed` ordering, the two new core lemmas, the comparison
decisions in `Decidable.sw`, `Int.sw` and `Float.sw`, the new example and
the snapshots, and the AoC and std `decreasing` definitions whose proofs
rewrite with `.unfold`. The 1 Nov codebase review
(`docs/research/rust-codebase-review.md`) has no findings in this area.

## Summary

The change is sound: nothing it generates is trusted. `f.unfold`'s
statement and `f.%plain.%same`'s are built from the plan, not from the
proof, and the kernel checks both proofs. `f.%plain` is an ordinary
definition, so the only way it could be "wrong" is by not being the
program as written. The example's `*Unfolds` theorems check that by
conversion, so they would fail if it weren't. The two lemmas are used
with their arguments in the right order. `Bool.elimDecTrueIf` fits every
comparison decision, because each is literally `Bool.decTrue (…)`.

The weak point is the one the brief suspected. The marking pass (`mark`)
and the proof builder (`proof`/`part`/`hole_proof`) are two separate
recursions that have to agree, and they don't quite. `mark` never looks at
a `Decidable.elim`'s proposition and type arguments, or at a kept `if`'s
own tag. So an `if` nested inside another `if`'s condition keeps a tag
that `post` then turns plain while the proof or the decision still has it
decided, and the kernel refuses `%same` or `%plain`. Because that refusal
is a hard error (the design note promised a fallback), a correct program
stops compiling. The shapes are unusual (F1 has two examples), the fix is
small, and an invariant check would catch any future drift. The rest is
low-severity robustness, and tests that don't cover one of the two new
lemmas.

**Top five recommendations**

1. Make `mark` strip tags from an `elim`'s or `ite`'s type arguments and
   from a kept `if`'s tag, and check after marking that exactly `count`
   tags remain (F1, F7). S.
2. Decide what a generator failure in `plain_view` does: fall back to the
   old `f.unfold` with a warning, as the design note's §6 said, or stay an
   error (D3100, F2).
3. Add tests for `Decidable.elimIf` (an unnamed `if a = b` or `if x ∈ s`),
   a call in the `else` of a `Bool` `if`, a lexicographic measure, an
   `if` under a lambda staying `if _:`, and F1's shapes (F9). S to M.
4. Have `Lemmas::new` return "no view" when `Decidable.elimIf` or
   `Bool.elimDecTrueIf` isn't loaded, instead of an internal error (F4). S.
5. Run the AoC checks for the eight days whose proofs rewrite with
   `.unfold`, which no lane ran (F10, D3101).

## Findings

| # | Severity | Confidence | Where | What | Size |
|---|---|---|---|---|---|
| F1 | medium | medium | `plain.rs:367-404`, `287-309` | tags left in an `elim`'s `p`/`a` arguments and in a kept tag `b`: the kernel refuses `%same` or `%plain` | S |
| F2 | medium | high | `decreasing.rs:1083-1088` | a generator failure fails the whole definition; the design note's fallback isn't there | S (after D3100) |
| F3 | medium | medium | `check.rs:5125-5134`, `plain.rs:426-458` | every `Bool` `if` in a `decreasing` body now carries its fact; under a lambda, a condition or an inner `match`, `f.unfold` can change from plain `if` to `if _:` | S (test, docs) |
| F9 | medium | high | `examples/accept/decreasing-plain-if.sw` | `Decidable.elimIf`, the bound-operand path, lex measures, `else` calls and the `if _:` fallbacks are untested | S-M |
| F10 | medium | medium | AoC proofs using `.unfold` | the wider reach was never checked against the AoC proofs | S (a run) |
| F4 | low | high | `plain.rs:253-280` | missing lemmas are an internal error, not "no view" | S |
| F5 | low | low | `decreasing.rs:1411-1419` | `keep_plain` covers all of `finish`, not only its final settle | S |
| F6 | low | high | `equations.rs:2050-2065`, `decreasing.rs:1777-1800` | `%unfoldStep` chosen by `DefId` order; it isn't in `def_items` | S |
| F7 | low | high | `plain.rs` as a whole | `mark` and the proof builder agree only by comment; the J chain and the child map are copies | S now, M later |
| F8 | low | high | `check.rs:5200-5210`, `07-recursion.md` | stale `Unused::Bool` doc; the guide says "false in the `else`" | S |

## Details

### F1. Tags that `mark` never looks at reach the proof (medium, medium confidence)

`Lemmas::mark`'s `elim` case (`plain.rs:367-404`) marks the decision and
the two branches but copies `args[0]` (the proposition `p`) and `args[1]`
(the result type `a`) unchanged. It also keeps the tag `b` as found,
without marking it. The `ite` case does the same with its type argument.
`pre` and `post` use `rewrite_up`, which rewrites every tagged `elim`
anywhere in the term, these arguments included. So a tagged `if` nested
inside them behaves inconsistently. In the decision, `mark` has dropped
its tag, so it stays decided. In `p` or in `b`, `post` turns it into a
plain `if`. The two copies then differ in a way conversion can't bridge,
because `Decidable.elim (Bool.decTrue c) …` and `Bool.ifThenElse c …`
are both stuck on a variable `c`.

There are two variants, both reachable from source. In each, an inner
`if` sits in another `if`'s condition and its own call uses its own
condition.

**(a) A kept `if` whose tag holds a tagged `if`.** `kind`'s comparison
case (`plain.rs:304-309`) answers `DecTrue` without comparing `b` with
the decision. `hole_proof` then passes the raw `b` to
`Bool.elimDecTrueIf` as `c` (`plain.rs:628`), but the hole's `post` holds
`post(b)`. That makes the lemma's right side `ite b_raw …` while the J
motive expects `ite post(b) …`, and the kernel refuses `%same`:

```stitchwort
def climbBoth (n: Nat) (i: Nat): Nat
    decreasing n - i
:=
  if (if i + 2 ≤ n then climbBoth n (i + 2) else 0) + i < n
  then climbBoth n (i + 1)
  else 0
```

The inner call needs `i + 2 ≤ n`, which only the inner condition gives.
The outer call needs `i < n`, which `omega` gets from the outer condition
`X + i < n`. Both `if`s are tagged. The outer one is kept (an allowed
position, a comparison, branches free of `h` once the calls lose their
proofs), and its `b` is `Nat.leq (Succ (X + i)) n` with `X` still tagged.

**(b) A decided `if` whose proposition holds a tagged `if`.** Here the
outer `if` is named, so it is never tagged. `mark` marks its decision,
which drops the inner tag there, but leaves the inner tag in `args[0]`.
`post` then makes `p` plain while the decision's type keeps it decided,
and the kernel refuses `%plain` itself: `Decidable.elim [p_post] … d`
with `d : Decidable p_pre`. This needs one other kept `if` in the body,
so that `count > 0`:

```stitchwort
def weird (n: Nat) (i: Nat): Nat
    decreasing n - i
:=
  if i + 1 ≤ n then
    (if big: (if i + 2 ≤ n then weird n (i + 2) else 0) < 100 then 1 else 0) + weird n (i + 1)
  else 0
```

Both examples rest on my reading: whether `omega` takes exactly those
facts decides whether each `if` is tagged. Either way the result is
`E-DECREASING` "internal error … refused … this is a bug in the compiler"
on a correct program. Nothing unsound is admitted.

`part`'s other internal error (`plain.rs:583`) and `hole_proof`'s "a
plain `if` with no lemma" (`plain.rs:621`) are reachable through the same
door. Starting from `args[0]`, `part` walks into a `Lam` inside a
proposition and finds it "where its proof can't reach". Beyond these
unmarked arguments, I found no shape where `mark` keeps a tag the builder
can't handle. `Let` is allowed only at a root, which is where `proof`
(with a type) handles it. Over-applied `elim`/`ite` go through the `App`
case. Every `Lam`, `Case`, `NumCase`, `Proj` and `Pi` drops the tags
beneath it through the default arm.

**Fix.** In `mark`'s `elim` case, run `args[0]`, `args[1]` and `b`
through `mark(…, allowed = false, …)`, which strips their tags, and do
the same for `ite`'s `args[0]`. Then the comparison case of `kind` can
safely check `b` against `bind::comparison`'s `Bool`, or rely on the
stripped terms agreeing. Add the F7 invariant check and both examples as
tests (expected: `f.unfold` shows the inner `if` as `if _:`). About 30
minutes.

### F2. A generator failure fails the definition (medium, high confidence)

`plain_view`'s error goes through `generator_failed` (`decreasing.rs:1083-1088`)
and becomes a hard `E-DECREASING`. The definition, `f.%step`, `f.%go` and
the old `f.unfold` proof were all fine, so any F1-like gap turns a
correct program into a compile error. The design note's risk section
(§6) said: "Fallback, if a shape defeats it: keep today's `f.unfold` for
that definition and give a note." The lane chose the error, which hides
nothing, but it costs the user their program for a compiler bug. A
fallback would drop the view, state `f.unfold` over `f.%step` as before,
and emit a warning that names it as a compiler bug. `%plain` would
already be declared, so it would need dropping or leaving unused. This
is D3100.

### F3. Every `Bool` `if` in a `decreasing` body now carries its fact (medium, medium confidence)

Before this change, a `Bool` `if` in a `decreasing` body was always
`Bool.ifThenElse`, and `f.unfold` showed it plain. Now it is decided with
`Bool.decTrue c` (`check.rs:5125-5134`), and the branches see `c = True`.
If a recursive call's proof now uses that fact, where `auto` or `omega`
finds a proof through it, the `if` stays decided wherever `mark` can't
show it plainly. That covers an `if` inside a lambda passed to another
function, in a condition, or in a `match` within a leaf
(`plain.rs:426-458`). In those places `f.unfold` used to show a plain
`if` and now shows `if _:`, and an existing proof that matched the plain
form breaks. `omega` emits only the facts its certificate uses
(`omega.rs:3859`), so this happens only where the new fact actually
helps. That is exactly the case where an older proof had found another
route. `syntax.md` documents the result, though not as a change for
existing `Bool` `if`s.

The `f.%step` of such definitions also runs `Decidable.elim (Bool.decTrue
c)` instead of `Bool.ifThenElse c`. The JS and Rust runtimes special-case
`Decidable.elim` (`js/src/lib.rs:2353`, `rt/src/fusion.rs:138`), so I
don't expect a cost, but nothing measures it.

**Recommendation.** Add a test that pins an under-a-lambda `Bool` `if`
(`f.unfold` shows `if _:`, or plain when the call doesn't need the fact),
and add a sentence to `docs/syntax.md` saying a `Bool` `if` there can now
show the `if _:` form. Restricting the fact to the positions `mark`
allows would avoid the change but lose the feature under lambdas
(`attach`), which the design wants. I'd keep it as built.

### F9. Test gaps (medium, high confidence)

The example covers `Bool` conditions and `Nat` comparisons through
`Bool.elimDecTrueIf`: `countUp`, `gcd`, `climb` (nested, in an argument,
after a `let`) and `sumWhile` (an arm of the definition's own `match`).
Its `*Unfolds` theorems can fail, since they check the plain form by
conversion. `opaque-decreasing.sw` covers an opaque `f`. Not covered:

- **`Decidable.elimIf`** (`Kind::ToBool`). No test reaches it. It is the
  path for an unnamed `if` on any proposition decided other than by
  comparison, which includes `if n = 0 then … else f (n - 1)`, probably
  the most common shape. Its argument order (`plain.rs:622-634`) has
  only been checked by reading.
- **The bound-operand path** of `kind` (`plain.rs:310-333`,
  `bind::Bound`).
- **A lexicographic measure** with a plain `if`. `decreasing_unfold`
  handles both measures, but no example has `decreasing (m1, m2)` with
  one.
- **A call in the `else` of a `Bool` `if`** that needs `¬(c = True)`, for
  example `if Nat.leq bound i then i else countUp bound (i + 1)`.
- **The `if _:` fallbacks**: an `if` whose `h` is used elsewhere, one
  under a lambda, one in a condition, with `f.unfold`'s form asserted.
- **`Int` comparisons**, and F1's two shapes.
- **SW-2146** (that `f.eq.*` and `f.induct` exist). It is partly covered
  already: `library__hash_stability__decreasing-plain-if.snap` lists
  `Main.countUp.eq.ifTrue`, `….induct` and the rest, so if one
  disappeared the snapshot would differ. That only proves they exist,
  not that they can be used, and a snapshot is easy to re-accept without
  noticing, so the ticket still stands.

### F10. The wider reach wasn't checked against AoC (medium, medium confidence)

An unnamed proposition `if` whose fact only a decrease uses now appears
plainly in `f.unfold`. The design intends this (§3(d): "`f.unfold` is
stated over the body as written … A hypothesis the body uses for
anything else stays"). It breaks any proof that takes the old
`Decidable.elim` apart after `rewrite f.unfold`, with `Decidable.elimEq`
or a lemma like `Nat.untilStableDecYes`. In std nothing changed: the
prelude hash snapshot only gains the two lemmas, and
`Nat.iterateUntilStable` uses a named `if h:`, which never changes.
Among the examples with hash snapshots, only `countDownZero` changed, and
its proof still holds. Lanes don't run the AoC checks, so no one ran
them. Eight days rewrite with `.unfold`: 2020 days 8 and 9, 2021 day 16,
and 2024 days 12, 23 and 24, and 2025 days 2 and 4. I read their
`decreasing` bodies and found nothing likely to be affected. Their
unnamed `if`s either have no call under them or reach their calls
through a lifted `match`, whose proof doesn't need the condition. A
targeted run would confirm that (D3101).

### F4. Missing lemmas are an internal error (low, high confidence)

`Lemmas::new` (`plain.rs:253-280`) fails with "`Decidable.elimIf` isn't
loaded" when either new lemma isn't bound. It runs whenever the step
kept a tag. That fails any qualifying `decreasing` definition elaborated
before `Decidable.sw`'s new theorems: one in std core earlier in the
load order (`Division.sw` uses `decreasing`), or one under a reduced
prelude. Return `Ok(None)` from `plain_view` instead, which keeps the
old `f.unfold`. That choice is deterministic for a given program, not a
limit. S.

### F5. `keep_plain` covers all of `finish` (low, low confidence)

`decreasing_step` sets `keep_plain` around the whole of `e.finish(&term,
0)` (`decreasing.rs:1411-1419`). `finish` settles the queue and compares
the helpers it is waiting on before its own `settle_tagged`. If any of
that settled another body through `settle_tagged`, as `lift.rs:783`
does, the `%plain` tags in that body would be kept for good, since only
the step gets the second, stripping settle. I found no path that lifts
during `finish`, so this is about how wide the window is, not a known
leak. Pass "keep plain" to the final settle only, for example through a
`finish_keeping_plain` or a parameter. That also removes the `Cell`'s
invariant, which today lives only in its comment. S.

### F6. `%unfoldStep` chosen by `DefId` order; missing from `def_items` (low, high confidence)

`equations.rs:2063` takes the newest `f.%unfoldStep` if it is newer than
the newest `f.%step`. That works: a definition re-elaborated without
plain `if`s leaves only an older `%unfoldStep`, which the filter
rejects, and the check cache replays declarations "in their original
order" (`cache/mod.rs`, `admit_replayed`). But the rule depends on two
invariants that no code checks. It would be more robust to choose
structurally: take `%unfoldStep` only if its type's right side is headed
by `step`, or record the pair in a table when `decreasing_unfold` makes
it. Both scans also walk every definition, now twice for each
`decreasing` definition. Separately, `f.%unfoldStep` isn't pushed to
`made` (`decreasing.rs:1777-1800`), so it never gets a `def_items`
entry, unlike every other generated definition. `auto_eligible` then
treats it as declared everywhere (`module.rs:2273`). It's harmless while
`%` names stay out of `auto`, but inconsistent. S.

### F7. Two recursions that must agree (low, high confidence)

`mark` decides which tags stay. `post` builds `%plain` from what it
keeps, and `proof`/`part`/`hole_proof` must then prove every kept tag.
They agree only by their comments, and F1 shows they drift. There's a
cheap guard: after `mark_tree`, count the `%plain` `let`s in `marked`
and return an internal error, or no view under D3100's fallback, unless
there are exactly `count` of them, each the decision of an `elim`. That
would have caught both of F1's variants. Longer term, one pass that
returns `(pre, post, proof)` for each node would make them agree by
construction (M). Smaller: `proof`'s J chain repeats `decreasing.rs`'s
`cong`/`rebuild` logic, and `children` (`plain.rs:103-180`) is a
hand-written child map that the next `Term` variant must remember to
update.

### F8. Comments and docs (low, high confidence)

- `Unused::Bool`'s doc (`check.rs:5207`) still says "The `Bool` reading
  of `a && b`". In a `decreasing` body it now also carries a plain
  `Bool` `if`'s condition.
- `docs/guide/07-recursion.md` says the `else` gets the condition
  "false". For a `Bool` `c` it is `¬(c = True)`. `syntax.md` gets it
  right, and `omega` reads both, so this is only precision.
- Conjunctions (`if a < b && c < d`) are decided by `Decidable.andThen`.
  `kind` finds no lemma for them, so they always show `if _:` when a
  call uses the fact. `syntax.md`'s list of cases that show `if _:`
  doesn't mention them. This is no regression, since they showed it
  before too.

## Checked and sound

- **Statements.** `f.unfold`'s type (`decreasing.rs:1725-1737`) and
  `%same`'s (`plain.rs:772-783`) are built from the plan and `%rec`'s
  telescope, independent of the proof, and say what the docs claim:
  `f x… = f.%plain x… (y… => f y…) c…`, and `f.%step x… (y… p => r y…)
  c… = f.%plain x… r c…`.
- **What `%plain` holds.** It is `post(mark(adapt(step body)))`. The
  calls lose their proofs. Kept `if`s become `Bool.ifThenElse b` with
  `b` from `into_bool`, the same `Bool` the plain `if` has outside
  `decreasing`, so the user's restatement matches by conversion. Lifted
  helpers get `y… p => r y…`, which beta-reduces to what they got
  before.
- **Lemma uses.** `Decidable.elimIf [p] [a] d y n t e sy sn`,
  `Bool.elimDecTrueIf [a] c y n t e sy sn`, `Decidable.elimCong` and
  `Bool.ifThenElseCong` each get their arguments in statement order
  (`plain.rs:622-678`). Every comparison decision is literally
  `Bool.decTrue (…)` (`Decidable.sw:147,150`, `Int.sw:115,117`,
  `Float.sw:321,323`), and a decision's proposition converts with `… =
  True` because those instances typecheck. The branch proofs `h => p`
  give `y h = t Trivial`, since `mark` checked that `h` is unused.
- **The J chains.** In `proof`, the base is `Refl : pre = pre`, step `i`
  turns hole `i` from `pre` to `post`, and the end is `pre = post`
  (`Same` parts hold no tags). In `decreasing_unfold`, the base is
  `f.%unfoldStep : f x = f.%step x r_f c`, and `r_f` equals
  `adapter(r_plain)` after beta. `%same` then moves that to `f.%plain`.
- **`Rec::adapt`.** The index arithmetic (`depth - 1 - level`), dropping
  exactly the last argument, partial applications (through `children` to
  the adapter) and binders (`children`'s depths match `Case`'s
  `names.len()`, as `respects` does) are all right. `instantiate(…,
  Refl)` for `%rec`'s result assumes the result doesn't depend on the
  proof. If it did, the kernel would refuse.
- **Leftover tags (Q5).** `f.%step` is defined from the second
  `settle_tagged`, which runs with `keep_plain` off and strips every
  `%plain`. Lifted helpers are settled in `lift.rs` before `keep_plain`
  is set. `%plain` has none, since `post` rewrites every kept one and
  `mark` dropped the rest. `f.%unfoldStep`, `f.eq.*` and `f.induct` come
  from the stripped step. While the body is being elaborated, a
  `let %plain` can appear in a term shown in a goal or error. That was
  already true of `%conj`, and it's rarer here because the tag is added
  after the `if`'s branches are done.
- **Equations.** `f.eq.*` from `%unfoldStep`'s decided tree state the
  `else` as `c = False` (D2186, `equations.rs:3708`), as a plain `if`'s
  equations do.
- **Opaque `f`.** `%unfoldStep` is opaque and unfolds `f`, as `f.unfold`
  does. `%plain` and `%same` don't mention `f`.
- **Runtimes** run `f.%step` with the tags stripped, unchanged in shape
  for `if`s whose branches don't use the fact (`unused_proof_if` still
  makes them `Bool.ifThenElse`).
- **`explain_obligation`'s note** now suggests the plain `if`, which is
  right in every position where a call can see the fact, under lambdas
  included.

## Calls I made

- F3: keep `Bool` `if`s giving their fact everywhere, and document the
  `if _:` change rather than restricting it.
- F4: no view when the lemmas aren't loaded is a deterministic choice of
  statement, not a limit, so it doesn't conflict with D2543.
- F6: recommend structural selection, not a fix to anything broken.

## Questions for Matt

- **D3100:** If generating `f.%plain` fails for a definition (a compiler
  bug, like F1), should `f.unfold` fall back to today's form with a
  warning that names it as a compiler bug, as the design note's §6 said,
  instead of failing the definition? [rec: yes. The program is correct
  and the old equation is still proved. Failing it costs the user their
  program for our bug, and the warning still reports it.]
- **D3101:** Run the AoC checks for the eight days whose proofs rewrite
  with `.unfold` (2020 days 8 and 9, 2021 day 16, 2024 days 12, 23 and
  24, 2025 days 2 and 4), to confirm the new `f.unfold` form broke none?
  [rec: yes. It's the only place the wider reach is untested, and my
  reading found nothing likely to break, so it should be a quick
  confirmation.]

## Tickets to file

**Lane A (Opus, about 60 min): the marking pass agrees with the proof.**
This is core `decreasing` generation (D2506).
- F1: strip tags in `elim`/`ite` type arguments and in a kept tag. Check
  the comparison case of `kind`.
- F7: assert that exactly `count` tags remain after `mark_tree`.
- F4: `Ok(None)` when the lemmas aren't loaded.
- F5: narrow `keep_plain` to the final settle.
- Tests: F1's two examples, an `if a = b` (`Decidable.elimIf`) and an
  `if x ∈ s` unnamed `if` with a call, and `snap:hashes`/`hash_stability`.
- If D3100 is yes: the fallback with a warning, plus a test that forces
  it (for example a debug option that refuses the view).

**Lane B (Sonnet, about 45 min): coverage and tidying.**
- F9: a lexicographic example, a call in the `else` of a `Bool` `if`, an
  `if` under a lambda and one in a condition with `f.unfold`'s form
  asserted, and `Int` comparisons.
- F6: structural `%unfoldStep` selection, and `%unfoldStep` in `made`.
- F8: the `Unused::Bool` doc, the guide's "false", and conjunctions in
  `syntax.md`'s list.
- F3: the `syntax.md` sentence.
- Fold SW-2146 in here, or note on it that the hash snapshot already
  lists the names.

**Not a lane:** D3101's AoC run, if Matt agrees, by the orchestrator's
verifier.
