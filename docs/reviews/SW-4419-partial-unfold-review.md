# SW-4430: review of SW-4419 (partial unfold, bounded-readback stage 3)

Opus paper review (D2364: the change generates kernel terms). Read from
`lane/SW-4419` at `4a24d2175`, against `main...lane/SW-4419` for `crates`,
`docs`, `examples` and `tools`. The hash snapshots were skipped. Nothing was
built or run.

**Verdict: merge after the named fixes.** The step is sound. Every way it
can go wrong ends in a check failure, a fallback, a kernel rejection or, at
worst, a panic, never in a proof of a different statement. The design's
D3688 claim ("at the `match`/`rewrite` itself, only gains") does not hold
as built in two places, though. Both are small to fix, and both widen the
risk that the Overmind run has to measure.

## 1. Soundness

**Verdict: sound.** Nothing here can produce an accepted proof of a
different statement.

- **The walk's result is convertible with the target.** Opening a call
  replaces `f a′…` with `quote_folded(unfold_once(eval(f a′…)))`, which is
  one delta step. The walked arguments `a′` are convertible with the
  originals by induction. The marks are `Ann`, and `eval` drops an `Ann`'s
  type (`value.rs:1704`), so a mark never changes a value. A call kept
  folded is rebuilt from its walked arguments, losing only `Loc` nodes.
- **What is built from it is checked as before.** For `match`, the motive
  is generalised from the opened goal and passes check 2 (agreement with
  today's generalisation, read back unfolded) and check 3 (the motive is
  type-checked now). For `rewrite`, `replace_occurrences_as` checks that
  the motive type-checks and computes back to the goal, then
  `hidden_copy` and the today's-instance check run. After that the kernel
  checks the declaration whole. So even a wrong opening could at worst give
  an ill-typed or non-convertible motive, and the elaborator or kernel
  rejects that.
- **The oracles are side-effect free.** Match's `is_needle` uses
  `conv_now`, which is pure conversion. Rewrite's oracle unifies (including
  `unify_solving_arguments`) inside a `Snapshot` that is restored, and the
  whole attempt sits inside `attempt`'s or `first`'s snapshot as well.
- **The markers.** `Meta(usize::MAX - 1)` doesn't collide with anything:
  `ELIDED` is `Meta(usize::MAX)`, and `erase::ERASED` (`usize::MAX - 1`)
  is a *variable* level, not a meta. Marks are never nested: `visit`
  returns `mark(t)` without walking `t`, and an opened body comes from
  `eval`, which has already dropped the argument marks. The strip in
  `opened` uses `replace_with`, whose hook is offered every node,
  including heads along an application spine (`Replace::app`), so it
  reaches every mark. **If one survived anyway:** rewrite treats any
  `Term::Meta` in the motive as `Outcome::Unchecked` and doesn't keep it.
  Match's check 3 would infer the `Ann` and evaluate its type, and
  `MetaStore::meta_solution` indexes `metas[m]` directly, so that is an
  out-of-bounds **panic**, not an acceptance. The kernel takes no metas in
  any case. So a survivor crashes and is never unsound. (Follow-up F1: a
  debug assertion after the strip.)

## 2. D3688: is every new success one the old path would have made?

D3688 itself isn't engaged. No statement changed: I checked the
`tools/fmt` diff, and every change there is in a proof body (the 46 pairs,
plus the reformatting around them). The design's §4.1 claim is that each
`match` or `rewrite` this changes ends with a result convertible with
today's. That holds for `rewrite` (`first` in the single-rule path). It
does **not** hold in two cases.

### M1. `match` and the transport can now *rescue* through calls (must fix)

In `matching/as_written.rs` `search`, the OnPath reading ends with
`(false, _) => Outcome::Rescued`, and `first` returns any `Ok(written)`.
So when today's search finds nothing anywhere and the folded reading
found `Nothing`, the OnPath reading can now refine the arms. That happens
when it finds an occurrence by conversion inside an opened body that
today's syntactic search over the normal form doesn't recognise (the
written-differently case, `Finder::agree`'s relaxation). Before this
change, that `match` refined nothing, so its arms saw the goal unchanged.
Now they see the scrutinee replaced. The arms' goals are then **not
convertible with the old ones**. The common idiom that breaks is `match s
with | C => (h: s = C …) rewrite h then …`: the `rewrite h` now finds
nothing (`E-REWRITE-NOTHING`). `transport_search` has the same
`(false, _) => Outcome::Rescued` arm.

This also contradicts the design's §3 ("If today's search finds nothing,
the partial step found nothing either … the rescue sees the same
situation"). **Fix:** for `Reading::OnPath`, `(false, Reading::OnPath)` →
`Err(Outcome::Nothing)` in both `search` and `transport_search`. That is
one line each.

**Related, not must-fix (watch item W1):** even with today's search
finding something, the agreement check lets OnPath abstract *more*
occurrences than today's (written-differently ones inside opened bodies).
Stage 2's folded reading already does the same, and that was accepted
there. But it means the arms of a `Partial` site are convertible with
today's arms only when no extra occurrence was abstracted. The design's
§0 and §4.1 wording ("keeps a goal convertible with today's") should say
so. A strict agreement mode for OnPath would make the claim exact, if the
Overmind run shows breakage of this kind.

### M2. `rewrite repeatedly`'s written-only pass now opens calls (must fix, or decide and measure)

`rewrite_once` calls `as_written::first` in `written_only` mode too, and
`first` now always tries the OnPath attempt after a `Nothing` or
`Incomplete` result. So:

- **Set rules change behaviour.** A set's rules are only ever looked for
  as written (`repeatedly.rs`, `listed.origin_set && !written_only`). A
  set rule whose key is visible but whose occurrence also has a hidden
  copy (`Incomplete`) used to fail. Now it can rewrite after opening calls.
  So a `rewrite repeatedly` with sets applies more rewrites, and its end
  goal, which is *not* convertible with the old one (rewriting isn't
  conversion), changes. Any `then` block or `try_close` after it sees a
  different goal. That is a new success at the step, but it is not one
  the old path would have produced.
- **The order of rewrites can change for listed rules.** A rule that used
  to wait for the full pass now fires in the written pass, possibly
  before other rules. The end goal can differ again.
- **Cost.** The written pass is the cheap pass by design (SW-3654: the
  printer lemmas' full search is the cost). Now every rule that passes
  `may_fit` but finds `Nothing` or `Incomplete` as written also pays for
  an OnPath walk (up to 64 openings) in that pass.
- **Doc.** `Repeated::written_only`'s comment ("Only the goal as written:
  no comparison by computing") is no longer true.

The design note doesn't mention `rewrite repeatedly` at all. **Fix:**
pass `written_only` into `first` and skip the OnPath attempt there. The
full pass still gets the step through the same `first`. If the
orchestrator would rather keep it, the Overmind run must cover it
explicitly (W3 below), and the `written_only` doc must change.

### 2.3 The fallback structure: correct

- **`match` `first`.** OnPath runs only after the folded reading came to
  `Nothing` or `Incomplete`, and not for a non-`on_path` scrutinee. Each
  attempt has its own `search_budget` and `Snapshot`. Every failure
  (`Err` outcome, over budget, a recoverable error) falls through to
  `report` and `Ok(None)`, and the caller then runs today's search as
  before. A fatal, unrecoverable error propagates, as it did for the
  folded attempt; whether the walk can raise one that today's path
  wouldn't (a nesting-depth error from a deep opened body) is covered by
  W4.
- **The transport.** It has the same structure, but it doesn't consult
  `Scrut::on_path` (F4).
- **`rewrite` `first`.** OnPath runs after `Nothing` or `Incomplete`.
  Failures (including `RanOut` on the OnPath attempt) fall to `First::Not`
  or `First::RanOut` from the *folded* outcome, so `unconfirmed` sees what
  it saw before. `rescue` and `unconfirmed` don't use OnPath. Good.

### 2.4 Later steps in the arm: what can stop checking

The design's §4.2 analysis stands: later `match` and `rewrite` steps are
robust, and `rfl`, `decide` and conversion are unaffected. Three things
are exposed:

1. **Unification against lemmas and inference of implicit or
   continuation arguments.** First-order on the folded calls versus on the
   bodies. The `[j := …]` drops show the gain; the same mechanism can pick
   a different solution elsewhere.
2. **Arms that now show opened bodies of definitions written with
   `match`/`if`.** The goal then contains lifted helpers (`f.%matchN …`)
   in place of today's normal form. A later step that relied on that
   computing further (such as `Parse.followsThen` expecting a `bind` head)
   may now meet a stuck helper call. This is the general form of the reify
   problem (§4).
3. M1, W1 and M2, if not fixed.

**For the Overmind run** (`check --no-cache` on the lane branch: `tools/fmt`,
`aoc`, `games/rogue`, std), ask it to report:

- **W2.** Every newly failing declaration, with its error code. Expect
  mostly `E-TYPE-MISMATCH` or `E-UNSOLVED` at a lemma application, or
  `E-REWRITE-NOTHING` for the `rewrite h` idiom (M1 or W1), inside a
  `match` arm or after a `rewrite`. For each, the
  `STITCHWORT_MATCH_METRICS`/`STITCHWORT_REWRITE_METRICS` line of the
  enclosing site: was it `partial`?
- **W3.** Declarations using `rewrite repeatedly` with a rule set, if M2
  is kept: failures, and changes in their end goals.
- **W4.** Any panic (a surviving marker or an index out of range) and any
  new `E-RESOURCE`. Grep the stderr for `panicked`.
- **W5.** Check time per namespace against `main` for the six fmt
  namespaces in the design's §6, and the counts of `partial` vs `nothing`
  per namespace. A low partial rate in the parser proofs means the
  64-opening cap, or the recursion guard, is cutting the walk short (see
  §3).
- **W6.** Goal displays (hovers or `examples/goals`) that contain `%`
  names after the change.

## 3. Determinism and cost

- **Determinism: yes.** `unfold_path` has no hash maps. The walk is
  pre-order through `replace_with_under`, the needles are a `Vec`, the
  recursion guard is a `Vec`, and the cap counts in walk order. The
  budget (`Budget::limited`) counts evaluation steps, not time. So the
  result depends only on the term.
- **Bounded: yes, with caveats.**
  - The cap is 64 openings per `opened` call. That counts opened-and-empty
    calls too, which is right, since they are the cost.
  - Each OnPath attempt runs under its own `search_budget` (steps).
  - Read-back and `replace_with` aren't step-counted, only depth-checked
    (`budget.nesting`). So the cost of one opening is proportional to the
    definition's body size, times 64.
- **Cost risk.**
  - In `match`, `opened` runs on the goal **and on every variable's type
    in context** that isn't skipped, each with its own 64-opening cap. It
    includes variables that can't be copied (`!unrefined[l]`), whose walk
    is wasted. In a parser proof with 30 to 40 hypotheses, that can be
    over 2,000 openings for one failed `match`. Follow-up F2: walk only
    the `unrefined` types.
  - The relevant variables are those of the needle as written. In the
    formatter's proofs they include `modes` and `self`, which nearly every
    call mentions, so the walk opens many calls that turn out empty and
    can reach the cap before the occurrence, in pre-order. That can only
    cost gains (falls back), never correctness, but W5 should show it.
  - **D2540 tension (note, not a fix):** whether the cap or the budget is
    hit decides between a partial result and today's, two representations
    of convertible goals. That is the same as the existing as-written
    attempt's budget, so it's not new in kind.

## 4. The reify exclusion

**It works, and it is tested** (`examples/goals/reify-return.sw` pins the
goal). **But it is keyed on the wrong thing.** The problem is not who made
the scrutinee. It is *what gets opened*: the bodies of handler machinery
(`Call (L (%stop msg)) …`), which today's full normal form computes past
after refinement, while the partial reading leaves them half-open in the
goal. A user-written `match` on a goal containing a `reify`-produced
computation would hit the same thing, and the other compiler-made
scrutinees (`walk/mod.rs:1419`, the walk tactic's planned `match`, and
`cases.rs:2856`'s atom split) are excluded by nothing, though their
openings are normally of user definitions and so fine.

So "any compiler-made scrutinee" would be the wrong generalisation too: it
would exclude the walk tactic's matches, which are exactly the
parser-proof shapes the step is for. **Recommendation (F3):** keep
`on_path` for now, as a conservative and tested patch, and file a
follow-up to replace it with a rule on the *opened* definition: don't open
a compiler-generated definition (lifted `%` helpers, the effect and
handler runtime). W6 would find the cases. Also make `transport_target`
honour `on_path` (F4). Reify passes no name today, so it has no
transport, but nothing enforces that.

## 5. Docs

- `docs/syntax.md` (both sections) and `docs/proving-guide.md` are
  accurate as far as they go. They don't mention the recursion guard or
  the cap. One clause would do: "a definition is opened at most once on
  each path, and at most 64 calls in all; past that the usual search
  runs".
- `docs/proposals/partial-unfold.md`'s status line is accurate (memo not
  built, cap instead; "outside proof positions" not built). Its body now
  overclaims:
  - §0's "Every step this changes keeps a goal convertible with today's"
    and §3's rescue paragraph are false until M1 is fixed, and §4.1 needs
    W1's qualification.
  - Nothing mentions `rewrite repeatedly` (M2).
- **Not done from the design's §7.6:**
  - `goal-as-written.md` has no "as built" paragraph.
  - `bounded-readback.md` §4.2 doesn't have the two refinements, and §7
    doesn't mark stage 3 (SW-1838) as built.
  - Follow-up F5, or fold it into the fix lane. The orchestrator should
    also close or retitle SW-1838.
- The two accept examples' comments are accurate to the code. They state
  the arm and next goals, but nothing checks those (see §6).

## 6. Tests

**Not enough.** The two accept examples show that the step succeeds on
the two motivating shapes, and their hash snapshots pin the terms. But:

- **There is no fallback example.** The design's §7.3 asked for one: a
  copy that the partial walk can't see (behind the recursion guard, for
  example `sum (a :: b :: xs)` looking for `sum xs`, or past a
  `Follows`-around-recursive-parser shape), so that agreement fails and
  today's result is used. That is the one path whose failure would be
  silent and wrong-looking (worse goals) rather than an error. It needs
  one accept example plus its goals snapshot. **Must fix (M3).**
- **Nothing pins the displayed goals.** The point of the change is the
  shape of the arm and next goals: `Follows` kept folded, the right
  `line others` kept folded, nothing opened that was found empty. A
  regression in the walk, such as opening too much, would still check,
  so only a hash snapshot would move, and hash moves get re-recorded
  routinely. An `examples/goals` file for each of the two accept shapes,
  showing the `False` arm's goal and the goal after `rewrite same`, would
  pin the two refinements of §2.3 (arguments first; opened but empty
  stays folded). **Must fix (M3, same lane; two or three small files).**
- The walk has no unit tests (the design's §7.1 listed seven). The goals
  examples above cover the two that matter most. The rest (several
  occurrences, under a binder, a call that steps at once, the cap, the
  recursion guard) are follow-up F6.
- The M1 fix needs a test: a `match` where today's refines nothing and
  the OnPath reading would rescue, showing the arm goal unchanged (a goals
  example).

## Must-fix (before merge)

- **M1.** No `Rescued` from the OnPath reading. In `matching/as_written.rs`
  `search` and `transport_search`, `(false, Reading::OnPath)` returns
  `Err(Outcome::Nothing)`. Add a goals example where today's refines
  nothing and the arm goal stays unchanged.
- **M2.** Skip the OnPath attempt in `rewrite repeatedly`'s written-only
  pass: pass `written_only` into `as_written::first`. Otherwise set rules
  newly fire, rewrite order changes, and the cheap pass gets dearer.
  (Alternative: keep it, fix `Repeated::written_only`'s doc, and have the
  Overmind run cover W3. I recommend the fix.)
- **M3.**
  - A fallback accept example: a hidden copy the walk can't reach, so
    agreement fails and today's search is used.
  - `examples/goals` snapshots for the `match` and `rewrite` partial
    shapes, pinning the folded `Follows` and the folded right-hand call.
- **M4.** Correct `partial-unfold.md`: §0, §3 and §4.1 as M1 and W1 leave
  them, and a sentence on `rewrite repeatedly` as M2 leaves it.

## Follow-ups (file as tickets)

- **F1.** A `debug_assert!` after the strip in `unfold_path::opened` that
  no `Meta(OCCURRENCE)` remains. A survivor panics in `meta_solution`
  rather than failing cleanly.
- **F2.** In `match`'s OnPath reading, walk only the `unrefined` variables'
  types (the others can't be copied). This is a cost fix.
- **F3.** Replace `Scrut::on_path` with a rule on the opened definition:
  never open compiler-generated definitions (`%` helpers, handler
  runtime). Check the walk tactic's and `cases`' goals while doing it.
- **F4.** Make `transport_target` honour `Scrut::on_path`.
- **F5.** Update the docs as the design's §7.6 asked: an "as built"
  paragraph in `goal-as-written.md`, and in `bounded-readback.md` the two
  refinements in §4.2 and stage 3 marked built in §7. Mention the guard
  and the cap in `syntax.md` and the proving guide. Close or retitle
  SW-1838.
- **F6.** Unit tests for `unfold_path`: several occurrences, under a
  binder, a call that steps at once, the cap, and the recursion guard
  (which skips a genuine nested path: incomplete, falls back).
- **F7.** `is_needle` duplicates `Finder::occurrence` (the same lowering
  and the same `same`/`conv_now` test). Share one function, so the oracle
  and the agreement check can't drift apart.
- **F8.** The recursion guard checks the folded call's head id but pushes
  the id that `eval` returned. They differ for a definition that unfolds
  straight to another's call. Push the folded id too. That costs
  completeness only, and the cap bounds it.
- **F9.** The walk takes a whole application spine at a `Def` head, so a
  partial application `f x` inside `f x y` is never offered to the
  oracle, though `Replace::app` offers it to `Finder`. That is incomplete
  only (falls back). Note it in the module doc, or offer the prefixes.
- **F10.** Unbuilt parts of the design: the per-cell memo (§2.1 2(d)),
  and the "outside proof positions" refinement of the relevant variables.
  The second would cut the cap pressure W5 measures.

## What I did not do

No builds, tests or metrics runs. Neither the claim that the two accept
examples fail without the step nor the count of 46 dropped pairs was
checked; both are from the lane. Whether `Snapshot` covers every side
effect of `unify_solving_arguments` (instance resolution, postponed
problems) was taken from its use elsewhere in `rewrite/as_written.rs`, not
re-read.
