# Record eta as merged: a fresh-eyes review (SW-2068)

*7 November 2026, by reading only: no builds, tests or runs. Read at
`a0cea6157` (`main`), covering merge `319c28c0c` (stages 1 and 1b, SW-1642)
and what followed it: SW-1829 (`eta_fields`), SW-1913 (the six AoC proofs,
repros in `docs/repros/sw-1913/`) and SW-1997 (`Bind::Alias`). I read
record-eta.md, record-eta-remaining.md, the SW-1764 review, the SW-1767 and
SW-1768 tickets, SW-1998 to SW-2000, and the SW-1869 core review
(`docs/reviews/code-review-core.md`), whose record-eta findings overlap
this one's; where they do, I say so and cite its ticket rather than filing
again. Line numbers are `a0cea6157`'s.*

## Summary

**Verdict: sound, and no new high-severity problem.** I found nothing that
lets eta equate terms that should differ. The eta conditions
(`qualifies_for_eta`) are read from the final declaration on both admission
paths and rule out each known unsound shape: proof-only records (D1981, the
Lean and Rocq unit-like problem), records in `Prop`, and projections out of
a proof or out of another type with the same layout. The Agda #2170 class
(projections out of irrelevant fields, and eta making all values of a type
equal) is excluded too. Irrelevance here is by sort only, never by
annotation, and a `Prop` type never has projections. Both rules terminate
for the reasons their comments give. The consumers of `Proj` that SW-1997
didn't reach are all handled: hash, cache codec, dump, JS, the Rust
runtime and native code (through `proj_as_match`), termination, erasure,
omega, ring and auto. A few consumers that look at terms *as written*
don't know `Proj` yet. Users see these in two places: how goals print, and
how `match` finds its scrutinee.

The weak spots are cost and coverage, not soundness. The SW-1829 shape
(one field call re-running its base call) survives in two places SW-1829
didn't touch, conversion's `unfold_folded` and the unfolded read-back. That
is the SW-1869 F1 remainder, already filed as SW-1914, and I confirm it's
still there. Two printers that recognise accessor calls don't recognise
`Proj`, so a record update on an unknown record prints as a full literal
once rule 2 has opened it. Neither fuzzer generates anything eta touches,
though record-eta.md §12 counts the fuzzers as a mitigation. One panic path
is new with eta: projecting an ill-typed metavariable solution while
elaborating. It's the SW-924 class and unconfirmed. The design note has
drifted from the code in five places.

**Top five recommendations**

1. **Land SW-1914** (field calls keep their base call's cell in
   `unfold_folded` and the unfolded read-back), and fold the representation
   clean-up of F9 into it. This is the one remaining instance of the 2ⁿ
   shape. Opus, M.
2. **Teach the as-written consumers about `Proj`.** `record_update` and
   Float's `keyOf` printer should count `Proj(d, i, x)` as "field `i` of
   `x`" (F2). `as_written::agree` needs a `(Proj, Proj)` arm (F5). Sonnet
   for the printer, S; the `agree` arm goes with SW-1999 (Opus).
3. **Make the fuzzers cover eta** (F4). Add `Term::Proj` and an eta record
   (plus a proof-only one) to `fuzz:kernel`'s generator. Add eta attempts
   to the `fuzz:soundness` corpus. Sonnet, M.
4. **Close the panic path from ill-typed metavariable solutions** (F3).
   Look for a repro first, then guard `first_order`'s solution as SW-924
   does, or turn `ReplayElim`'s mismatched projection into an error. Opus,
   S to M.
5. **Bring record-eta.md up to date** (F6). §6.4 says rule 2 doesn't fire
   on unsolved metavariables; it does (D2511). Four smaller drifts are
   listed below. Sonnet, S.

**Counts:** 0 high, 4 medium, 6 low.

## Findings

| # | Where | Finding | Sev | Conf | Size |
|---|---|---|---|---|---|
| F1 | `core/src/value.rs:2237-2273`, `2596-2616`, `1627-1657` | A stuck field call is a `Neutral(Def f, [x, .i])` with no unfolding cell. Every comparison that unfolds it, and every unfolded read-back, re-runs `f x` from scratch: k re-runs for k fields, multiplied by nesting. SW-1829 fixed only the forcing path. **SW-1914, still open** | medium | high (gap), medium (cost) | M |
| F2 | `core/src/pretty.rs:2109-2154`, `1620-1628` | `record_update` and Float's `of_bits` recognise only accessor calls, not `Proj`. A record rule 2 opened, read back with `Proj` fields, prints as a full literal (`{ hp = state.hp, …, message = m }`), not `{ state \| message = m }` | medium | high | S |
| F3 | `core/src/value.rs:1730-1741`, `1899-1913`; `elab/src/unify.rs:2015-2050` | Rule 2 now fires on unsolved metavariables (D2511), so `?r.0` exists before `?r` is solved. `first_order` can solve `?r` with a value of another type (its pairs needn't share one). Forcing `?r.0` then reaches `ReplayElim` → `project`, which panics on anything but `Ctor(d)` or a neutral. Before eta, `R.f ?r` just got stuck. SW-924 class; unconfirmed | medium | low | S-M |
| F4 | `core/tests/it/fuzz.rs:42-46`, `48-104`; `driver/tests/soundness_fuzz.rs` | Neither fuzzer touches eta. `fuzz:kernel`'s generator has no `Term::Proj`, and its only data types (`Nat`, `List`) have no eta. The soundness corpus has no eta attempt. record-eta.md §12 counts both as mitigations | medium | high | M |
| F5 | `elab/src/matching/as_written.rs:690-766` | `Finder::agree` has no `(Proj, Proj)` arm. Two targets that differ only inside a projection fail the completeness check, so `match` drops the as-written result and falls back to the unfolded test. That's SW-1999's territory | low | high (gap), medium (impact) | S |
| F6 | `docs/proposals/record-eta.md:344`, `305`, `532-535`, `562-564`, `290-294`, `654-656` | The design note and the code disagree in five places (details below); the biggest is that §6.4 says rule 2 doesn't fire on unsolved metavariables | low | high | S |
| F7 | `elab/src/unify.rs:1669-1673`, `2030-2032` | `NO_ETA` is set and reset by hand. A panic in between leaves rule 1 off in the unifier on that thread for good, and `search.rs:1402` and `driver.rs:129` catch panics and keep the thread. Confirmed, and **filed twice**: SW-1901 and SW-1979. Merge them | low | high | S |
| F8 | `core/src/value.rs:1974-1989` | Rule 2 builds all k fields on every firing (k spine copies; on a call, k `Rc<Unfolding>`s too), though a branch usually reads one, and an accessor exactly one. record-eta.md §10 suggested binding them lazily; that isn't done | low | medium | M |
| F9 | `core/src/value.rs:655-671`, `727-737`, `2152-2162`, `1652-1654` | A field of a call has two representations: a `Value::Call` whose spine ends in projections, and a `Neutral(Def)` whose spine does, once stuck. The invariant "a call's spine is its arguments then projections" lives only in comments, and each of about ten readers must remember `is_call_field` or reach an `unreachable!` | low | high | M (with SW-1914) |
| F10 | tests | Missing: rule 1 in shortcut mode, a `{ u: UnitType, ok: P }` record (two unknowns stay apart), the occurs case `?r ≡ { a = ?r.a, b = 3 }`, any surface `examples/` file for eta, a JS test of a projection, and a codec round trip of `Term::Proj` on its own | low | high | M |

## Details

### F1. Field calls still re-run their base call (SW-1914)

SW-1869's F1 named three paths where a stuck field call re-runs its call.
SW-1829 fixed a different one: forcing, where `Frame::CallField` re-forced
the call. It did so by presetting each field's cell with the stuck value
(`eta_fields`). I checked that preset against what `CallField` computes,
case by case: a plain call, a nested field call, a call that steps at once,
and a metavariable at the head. It's the same value, and the `Kept`
epoch discards it once a metavariable inside is solved.

The other two paths are unchanged at `a0cea6157`:

- **Conversion.** `unfold_folded` (`value.rs:2237`) runs `f`'s case tree
  from its arguments for each field-call neutral it meets, with no cell and
  no memo (`CallMemo` keys on `Value::Call` cells only). In `{ a = …, b =
  … } ≡ n`, each pair against `(f x).k` runs `f x` again.
- **Unfolded read-back.** `value.rs:2614` rebuilds the call as
  `Value::Call(*id, call, Rc::default())`, a fresh cell, so each field
  read back unfolded recomputes `f x`. The term also gets one copy of
  `f x`'s unfolding per field, which may be part of SW-1762's 4.6k → 106k
  nodes.

SW-1914 says 19,261 such re-runs in 2020 day 20's proofs. This is the only
remaining instance of the "each level redoes the one below" shape I found.
`same_field_records` and `one_step_apart` are bounded, and `matches_at_once`
is SW-1869 F6.

**Fix:** SW-1914 as filed. Its option (b), keeping a stuck field call as a
`Value::Call` with the stuck value in its cell, also fixes F9.

### F2. Printers that know accessors but not projections

`record_update` (`pretty.rs:2109`) prints a constructor as `{ x | f = s }`
when most of its fields are `R.f x` *accessor calls*. Rule 2 binds fields
to `Proj(R, i, x)`. So when an update helper is opened on an unknown
record and the result is read back unfolded (motives, `cases`, `match`,
tactic output), the constructor has `Proj` fields, and it prints as the
whole literal. For the roguelike's `State` (SW-1762's `resolveOutOfWalls`)
that's every field written out where `{ state | message = … }` was
shown before. The same value written by hand (accessor calls) prints as an
update, so one value has two printed forms depending on how it was made.
`of_bits` (`pretty.rs:1620`) has the same gap for `x.bits` inside
`Float.keyOf`.

record-eta.md §6.4's table lists these two printer cases as needing a
`Proj` arm "if use sites switched". But read-back already produces `Proj`,
so they're needed now.

**Fix:** in `record_update`'s `taken_from` and in `of_bits`, accept
`Term::Proj(d', i, x)` with `d' == d` and `i` equal to the field's index.
Add a snapshot of a goal showing an update on an unknown record. S, Sonnet.

### F3. A new panic path: projecting an ill-typed solution

`project` (`value.rs:1899`) panics on a constructor of another type, a
number, a function and so on. Its doc says only an ill-typed term reaches
it, and in the kernel that's true (`infer_proj`). In the elaborator,
values can be ill-typed for a while:

1. Rule 2 fires on an unsolved `?r` of eta type `R` (D2511). Any `match`
   on `?r` in a goal leaves `?r.0` in values.
2. `first_order` (`unify.rs:2015`) pairs `?m … x` with `f … y` by `x ≡ y`.
   The comment says these needn't share a type. With `x = ?r` and `y = 5`,
   solving gives `?r := 5`.
3. The next force of a value holding `?r.0` replays the projection
   (`Frame::ReplayElim`, `value.rs:1730`), and `project(R, 0, Nat(5))`
   panics.

Before eta, step 1 left `R.f ?r` stuck, and `branch` on a `Nat` at type `R`
is just stuck too, so there was no panic. SW-924 is the same shape for
application, and was fixed by checking `can_apply` after `first_order`.
`apart` doesn't help here: a metavariable is never apart from a number. I
haven't built a repro, so confidence is low. The driver and the language
server catch the panic per item, so the cost is a lost declaration with an
internal error, not a crash.

**Fix:** first try for a repro, the way SW-924 was found: unifier
property tests with a record-typed metavariable under a `match` and a
`first_order` pairing at another type. Then either extend `first_order`'s
after-check (undo when a solved metavariable's head constructor isn't of
the type its projections name), or make `ReplayElim`'s mismatch an
internal `Err` rather than a panic (it runs only while elaborating). S to
M, Opus (unifier and core).

### F4. The fuzzers don't exercise eta

`fuzz:kernel` (`crates/core/tests/it/fuzz.rs`) checks that the kernel
never panics on random terms. Its generator has no `Term::Proj` arm, and
`data()` picks `Nat`, `List` or a missing id, none with eta. So
`infer_proj`, `project`, rule 1 and rule 2 never meet a random term. The
soundness fuzzer's corpus has record attempts (proof fields, updates) but
none about eta. record-eta.md §12 lists "the fuzzers … run over records
with and without proof fields" as a mitigation for trusted code growing,
and neither does yet.

**Fix:** add to `fuzz:kernel`'s prelude an eta record with a data field
and a proof field, a proof-only record, and a parameterised `Box`. Add a
`Term::Proj` arm with in-range and out-of-range indices and the wrong
type. Add `fuzz:soundness` attempts that must fail: `(x y: Small) → x = y`
for a proof-only `Small`; a recursive record's eta; `Person` against `Pet`
through the surface; `Box Nat` against `Box Bool`. Running
`fuzz:soundness` takes minutes, so it needs Matt's OK (D2941). M, Sonnet.

### F5. `match` as written stops at a projection

`Finder::agree` (`matching/as_written.rs:690`) compares the as-written
generalisation with the usual one, structure by structure, and has arms
for every form but `Proj` (and `Case`, which can't appear there). So
`Proj(d, i, a)` against `Proj(d, i, b)` with `a` and `b` differing only
where a scrutinee was abstracted gives `false`. The whole as-written
result is then dropped, and `match` falls back to the unfolded test. Goals
hold `Proj` wherever rule 2 has computed (`(down p).column`), so this
switches the as-written stage off on exactly the goals eta changed. It may
be part of what SW-1999 sees. **Fix:** add the arm `(Proj(d1, i1, t1),
Proj(d2, i2, t2)) => d1 == d2 && i1 == i2 && self.agree(g, t1, t2,
under)?`, with a test in which the scrutinee occurs under a projection.
S. Give it to SW-1999's lane, since `match` is core language (Opus,
D2506).

### F6. Where record-eta.md and the code disagree

1. **§6.4 (line 344):** "Not when `x` is an unsolved metavariable (the
   elaborator solves it instead)". The code fires rule 2 on unsolved
   metavariables (`value.rs:1861-1865`, D2511), and record-eta-remaining.md
   §2 relies on that.
2. **§6.2 (line 305):** "on a glued call, force it first". The code keeps
   the projection of a call lazily as a field call (`Frame::ProjOf`,
   `value.rs:1595`, stage 1b) and forces only when something looks.
3. **§8.3 (lines 532-535):** "Not against a value stuck on an unknown".
   `blocked` looks only at `Def`-headed values three calls deep, so a
   field of an unknown (`?b.rows`) isn't counted: SW-1998, whose patch is
   in `docs/repros/sw-1913/`. The note should link it.
4. **§9 (lines 562-564):** "`Proj` compiles to field access". In JS it
   does. The Rust runtime and native code compile it as a `match`
   (`Term::proj_as_match`, beta-reduced to a `let`), which is how SW-1997's
   crash was reached.
5. **§6.1 (lines 290-294) and §12 (lines 654-656):** §6.1's list of
   library types with eta (`Pair`, `Mod`, `SafeNat` …) is stage 3's
   (D2509 holds eta to declared records). §12's fuzzer mitigation isn't
   built (F4).

SW-1913 found a sixth, in §6.4, which its ticket covers.

### F7. `NO_ETA` (confirmed; two tickets for one fix)

`first_order` sets `NO_ETA` with `replace(true)` and puts it back
afterwards. Errors are safe because `same?` is read after the reset.
Panics aren't. `search.rs:1402` catches per candidate and goes on with the
next, and the driver's workers catch per item and keep the thread. After
one panic inside `first_order`, rule 1 stays off in the unifier on that
thread, and checks that need it fail in ways that depend on which thread
ran them. `search::Restore` (`search.rs:916`) already restores other state
when a panic unwinds, and the unifier uses `Scoped::set` elsewhere. Use
it here. SW-1901 and SW-1979 both describe this fix; merge them into one.

### F8. Rule 2 binds every field eagerly

`eta_fields` makes all k fields for every firing: `project` clones and
pushes the neutral's spine each time (a copy when it's shared), and
`project_call` also allocates a cell per field. An accessor opened on an
unknown uses one of them. The prototype measured rule 2 at about 5%, and
record-eta.md §10 suggested binding fields lazily. Cheapest form: note,
per branch body, which of its k fields it mentions (computed once per
tree, like `has_lift_leaf`), and bind the others to `erased()`. Stage 5's
accessor bodies as `Proj` remove the accessor case entirely; this covers
user `match`es too. Worth doing only with stage 3's measurement (pairs and
`Text`), so I'd attach it to SW-1644 as a measured option rather than
start a lane.

### F9. One idea, two representations

A field of a call is a `Value::Call(f, [x, .i], cell)` until it's forced
and found stuck. After that it's `Neutral(Def f, [x, .i])`: "a name for
that projection", which `is_folded` counts as folded so that conversion
unfolds it. Readers must tell these apart from a call and from a stuck
definition. `is_call_field` guards about ten sites (`omega`, `ring`,
`auto`, `dot`, `one_step_apart`, `unify_step`), and `call_args`,
`folded_parts` and readback `unreachable!` if a guard is missed. Each site
I checked is guarded. The risk is the next one. SW-1914's option (b)
would leave one representation. In the same lane, a
`call_parts(spine) -> (args, fields)` helper would replace the
`unreachable!`s.

### F10. Tests worth adding

- **Kernel:** rule 1 in shortcut mode, a constructor's proof field
  compared against the projection (the `Box.unbox (MkBox p)` case in
  record-eta.md §6.5). A record `{ u: UnitType, ok: P }`: two unknowns
  aren't equal (SW-1764 reasoned through this but didn't test it).
- **Unifier:** `?r ≡ { a = ?r.a, b = 3 }` fails by the occurs check and
  doesn't loop (stage 3's brief has this for pairs; records have it now).
  A test showing `NO_ETA` is live (stage 2′ lists it).
- **Surface:** no `examples/accept` or `examples/reject` file is about
  eta: `positionEta := rfl`, `(down p).column = p.column := rfl`,
  proof-only `x = y` rejected. Stage 2′ (SW-1643) lists these. The guide
  and `syntax.md` still don't mention eta, which CLAUDE.md requires for a
  user-visible feature; owed since stage 1.
- **Backends:** a JS test compiling `Proj` (SW-1943 was fixed without
  one, because no source program makes such a projection). The rt test
  SW-1997 added covers the Rust side.
- **Cache:** a direct encode/decode round trip of a term holding
  `Term::Proj`. The cold-against-warm example dumps probably cover it
  through `cases-bool`'s stored proof, but nothing checks that on purpose.
  Low confidence that this is missing.

## Checked and sound

So the next reviewer needn't repeat these:

- **Which types get eta.** `qualifies_for_eta` (`check.rs:2255`) checks
  one constructor, no indices, sort not `Prop`, a group of one, no field
  mentioning the type (syntactically, through `Data`, `Ctor` and `Proj`;
  nothing else can name a pending type), a non-`Prop` field sort, not
  `no_eta`, and `record`. It's computed after `state = Final` in
  `install_data_group`, which both admission paths use. The cache saves
  `record` and `no_eta` (`cache/mod.rs:1618-1621`, `2845`). `mark_no_eta`
  acts only while the type is pending, so `eta` never changes under a
  kept unfolding. Field sorts are concrete, and `proof_field` reads the
  same `field_sorts`.
- **Unit-like types and Agda #2170.** No `Type` value is unit-like by
  conversion. A record whose one data field has a type without eta
  compares that field as two neutrals. `Box a` can't take a proposition
  (exact universes). A field whose type is a function into `Prop` is
  itself `Prop`. #2170's shape (data out of an irrelevant field, or
  irrelevance making every value of a type equal) needs a projection out
  of a `Prop` type or an irrelevance annotation. `infer_proj` refuses the
  first (eta implies `Type`), and Stitchwort has no annotations. I worked
  from the issue's known shape and didn't re-fetch it.
- **Typing of `Proj`.** The type is inferred and forced to `Data(d, ps)`
  with the same `d`. The field index is bounded. Earlier fields are
  substituted as `Proj(d, j, t)`. `project` never takes apart another
  type's constructor.
- **Rule 1** (`value.rs:3158`). It comes after the glued-call arm, the
  folded and field-call arm, numbers and compact lists. Fields go left to
  right; proof fields are skipped in normal mode and compared in shortcut
  mode. It terminates because the constructor side shrinks. The
  reference evaluator has the same rule.
- **Rule 2** (`branch`, `walk_tree`, `reference::eval_tree`, `same_trees`).
  It's off while a program runs and held for natives (`eta_held`, the same
  test in all four). It removes a `case` and adds none.
- **`eta_fields`' preset (SW-1829)** equals `Frame::CallField`'s result
  in every case. It skips a metavariable head and a call that steps at
  once, as `CallField` does; for nested field calls it sets the same named
  neutral; and the `Kept` epoch and modes discard it once something it
  depends on changes. So what a call unfolds to still doesn't depend on
  who forced it first (SW-1782).
- **`Unfolding { kept, base }`.** Fields share the base's cell through
  `base`, each with its own `Kept`. `CallMemo` keys are per cell and keep
  their values alive, so addresses aren't reused. `same_spines` checks
  lengths and pairs projections; a call against its own field can't share
  a type, since the type isn't recursive.
- **Unifier.** The metavariable arms come before rule 1. `ptr::eq(n, &a)`
  is valid because the match is on `(&a, &b)` (`unify.rs:1384`). Nested
  runs don't let waiting pairs escape `NO_ETA`'s scope (`nested` clears
  `waiting`). `same_field_records` compares records of one type `d`, so
  it's lossy (noted as such) but never ill-typed.
- **Consumers of `Proj`.** The hash writes a tag, the data reference, the
  index and the child. The codec encodes and decodes symmetrically, and
  `datas()` reference collection includes it. `dump` prints it. JS gives
  `undefined` for an erased field, `toCanonicalBits` for `Float` (whose
  other field is a proof, so erased), `listOfArray` for `Array` (one
  field), and the value itself for unboxed records. The Rust runtime and
  native code go through `proj_as_match`, which `beta` lowers to a `let`
  (no closure). `Bind::Alias` is never chained (`lower.rs:1142`). Native
  code takes rt's lowered IR, so it inherits both. Termination walks into
  `Proj` and finds no descent, which is conservative; the match is
  exhaustive. Inertness counts it as taking apart. Erasure is by type, and
  `project` passes erased values through while running. `omega`, `ring`,
  `auto` and `dot` guard field calls. `Quot`-headed neutrals with a
  trailing projection read back and rename correctly. The formatter's
  equivalence check is syntactic, and its hash oracle depends only on
  elaboration being deterministic, which `Proj` doesn't change.
- **SW-1997's fix.** The unboxed-record branch binds the field as an
  alias of the scrutinee's level, resolved where it's read. Erased stays
  erased. No other `Bind::Slot` is copied to a new level in `lower.rs`.

## Status of earlier findings in scope

- **The 1 Nov whole-codebase review** (`docs/research/rust-codebase-review.md`)
  predates record eta and has no finding about it.
- **SW-1869's core review:** F1 is partly fixed (the forcing path, by
  SW-1829); conversion and read-back are still open, SW-1914 (F1 here).
  F12 (`CallField` steps the base twice when it matches at once,
  `value.rs:1637-1641`) is still open, in SW-1914. F14 (`admissible`
  skips `Proj`'s data reference) is still open, SW-1888.
- **SW-1764** (stage review): its must-fix (the cache dropping `no_eta`)
  and its small items (hold in the walkers, hold tests, mutual records,
  pending projection) are done (SW-1768), as are its code-quality items
  (SW-1767). Its "update §6.4" item is done (SW-1766), though §6.4 is
  stale again on metavariables (F6).
- **SW-1913's gaps:** SW-1998, SW-1999 and SW-2000 are all still open,
  and F5 may belong to SW-1999.

## Tickets to file

Grouped into lanes. Everything already on the board is cited, not
refiled.

1. **Printers know projections** (Sonnet, 30 min): F2. `record_update`
   and `of_bits` accept `Proj`, with a goal snapshot of an update on an
   unknown record. Needs `snap:examples` for the new snapshot.
2. **Fuzz record eta** (Sonnet, 60 min): F4 and the kernel and unifier
   tests in F10. A `Proj` arm and eta, proof-only and parameterised
   records in `fuzz:kernel`; eta attempts in `fuzz:soundness`'s corpus;
   shortcut-mode rule 1, `{ u: UnitType, ok: P }`, the `?r` occurs case,
   and a direct codec round trip. Running `fuzz:soundness` needs Matt's OK
   (D2941).
3. **Ill-typed projections while elaborating** (Opus, 60 min): F3. Find a
   repro (unifier property test: a record metavariable under a `match`,
   with a `first_order` pairing at another type). Then guard
   `first_order`'s solution or make `ReplayElim`'s mismatch an error.
   Stop and report if there's no repro within 30 minutes.
4. **record-eta.md up to date** (Sonnet, 20 min): F6's five points, with
   links to SW-1998 and D2511.
5. **Add to existing tickets:**
   - SW-1999: F5's `(Proj, Proj)` arm in `as_written::agree`, with its
     test.
   - SW-1914: F9's single representation and a `call_parts` helper.
   - SW-1644: F8 as a measured option.
   - SW-1643 (stage 2′): F10's surface examples, the JS projection test,
     and the guide and `syntax.md` text.
6. **Board tidy** (orchestrator): merge SW-1901's `NO_ETA` item into
   SW-1979, or the reverse (F7).

## Questions for Matt

- **D2940:** Hold stage 3 (`Pair`, `Text`, `Char` eta, SW-1644) until
  SW-1914 (field calls keep their cell) and SW-1998 and SW-1999 (the
  unifier and `match` gaps) have landed? Stage 3 multiplies rule 2's
  firings, and with them every remaining instance of the re-run cost and
  the as-written gaps. **[rec: yes]**
- **D2941:** Allow one background `fuzz:soundness` run (a few minutes)
  once lane 2 has added the eta attempts, as that lane's check?
  **[rec: yes]**
