# Proposal: bounded read-back: the elaborator looks at goals as written and unfolds only what it needs

**Status:** draft 1, 6 November 2026, design only, stopped for Matt's decisions
([§8](#8-decisions), D2519–D2526). Ticket SW-1712, from D2514 (Matt, 6 Nov 2026: "bound
unfolded readback by making the elaborator's searches look at goals as written, starting with
a short design note on Opus that revisits D484; accessor types read back as written too").
Unblocks record eta (SW-1642, SW-1667). Written against `main` at `e0f9d7809` and
`lane/SW-1642` at `c91991954`; all `file:line` citations are `main`'s unless marked
"(branch)". Migration cost (hashes, snapshots, pins, sweeps) is not counted; options are
judged by where they end up.

**Why a note of its own, not a section of goal-as-written.md.** That note is about two
tactics (`rewrite`, `match`) and is decided and mostly built. This one covers every unfolded
read-back in the elaborator: the unifier, implicit arguments, error notes, `decide`, record
accessors and the searches. It revisits D484 as a whole and revives D1280 (goal-readback.md).
goal-as-written.md stays the record of stages 1–4; §4.3 here says what changes in them.

Related notes: [goal-as-written.md](goal-as-written.md) (stages 1–4, SW-1627–SW-1630),
[goal-readback.md](goal-readback.md) (the size cap, D1280, deferred 26 Oct),
[folded-calls.md](folded-calls.md) (glued calls, D483, D484),
[record-eta.md](record-eta.md) (on `lane/SW-1642`; rule 2, §6.4),
[folded-goals.md](folded-goals.md) (SW-742).

Labels:

- **[checked]**: read in this repository at the place given.
- **[cited]**: read in the note or ticket named.
- **[inferred]**: my reasoning from checked or cited facts.

Nothing here was run: this lane was read-and-write only (D2518). Every claim that needs a
measurement says so, and stage 0 ([§7](#7-stages)) makes the measurements.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [Every place that reads back unfolded](#2-every-place-that-reads-back-unfolded)
3. [What was decided before](#3-what-was-decided-before)
4. [The design](#4-the-design)
5. [D484, revisited, and why it is safe](#5-d484-revisited-and-why-it-is-safe)
6. [Accessor types as written](#6-accessor-types-as-written)
7. [Stages](#7-stages)
8. [Decisions](#8-decisions)
9. [What this note did not do](#9-what-this-note-did-not-do)

## 0. Summary

**The problem.** Record eta's rule 2 lets a function that matches on a record compute when
the record is unknown. That's what it's for, but it also works under binders, so
`album => withPhotosOf trip.albums album` or `leg => leg.start + leg.duration` now run deep
into their definitions instead of stopping at the first record pattern. Goals that used to be
small when fully unfolded are now huge. About 290 places in the elaborator read values back
fully unfolded (`value::quote`). Each one builds the whole normal form, up to the
10,000,000-node limit, and then fails with "a value was too large to show". The trip-journal
example project fails this way. Patching the sites one at a time didn't work. Even a site that
recovers from the error has already spent up to ten million steps, so the next site in the
same declaration runs out too.

**The change.** All of these read-backs mean one thing: **the goal unfolded, except that a
call whose own unfolding is too large (100,000 nodes, as D1280 measured) is kept as the
call**. That one thing is never built whole. Each site asks it a question ("where does this
occur?", "does this mention `x`?", "are these the same?", "what is it, if it's small?"). One
shared reader answers by walking the value **as written**. It unfolds a call only when the
answer could depend on what is inside: a call whose arguments don't mention the variables of
what is searched for can't hide it, so it is never opened. Terms the elaborator writes into
its output (record accessors' types, a record update's annotations, `fromYes`'s goal) are read
back folded, as written.

**What it should do.** Below the cap every site gives exactly today's answer, because pruning
only skips calls that can't hold the answer, and the walk keeps today's order. On `main`
today nothing reaches the cap (D1280 measured std, AoC and the roguelike on 26 Oct; stage 0
measures again). Above the cap, where today ends in `E-RESOURCE`, the search sees the call as
written, as Lean always does. Trip-journal's goals stay as their source shows them, and their
searches open only what they need. Accessor types read as their source writes them, so their
hashes move once, and so do the hashes of `Float`'s natives pinned in
`crates/core/src/float.rs:81`.

**Stages.** 0 measure (no change); 1 output terms folded (accessors); 2 the capped read-back
as `Ctx::quote`'s meaning, the semantic change; 3 the lazy reader in the core, which is speed
only and can't change results; then the sites move onto it: 4 "mentions" and zonk, 5 messages,
6 searches, 7 `decide`. Record eta needs 1 and 2 to be correct, and 3 to 6 to be fast enough
on trip-journal; stage 0 says whether 1 and 2 alone are enough to resume SW-1667.

## 1. The problem

### 1.1 What record eta changes

Before record eta, a `case` on an unknown record was stuck. So `merge local remote` on
unknown trips stopped at once, since every one of its helpers starts by taking a record apart
(`local.legs`, `{ album | photos = … }`). The value was a small stuck call, and reading it
back unfolded wrote out that small stuck call. Rule 2 (record-eta.md §6.4; `branch`,
`crates/core/src/value.rs` (branch), the arm `n @ Value::Neutral(..) if eta_case(g, *d)`)
takes the only branch instead, with the fields bound to projections of the scrutinee, "not
while a program runs". **[checked]**

It does this anywhere the elaborator evaluates, including inside a function's body when the
body is read back: the unfolded read-back visits a lambda by applying it to a fresh variable,
and that variable is an unknown record. **[checked: `quote_as`, `value.rs:1974`, visits every
part including function bodies; goal-readback.md §1 found the same]** So with eta, the
unfolded read-back of a goal goes through every helper that takes a record apart, under every
binder. Gluing keeps each helper's call as a call (`project_call`, (branch)), so the goal *as
written* is unchanged: `quote_folded` still writes `withPhotosOf trip.albums album`. Only the
unfolded read-back grows. **[checked: `matches_at_once`, `value.rs:584`, keeps a call whose
case is on a neutral; rule 2 doesn't make it "step at once"]**

### 1.2 The trip-journal shape

`examples/projects/accept/trip-journal` (README.md) proves things about `merge local
remote`, which combines two copies of a journal whose times are `Float`s. Every type in it is
a record (`Trip`, `Leg`, `Album`, `Stop`, `Pin`, `Float` itself, `{ bits, valid }`). A
typical goal, from `Trip/Proofs/Self.sw:141`:

```
rewrite List.mapCongMem trip.albums (album => (withPhotosOf trip.albums album, locate trip.legs album.start))
  (album => (album, locate trip.legs album.start)) (album m => rewrite withPhotosOfSelf trip.albums ids album m in rfl) in
```

As written it is a line of text. Unfolded with eta, every `album =>` body runs:
`withPhotosOf` takes `album` apart (`{ album | photos = … }` becomes a literal of four
projections), and `locate` takes the legs apart and compares `Float`s. `Float.add`
(`crates/elab/src/std/Float/Float.sw:228`) is "stuck until both records are known, so `x + y`
stays as written on unknowns". Under eta, it is no longer stuck on unknowns: it becomes
`Float.ofBits (Float.Model.addBits …)`. **[checked]** The read-back writes each shared value
out at every place it's used (`let`s are inlined), so the size multiplies with every helper
that uses its argument twice. **[inferred: which declaration and which definition first passes
the limit is not established. The SW-1667 lane's report says only "rule 2 computes under
binders, unfolded quote hits 'too large to show'". Stage 0 gets it from the error's own note,
which names the definition (`too_large_notes`, `crates/elab/src/module.rs:677`)]**

### 1.3 Why fixing the sites one at a time didn't work

- **A failed read-back still costs its steps.** `quote_as` calls `budget.step()` for every
  node (`value.rs:1998`) and fails only after `size_limit()` nodes (10,000,000,
  `crates/core/src/budget.rs:109`). An error is "recoverable" only in the sense that the
  declaration may go on (`crates/elab/src/undo.rs:126`). By then it has done ten million
  steps of work. Sites that swallow the error with `.ok()` (most of the message notes, §2.4)
  pay the same. **[checked]**
- **Many sites meet the same value.** One `rewrite` reads back the goal (`rewrite.rs:739`),
  its left side (`:760`), the next goal after each step (`:805`), the motive for the
  completeness check (`rewrite/as_written.rs:416`) and today's instance (`:290`). If it
  fails, its error notes read both sides back again, about ten times (§2.4). Fixing one site
  moves the failure to the next. **[checked]**
- **Stage 4 of goal-as-written.md already recovers in `rewrite` and `match`** (SW-1630: the
  as-written result, with `W-REWRITE-UNCONFIRMED` or `W-MATCH-UNCONFIRMED`). But it is
  reached only after the unfolded read-back has run out, so it pays the ten million steps
  first, and it warns on what, in trip-journal, would be ordinary proofs. **[checked:
  `rewrite.rs:739–751`, `matching.rs:937–946`]**

## 2. Every place that reads back unfolded

`crates/elab/src` has about 290 calls of `quote`, `quote_at_most` or `Ctx::quote`
(`check.rs:648`, which is `quote` at the current level) **[checked: grep, 290 lines]**.
They fall into five kinds by what they need from the term. The tables give the sites the
brief names and the ones I read. Stage 0 classifies the rest, mostly `omega.rs` (42, its own
`Quoter` over atoms, `omega.rs:1951`), `effects.rs` (39, rows), `derive_induct.rs` (31),
`equations.rs` (10, generated equation lemmas) and `interfaces.rs` (11).

For each kind, the question is whether the site needs the unfolded form as such, or whether
the form as written plus unfolding on demand would give the same answer.

### 2.1 Searches: find an occurrence in the normal form

These need the *answer* today's unfolded search gives (which occurrences, which instance),
not the term itself.

| Site | Reads back | Needs |
|---|---|---|
| `rewrite.rs:739`, `:756` (`rewrite_once`) | the goal, forced | occurrences of the left side, by key, then unification |
| `rewrite.rs:760` | the rule's left side | its key and its normal form to compare |
| `rewrite.rs:805` | the goal after each step under a binder | the same, for the next step |
| `rewrite/as_written.rs:288`, `:290`, `:351`, `:471` (`todays_instance`) | the left side and the unfolded goal | the first occurrence in pre-order, so the as-written result picks today's instance |
| `rewrite/as_written.rs:415–416` (`hidden_copy_in`) | the left side and the motive, unfolded | whether any copy is left hidden inside a call kept folded |
| `rewrite/under.rs:353`, `:546`, `:557–558`, `:578`, `:650` | functions' bodies, for rewriting under binders | occurrences that use the binder's variable |
| `rewrite.rs:1918–1919` | the goal and the flipped rule | whether the rule fits the other way round (a message) |
| `matching.rs:933`, `:936` (`generalised_now`) | every variable's type and the goal | syntactic occurrences of the scrutinee's normal form |
| `matching.rs:1414` (`normals`) | the scrutinee, capped at the largest target | its normal form, the needle |
| `matching/as_written.rs:658` (`unfolded`) | the generalised targets, unfolded | which scrutinee variables survive unfolding; agreement with today's generalisation |
| `matching.rs:512`, `:779`, `:1594` | normal forms of hypotheses and the motive | the same occurrence tests and the motive draft |
| `check.rs:1322–1323`, `:1336` (`along_match_equation_now`) | `found`, `expected`, the equation's sides | today's syntactic transport test (SW-1538) |
| `check.rs:1531` | a term with the scrutinee replaced, unfolded | whether it equals the refined one |
| `cases.rs:1246`, `:1284`, `:1301`, `:1330`, `:1566` | stuck values and fields | normal forms used as keys for "seen" and "known" sets: an equality test |

None of them needs the whole normal form. They need: candidates with the needle's key, in
today's order, each compared as today; and, for the completeness checks, the certainty that
no other candidate exists. **[inferred]**

### 2.2 Mentions: does the normal form mention a variable or an unknown?

| Site | Question | Today's direction if it can't read back |
|---|---|---|
| `check.rs:3889` (`ignorable_arguments`, for every `auto` implicit argument; reads the goal and **every** variable's type) | which variables a proof's unknown may ignore | gives up (`None`): nothing ignorable |
| `unify.rs:177` (`on_pending`), `unify.rs:978` (`mentions_unknown`) | mentions a pending or any unknown | already capped (`KNOWN_CAP`, 4,096, `unify.rs:973`): "too large" counts as "may" |
| `bind.rs:95`, `:99` | the result type mentions the bound variable | refuses (`None`) |
| `matching.rs:434` | the goal mentions an index | error |
| `lib.rs:4954` | a default's goal or a later type mentions a variable | `false` |
| `rewrite.rs:707`, `rewrite.rs:1690` (`mentions_draft`), `matching.rs:1685` (`first_meta`), `cases.rs:1582` (`has_meta`) | a premise or type mentions an unknown or a draft | error |

They need one bit, exactly. The as-written form gives an over-approximation: the free
variables of a call's unfolding are among those of its arguments, but the reverse fails
(`keep a b := a` drops `b`). So the as-written form alone is safe only where "mentions" is
the conservative answer (`check.rs:3889`: fewer ignorable arguments), and wrong where
"doesn't mention" is what lets the elaborator go on (`bind.rs:95`). **[inferred]**

### 2.3 Zonk

| Site | What | Needs |
|---|---|---|
| `unify.rs:2777–2780` (`zonk_changed`, a meta-headed term) | the solution read back folded; **if any call's arguments mention an unsolved unknown, the whole solution read back unfolded** | only those calls unfolded: the unknown may vanish in their unfolding |
| `unify.rs:2597` (`both_forms`), called at `unify.rs:2791` under `cheaply` (10,000 nodes, `unify.rs:2566`) | a `let`'s value, folded and unfolded, for `refold` | already bounded; the unfolded form is there because "a decision's solution is found on the unfolded goal (D484)" |

`unify.rs:2779` is the brief's "unifier's zonk". It is all-or-nothing: one call holding an
unsolved unknown sends the whole solution through `quote`. **[checked]**

### 2.4 Messages: notes on an error

All of these run on the error path, but an error built inside an attempt that is then undone
pays for them too. Most read both sides back unfolded and ignore failure:

`check.rs:772` (opaque notes), `:798`, `:816` (equation notes), `:864`, `:880`
(`differ_only_in_hidden`, `differ_only_in_proofs`), `:894` (`first_difference_note`, unfolded
for display), `:921` (`with_alike_updates_note`), `:1170` (`unrefined_hint`), `:6967`
(`same_function`), `:6995` (`match_equation_note`), `:7105` (branch notes); `rewrite.rs:1759`
(`shown_computed`), `:2101` (opaque notes), `:2113`, `:2127` (`hypothesis_holding`, every
variable's type). **[checked]**

They need the normal form, but only when it is small enough to be worth showing. A note
about a value of a million nodes helps nobody. **[inferred]**

### 2.5 Output terms: written into what the elaborator produces

| Site | Term |
|---|---|
| `shared.rs:246` (`accessors`) | **each record accessor's result type** |
| `shared.rs:600`, `:633`, `:644`; `records.rs:1448`, `:1470`, `:1543` | a record update's `let` types, annotations and parameters |
| `auto.rs:352` (`from_yes`) | the goal in `fromYes [p := goal] decision Trivial` |
| `bind.rs:108`, `named.rs:726–727`, `:895` | binder types of elaborated lambdas |
| `lib.rs:956`, `:1036`, `:1080`, `:1375` | types of a checked input, a goal hole's target |
| `matching.rs:521`, `:657`, `:851` | scrutinee types in the motive |
| `rewrite.rs:1605`, `check.rs:4980` | carrier and type terms handed to the kernel's inference |

The kernel checks every one of these up to conversion. A folded term is convertible to the
unfolded one and smaller (folded-calls.md stage 3 moved the others: "for terms the
elaboration produces, such as annotations and helper types", `check.rs:651–653`). So nothing
needs the unfolded form here. It changes hashes only. **[checked; inferred for "nothing
needs it": stage 1 checks it]**

### 2.6 `decide` (D484 itself)

`auto.rs:783–795`: "The search sees the unfolded proposition (D484 …): it runs with gluing
off, on `prop` read back and computed again unglued." It needs the whole proposition as a
term, unfolded, because it re-evaluates it with gluing off. `decide_as_written`
(`auto.rs:366`) is already the fallback when that decision is stuck. **[checked]**

### 2.7 The kernel

The kernel already reads back as written where it matters (`quote_kept` in `check_case`,
`crates/core/src/check.rs:923`, and `substitute`, `:1266`, `:1346`, `:1373`). That was
goal-readback.md §6's kernel finding, since fixed. One unfolded read-back is left,
`core/src/check.rs:378`. It is out of scope here unless stage 0 finds trip-journal reaching
it. **[checked]**

## 3. What was decided before

- **D484** (folded-calls.md, Oct 2026): "`rewrite` and the decision search see … the unfolded
  goal, as today, so every existing proof keeps working". The reason was no regressions, not
  that the unfolded form is better. Since then D484 has been narrowed twice. Stage 3 of
  folded-calls.md moved output terms, zonk and messages to folded read-back, "keeping the
  unfolded one for `rewrite`'s search, `refold` and `unify_index`'s occurs check"
  (folded-calls.md, stage 2's "Next"). goal-as-written.md (D2475–D2480) made `rewrite`,
  `match`, `cases` and the transport look as written first, keeping today's result as the
  check and the fallback. **[cited]**
- **D1280** (goal-readback.md §5, 26 Oct, deferred by Matt): "`rewrite` and `match e:` see
  the unfolded goal, except that a call whose unfolding would take more than 100,000 nodes to
  write out is left as the call". Measured then: at 100,000, **nothing in std, AoC or the
  roguelike is kept folded** and times don't move, but at 10,000 one AoC proof breaks
  (`Year2025/Day08/Proofs/Part2.sw:287`). Its two lessons apply here. First, a rule that
  cuts by *position* (inside a stuck `if`, under a binder) breaks proofs, because the needle,
  read on its own, then reads differently from its copy in the goal. Second, a shared budget
  whose exhaustion decides which call is kept "breaks the repro: which call is kept then
  depends on where the budget ran out". The kept call must be a function of the call alone.
  Its cost, measured: each kept call wastes up to 100,000 nodes of read-back each time it is
  met (rogue2q 18.7 s against 2.9 s), so it proposed a cache. **[cited]**
- **goal-readback.md option (a), `look`:** folded, unfolding a call when its one-level
  unfolding contains the target. Broke `std/List/Toolkit.sw`, because a target two calls deep
  was missed, "and a deeper one is a full unfolding again". **[cited]** §4.2 is a deeper
  look that is *not* a full unfolding, because it opens only calls that could hold the
  target.
- **The lessons of goal-as-written.md's reviews:** agree with today's choice of instance; no
  extra copies; undo every failed attempt; errors fall back; kernel-checked motives. **[cited]**
  §4 keeps each.

## 4. The design

### 4.1 One meaning for "unfolded": the capped normal form

Every unfolded read-back in the elaborator means the same thing from now on:

> **The capped normal form** of a value: its normal form (as `quote` gives today), except
> that a glued call whose own unfolding would read back to more than `CAP` nodes is written as
> the call, its arguments read back by the same rule. A call that steps at once by matching
> (`matches_at_once`) is never kept. `CAP` is 100,000 (D1280), a field of `Limits`.

That is D1280's `quote_search`, extended from `rewrite` and `match` to every site in §2.1–§2.4.
Whether a call is kept depends only on the call (its definition and its arguments), so a
needle and its copy in the goal read back alike wherever they sit. That is D1280's
consistency property, and the reason it worked where cutting by position didn't. "Would read
back to more than `CAP`" is computed with `quote_at_most`'s cap (`value.rs:1917`) on the
call's unfolding alone, and the answer is cached per declaration by the call's cell, as D1280
proposed.

The capped normal form is a *definition*. It doesn't have to be built.

### 4.2 The reader: asking the capped normal form a question without building it

One module in `crates/core` (`readback.rs`, next to `quote_as`) answers the questions the
sites ask, by walking the value **as written** (as `quote_folded` does) and unfolding a call
only when the answer could depend on what is inside it:

- **`find(value, needle)`**: the occurrences of `needle` in the capped normal form, in
  pre-order, each handed to the site's own comparison (a key match, then `same` or
  unification, as today).
- **`mentions(value, vars, metas)`**: whether the capped normal form mentions any of these
  variables or unknowns.
- **`unfold_where(value, pred)`**: the term read back folded, except that the calls `pred`
  picks are unfolded (by the same rule, recursively). This is for zonk: the calls whose
  arguments mention an unsolved unknown.
- **`small(value, cap)`**: the capped normal form, if it is at most `cap` nodes in all, else
  `None`. This is for messages and `decide`.

**When a call can be skipped.** For a glued call `f a₁ … aₙ` (or a closure, which is a body
and an environment):

1. **Free variables.** Every variable and unknown free in the call's normal form is free in
   some argument (with solved unknowns replaced, as `force_solved` does), because `f` is a
   closed definition. So if the needle mentions a variable or unknown that no argument
   mentions, no occurrence of the needle can be inside, and the call is read as written. The
   same goes for `mentions`: if no argument mentions `x`, the call's normal form doesn't. If
   one does, the call is unfolded one step (`unfold_once`, `value.rs:570`, which keeps the
   calls it returns as calls) and the walk goes on inside. **[inferred: the substitution
   lemma; it holds for the elaborator's evaluator because definitions are closed terms and
   unknowns are applied to the variables they may use (`fresh_meta`, `check.rs:959`)]**
2. **Heads, optional.** For a needle whose key is a definition `h`, an occurrence inside
   `f a⃗` has its head either from `f`'s body or from an argument. So if `h` is not
   reachable from `f`'s body or from the definitions the arguments mention, the call can be
   skipped. Reachability is a fact about definitions, computed once per definition and
   cached. It helps when the needle's variables are everywhere (a needle about `trip` in a
   goal about `trip`). It's an optimisation, so stage 3 measures whether it pays for itself.
3. **The cap.** A call whose unfolding is over `CAP` is read as written: that is §4.1's
   definition, not a heuristic of the reader.

Under these rules the reader opens exactly the calls whose unfolding could change the answer,
in the order the full read-back would visit them, so **its answer equals the answer from the
capped normal form built whole**. Below the cap, that is today's answer. **[inferred; stage 3
tests it as a property: on random and real values, every question answered both ways]**

Why this bounds trip-journal: a needle like `List.appendNewBy entries entries (…)`
(`Self.sw:78`) doesn't occur in the `album =>` bodies' helpers, and `appendNewBy` isn't
reachable from `withPhotosOf` or `locate`. So those calls are never opened, however large
their unfolding. A needle that mentions only `trip`, in a goal where everything mentions
`trip`, is where rule 2 opens much and the cap does the bounding. **[inferred: stage 0
measures how much is opened]**

**Undo.** The reader only reads. It solves no unknown, and the comparisons it hands
candidates to are the sites' own, inside the snapshots they already take (`hidden_copy`,
`rewrite/as_written.rs:390`; `todays_instance`, `:448`). "Undo every failed attempt" holds as
it does now. **[checked]**

### 4.3 Each site

| Kind (§2) | Today | With this design |
|---|---|---|
| **Searches** (§2.1) | read back whole, search the term | `rewrite`, `match`, `cases` and the transport keep their as-written search first (goal-as-written.md stages 1–3). The **completeness check** (`hidden_copy_in`), **today's instance** (`todays_instance`), the survival and agreement checks (`matching/as_written.rs:649–690`) and the fallback search all use `find` on the capped normal form instead of a whole read-back. The fallback search itself (today's search when the as-written one finds nothing or is incomplete) runs on `find` too. `cases`' seen and known sets (`cases.rs:1246–1566`) compare by `conv_now` (`check.rs:676`) rather than by equal normal forms. |
| **Mentions** (§2.2) | read back whole, look | `mentions`: exact, in both directions, so `bind.rs:95` stays as permissive as today. `KNOWN_CAP`'s "too large means may" (`unify.rs:978`) is no longer needed, but keeping it is harmless. |
| **Zonk** (§2.3) | `unify.rs:2779` re-reads the whole solution unfolded | `unfold_where(solution, args mention an unsolved unknown not kept)`: the same term today's fallback writes for those calls, folded everywhere else. `both_forms` (`unify.rs:2597`) is unchanged (already bounded). |
| **Messages** (§2.4) | each note reads both sides back | each side is read once per error, as `small(value, NOTE_CAP)` (10,000 nodes, as `cheaply`), shared by every note through a cache on the error being built. A note whose side is too large is left out, as an `Err` from `quote` leaves it out today. |
| **Output terms** (§2.5) | `quote` | `quote_folded`. Hashes move (§6). |
| **`decide`** (§2.6) | `quote` of the whole proposition, re-evaluated unglued | `small(prop, CAP)`, then today's search unchanged. If it's too large, `decide_as_written` (already there, `auto.rs:366`), and `from_yes` with the goal folded. See D2522. |

Stage 4 of goal-as-written.md (the "unconfirmed" paths) becomes the case where the cap kept
a call: the search ran on the capped normal form, which is a complete answer by §4.1's
definition. So there is nothing left unconfirmed to warn about, and
`W-REWRITE-UNCONFIRMED`/`W-MATCH-UNCONFIRMED` go. D1280's message note takes their place, on
failure only: "`f a b` was left as it is: its unfolding is larger than 100,000 nodes". See
D2521.

## 5. D484, revisited, and why it is safe

**What D484 becomes.** "The elaborator's searches look at the goal as written first. Where
they need what a call computes to, they look inside that call only, and never inside a call
whose unfolding is larger than 100,000 nodes. Below that size, what they find is what they
found by unfolding the whole goal." D484's promise ("every existing proof keeps working")
is kept wherever no call in the proof is that large.

**Soundness.** Nothing here touches the kernel's rules. Every motive is still type-checked
(`check_motive`, `rewrite.rs:1585`, `matching.rs:1587`), every term the elaborator writes is
still checked by the kernel, and a folded and an unfolded term are convertible. A wrong
answer from the reader could make a proof fail or pick a different (still checked) term, but
it can't make a false statement check. **[inferred, as goal-as-written.md §4]**

**Completeness and agreement with today.** Three properties, each tested in its stage:

1. *The reader is exact.* For every question, `find`/`mentions`/`unfold_where`/`small` give
   the answer the capped normal form built whole gives: same occurrences, same order, same
   bit (§4.2's skipping rules skip only what can't matter). So "agree with today's choice of
   instance" holds: the first occurrence in pre-order is the same one. "No extra copies"
   holds too: the completeness check sees exactly the copies today's search would replace.
2. *Below the cap, the capped normal form is the normal form.* By definition.
3. *On `main` nothing reaches the cap.* D1280 measured this on 26 Oct. AoC 2020's days were
   added since, so stage 0 measures again: the largest single-call unfolding met by any
   unfolded read-back over std, AoC, the roguelike and the examples. The margin D1280 found
   was real: at 10,000 one AoC proof broke, at 100,000 none.

With these, a proof that checks today on `main` checks the same way, with the same terms,
except that the output terms of §2.5 are folded (§6). The behaviour changes only where some
call's unfolding exceeds the cap: today such a goal either fails with `E-RESOURCE` (above
10,000,000 in all) or succeeds slowly between the two bounds. The second case is the
regression risk, the same one D1280 accepted. **[inferred]**

**What doesn't come back.** Lean's rule (rewrite only what is visible) stays rejected for
calls below the cap: the completeness check still reaches into hidden copies (days 10 and 14,
`Result.traverseCons`, `List.foldMaxMem`; goal-as-written.md Q4).

**Time.** On `main`, the reader opens a subset of what today's read-back builds, so it should
be faster than today wherever it replaces a whole read-back. The catch is each cap test,
which costs up to `CAP` nodes per large call, once per declaration with the cache.
**[inferred; stage 3 measures std, AoC and the roguelike, within the test budget agreed for
it]**

## 6. Accessor types as written

**What changes.** `accessors` (`shared.rs:227`) declares each record field's accessor
`T.f : [params] → (r: T params) → F` and reads `F` back with `quote` (`shared.rs:246`). So
today an accessor's type is the field's declared type **computed to its normal form**, with
the earlier fields as accessors of `r`. With `quote_folded` it is the type as declared.
Examples **[checked in the declarations; the normal forms are my reading]**:

- `Float.valid : (r: Float) → Float.isValid r.bits = True`. Today it is the normal form of
  `Float.isValid`, the disjunction of `Nat.leq` tests on `r.bits`
  (`Float/Float.sw:34–36`).
- `Trip.Model.WellFormed.pinsFit : (trip: Trip) → (w: WellFormed trip) → List.All (pin =>
  pinFits trip.legs pin = True) trip.pins` (`Trip/Model.sw:168`). Today the lambda's body
  is computed. With eta, `pinFits trip.legs pin` runs through `firstCovering` and `Float.leq`
  on `pin.start` under the binder, which is where an accessor's type alone can reach the
  limit.

**For users.** The type of `w.pinsFit` shows as written, in hovers, in goals that list it,
and in "this has type …" messages. A `rewrite … at w.pinsFit` finds what the user wrote
as-written first (goal-as-written.md), with today's search as the fallback, so proofs that
rewrote inside the computed form still work. **[inferred]** Nothing else changes: the
accessor's body (a `case` on `r`) is untouched, and for eta records the elaborator emits
`Proj` for `r.f` anyway (record-eta.md §6.4). **[cited]**

**In hashes.** An accessor's content hash covers its type, so every accessor whose field type
contains a call that computes gets a new hash, and so does everything that mentions it.
**[checked that hashes cover the type: `def_hash` hashes `def.ty`, `crates/core/src/hash.rs:105`; inferred that dependents move, as for any definition]**
Concretely:

- **Float pins.** `NATIVE_HASHES` (`crates/core/src/float.rs:81`) pins the content hash of
  each definition with a native. The natives' bindings check it (`float.rs:742–757`, "its
  content hash isn't the pinned one"). `Float.neg`, `Float.abs`, `Float.sub` and others use
  `x.valid` (`Float.sw:200`, …), so their pins move in the same commit, as they already moved
  once on `lane/SW-1642` (`float.rs` diff, FloatNeg, FloatAbs, FloatSub). `FLOAT_DATA_HASH` is
  the data type's and doesn't move. The `*_bound_to_the_prelude` tests
  (`crates/cli/tests/extract.rs:3198–3243`) and the float gate (`crates/driver/src/float_gate.rs`)
  are the checks. **[checked]**
- **Snapshots.** `hash_stability` snapshots move for every example with a record whose field
  types compute. A record update's annotations (`shared.rs:600–644`, `records.rs:1448–1543`)
  move the same way. Not a cost (migration cost doesn't count), but the stage's lane
  re-records them.

**A check for the stage:** whether gluing is on when `accessors` runs. If it isn't,
`quote_folded` is `quote` (`value.rs:1924`: "Without gluing … this is `quote`"), and the
field type must be evaluated with gluing on first. Data declarations are elaborated inside
`check_component`, which runs under `glued` (`module.rs:404`), so I expect it is on.
**[inferred]**

## 7. Stages

Each stage is one lane, merged to `main` on its own. Stages 2 to 7 change nothing on `main`
by §5's argument, and each says how that is checked. Stages that change elaborated terms or
search behaviour get an Opus review (D2364). Estimates are guesses from similar lanes (the
goal-as-written stages took about 120 min each).

0. **Measure (no behaviour change).** A counter under an environment variable
   (`STITCHWORT_READBACK_METRICS`, as `STITCHWORT_MATCH_METRICS`): for every unfolded
   read-back, its site and node count, and the largest single-call unfolding met. Run over
   std and trip-journal on `main` and on `lane/SW-1642`, and AoC, the roguelike and the
   examples on `main` (needs the test exception, D2524). Also the classification of the
   remaining ~200 sites into §2's kinds, as a table appended to this note. Out: the trip-journal
   declarations and definitions that pass the limit, and the largest unfolding on `main` (is
   100,000 still safe?). Sonnet, 60 min. *Risk:* none to behaviour.
1. **Output terms folded (§2.5, §6).** `shared.rs:246` and the rest of §2.5's table to
   `quote_folded`. Float pins, hash snapshots and the bound-to-the-prelude tests updated.
   Accept: the accessor types print as declared (a snapshot of `Float.valid`'s and of a
   dependent field's type); std, the float gate and the examples' hash snapshots re-recorded.
   **Record eta needs this.** Sonnet, Opus review (kernel terms change); 60 min. *Risk:* a
   proof that relied on an accessor's type being in normal form for a syntactic test.
   goal-as-written.md's fallbacks should cover that; the AoC check at merge shows it.
2. **The capped normal form (§4.1), built whole.** `quote_capped` in `value.rs` (D1280's
   `quote_search`: the per-call cap, the cache per declaration, never keeping a call that
   steps at once). `Ctx::quote` and the free `quote` calls in §2.1–§2.4 use it. No laziness
   yet. On `main` nothing changes (stage 0's measurement says nothing reaches the cap). Unit
   tests as goal-readback.md §7. Accept: D1280's repro (`grow x 40`) and trip-journal on
   `lane/SW-1642` get past the elaborator, slowly at worst. **Record eta needs this for
   correctness.** Opus (core read-back), 90 min. *Risk:* time, measured by D1280 at 6× on
   rogue2q before its cache. If trip-journal is too slow at this stage, it waits for 3–6.
3. **The reader (§4.2).** `readback.rs`: `find`, `mentions`, `unfold_where`, `small`, with
   the free-variable rule, the cap, and the head rule if it pays. Tests: a property test that
   each question gives the same answer as on `quote_capped`'s term, over
   `crates/core/tests/glue.rs`-style values and over every read-back of std under a debug
   switch that runs both and panics on a difference. Opus, 150 min. *Risk:* a mistake in
   the skipping rule. That would be a missed occurrence, never unsoundness, and the
   both-ways debug switch is there to catch it.
4. **Mentions and zonk onto the reader** (§2.2, §2.3): `check.rs:3889`, `bind.rs:95/99`,
   `matching.rs:434`, `lib.rs:4954`, `rewrite.rs:707/1690`, `matching.rs:1685`,
   `cases.rs:1582`, `unify.rs:978/177`; `unify.rs:2779` to `unfold_where`. Accept: the SW-323
   tests (`ignorable`), zonk's tests in `unify.rs`. Sonnet, Opus review, 60 min.
5. **Messages onto `small`** (§2.4), with one read-back per side per error. Accept: the
   E-REFL and E-TYPE-MISMATCH snapshot tests unchanged. Sonnet or DeepSeek, 45 min. *Risk:*
   a note lost where a side was between 10,000 and 10,000,000 nodes. Acceptable: such a note
   is unreadable anyway.
6. **Searches onto `find`** (§2.1): the completeness checks, today's instance, the
   survival and agreement checks, the fallback searches, `rewrite/under.rs`, the transport,
   `cases`. Stage 4's unconfirmed paths and warnings removed, with D1280's note in their
   place (D2521). Accept: goal-as-written.md's accept examples unchanged
   (`examples/accept/match-equation-as-written.sw`, the stage 1–2 repros),
   `examples/reject/as-written-unconfirmed-slow-check.sw` rewritten for the note, and day
   11's `settledExactly` still checking. Opus (motives and instance choice), 150 min; could
   be split into `rewrite` (6a) and `match`/`cases`/transport (6b). *Risk:* the largest
   stage. Mitigated by stage 3's both-ways switch, run here over std, AoC and the roguelike
   once (D2524).
7. **`decide`** (§2.6, D2522). `small(prop, CAP)`, else `decide_as_written` and a folded
   `from_yes`. Accept: `examples/accept/and-or-not.sw` keeps `Nat.decLessEq y 9` (today's
   choice). Sonnet, 30 min.

Then: SW-1667 rebases onto `main` and goes on (trip-journal, `a_namespace_checked_alone_has_the_same_hashes`).
folded-calls.md's D484 entry and goal-as-written.md's stage 4 get a line pointing here.
`docs/syntax.md` ("rewrite", "Generalised `match`") says that a call larger than the cap is
looked at as written. That is a user-visible rule, so the language guide's proofs chapter
says it too (stage 6's lane).

**What record eta needs first.** Stages 1 and 2 make trip-journal *correct* (no
"too large to show"). Stages 3 to 6 make it *fast*. Whether 1 and 2 are enough to resume
SW-1667 is stage 0's answer: if trip-journal under stage 2 takes more than about twice its
time on `main`, SW-1667 waits for stage 6. See D2525.

## 8. Decisions

- **D2519.** Make every unfolded read-back in the elaborator (§2.1–§2.4) mean the **capped
  normal form**: today's unfolded form, except that a call whose own unfolding is over
  100,000 nodes is kept as the call. This revives D1280, deferred on 26 Oct, and extends it
  from `rewrite`/`match` to every site; it is how D2514's "unfold only what's needed" is
  bounded. [rec: yes. It is a function of the call alone, so needles and goals read alike.
  At 100,000 nothing on `main` was kept when D1280 measured it, and stage 0 checks again.]
- **D2520.** Answer the sites' questions with **one shared reader** that walks the goal as
  written and opens a call only when what is asked about could be inside (its arguments
  mention the needle's variables, and optionally its definition can reach the needle's
  head), with the rule that its answers equal those on the capped normal form built whole,
  tested both ways. [rec: yes. It is what makes "look as written, unfold only what's needed"
  exact rather than a heuristic, unlike goal-readback.md's one-level `look`.]
- **D2521.** Remove stage 4's `W-REWRITE-UNCONFIRMED` and `W-MATCH-UNCONFIRMED` once
  searches run on the capped normal form (stage 6). In their place, a note on a *failure*
  only: "`f a b` was left as it is: its unfolding is larger than 100,000 nodes". [rec: yes.
  The result is no longer unconfirmed: it is the complete answer under the new rule, and
  in trip-journal-like code the warnings would fire on ordinary proofs.]
- **D2522.** `decide` keeps D484 where the proposition is small enough: today's unfolded,
  unglued search when the proposition's capped normal form is at most 100,000 nodes in all,
  else the as-written decision (`decide_as_written`). Not as written first, which would
  change the decisions made today (`y < 10` by `Nat.decLessThan y 10` rather than
  `Nat.decLessEq y 9`, folded-calls.md) and the programs that run them. [rec: yes;
  as-written first only if a proof needs it.]
- **D2523.** Read back folded **all** the output terms of §2.5, not only accessor types
  (D2514): a record update's annotations, `fromYes`'s goal, elaborated binder types,
  scrutinee types in motives, kernel inference inputs. Hashes and Float pins move in stage 1.
  [rec: yes. Same reason as accessors, the same stage, and one hash churn instead of several.]
- **D2524.** Test strategy for stages 0, 3 and 6, as an exception to the lane test budget:
  each runs one check of std, AoC, the roguelike and the examples in the background, with the
  both-ways switch or the metrics on, stopped at 6 minutes as D2507's verifier is. [rec: yes.
  §5's "nothing changes on `main`" is a measured claim, and these are the stages that rest
  on it.]
- **D2525.** Order: 0, 1, 2 first; SW-1667 resumes after stage 2 if trip-journal then takes
  at most twice its time on `main`, else after stage 6; stages 3 to 7 continue on `main` in
  any case. [rec: yes. Record eta needs correctness first, and the speed stages can't change
  results.]
- **D2526.** `CAP` stays fixed at 100,000 with no per-proof syntax to lift it (D1281,
  deferred with D1280). [rec: yes, until a proof needs more. `rewrite f` (goal-as-written.md
  Q6) or `f.unfold` is the way into a large call.]

## 9. What this note did not do

- It ran nothing (D2518). The size of trip-journal's read-backs, the definition that first
  passes the limit, the largest unfolding on `main` today, and the reader's speed are all
  stage 0's or stage 3's measurements.
- It classified about 90 of the 290 unfolded read-back sites by reading them. The rest,
  mostly `omega.rs`, `effects.rs`, `derive_induct.rs`, `equations.rs` and `interfaces.rs`,
  are classified in stage 0. Of these, `equations.rs`'s generated equation lemmas are the
  ones to treat with care: their statements are what `rewrite` later searches with, so
  reading them back folded would change proofs, unlike §2.5's terms.
- It doesn't revisit record eta's rule 2 itself (for instance, not firing under binders in
  the elaborator). D2514 chose to bound the read-backs instead.
