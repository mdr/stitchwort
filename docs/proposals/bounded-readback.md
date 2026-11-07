# Proposal: bounded read-back: the elaborator looks at goals as written and unfolds only what it needs

**Revision 3** (SW-1728, 6 Nov 2026), for the direction Matt chose after the strategy review
([SW-1726](../reviews/SW-1726-unfolding-strategy.md)): computing decides, searches act on
what is visible, limits fail (D2541–D2545). What changed: the capped normal form (revision
2's §4.1, stage 2) is deferred, with D2519, D2529 and D2533 ([§9](#9-deferred-the-cap)); the
reader has no exact-agreement contract and starts in stage 4 (D2520 narrowed); the
completeness checks and both "unconfirmed" warnings go (D2542, replacing D2534); a plan for
the proofs D2542 breaks ([§8](#8-the-proof-migration-d2542)); `rewrite f` (D1433) joins the
plan; stages re-planned and re-estimated ([§7](#7-stages)); D2539 is moot; two new questions,
D2548 and D2549 ([§10](#10-decisions)).

*Revision 2* (SW-1722, 6 Nov 2026) answered the review
([SW-1717](../reviews/SW-1717-bounded-readback-review.md)) and the comparative study
([SW-1718](../reviews/SW-1718-unfolding-comparison.md)): the reader prunes by the needle's
relevant variables (H1); the cap became recursive under fixed limits (H2, M4); stage 0 measures
on `lane/SW-1642` too (H4); `decide` reads back folded (M3); messages elide with `⋯` (S2); the
reader memoises negative answers (S4). Its cap and agreement machinery are what revision 3
drops.

**Status:** draft 3, design only. Its direction is decided ([Decided](#decided)); D2548 and
D2549 are decided yes (Matt, 6 Nov 2026). Ticket SW-1712, from D2514 (Matt, 6 Nov 2026:
"bound unfolded readback by making the elaborator's searches look at goals as written,
starting with a short design note on Opus that revisits D484; accessor types read back as
written too"). Unblocks record eta (SW-1642, SW-1667). Revision 3 was written against `main`
at `2991bb684`; its new citations (the seven declarations of §8) were checked there. All other
`file:line` citations are from revision 2 (`main` at `0d0e12b79`) unless marked "(branch)":
nothing under `crates/` that they cite was re-read for revision 3. Migration cost (hashes,
snapshots, pins, sweeps, the proofs of §8) is not counted; options are judged by where they
end up.

**The remaining work** (stages 0c to 7 after stages 0a, 0b, 1 and 1b merged, with record
eta on `main`) is planned in [bounded-readback-remaining.md](bounded-readback-remaining.md)
(SW-1828, 7 Nov 2026). It also corrects §2.5 and §4.2 below, and reads two of §4.4's limits
as exact.

**Why a note of its own, not a section of goal-as-written.md.** That note is about two
tactics (`rewrite`, `match`), and its stages 1–4 are built. This one covers every unfolded
read-back in the elaborator: the unifier, implicit arguments, error notes, `decide`, record
accessors and the searches. goal-as-written.md stays the record of its stages; it now records
Q4 reversed by D2542 and points here for what changes in them (§4.3).

Related notes: [goal-as-written.md](goal-as-written.md) (stages 1–4, SW-1627–SW-1630),
[goal-readback.md](goal-readback.md) (the size cap, D1280, deferred 26 Oct),
[folded-calls.md](folded-calls.md) (glued calls, D483, D484),
[record-eta.md](record-eta.md) (on `lane/SW-1642`; rule 2, §6.4),
[folded-goals.md](folded-goals.md) (SW-742). Reviews:
[SW-1717](../reviews/SW-1717-bounded-readback-review.md) (findings H1–H4, M1–M6, L1–L5),
[SW-1718](../reviews/SW-1718-unfolding-comparison.md) (suggestions S1–S8),
[SW-1726](../reviews/SW-1726-unfolding-strategy.md) (the strategy, options (a)–(e)).

Labels:

- **[checked]**: read in this repository at the place given.
- **[cited]**: read in the note or ticket named.
- **[inferred]**: my reasoning from checked or cited facts.

Nothing here was run: all three lanes were read-and-write only (D2518, SW-1722, SW-1728).
Every claim that needs a measurement says so, and stages 0a and 0c make the measurements.

## Decided

Matt, 6 Nov 2026, taking the strategy review's recommendation:

- **D2541, yes.** Computing stays the way to *decide*: conversion, `rfl`, `decide`,
  `byDecision`, `cases`, tests and the counterexample search. No Lean-style transparency
  system and no `simp`. D484's clause that the elaborator's *searches* see the goal fully
  computed is retired.
- **D2542, yes.** Searches rewrite only what is visible: Lean's rule, option B of
  goal-as-written.md, reversing its Q4. `rewrite`, `match`, `cases`' generalisation and the
  transport use the as-written occurrences whenever there are any, with no completeness check,
  and look inside definitions only when nothing is visible. The proofs this breaks (seven
  measured: two in std, five in AoC) are rewritten (§8). `W-REWRITE-UNCONFIRMED` and
  `W-MATCH-UNCONFIRMED` go. E-REFL gets a note when a rewrite left a copy inside a call.
  Replaces D2534.
- **D2543, yes.** Limits fail with a message naming the call, and never switch to another
  answer. No size cap for now: D2519, D2529 and D2533 are deferred (§9).
- **D2544, yes.** Stage 0a tries record eta's rule 2 switched off in the read-backs that
  searches use, on `lane/SW-1642`.
- **D2545, yes.** Order: 0a; then 1, 0b, 4 and 5; then D1433; then 3, 6a and 6b. SW-1667
  resumes once the kinds of site 0a finds failing have moved. Amends D2537.
- **D1433, yes** (by D2545). `rewrite f`: a rule naming a definition means one step of it.

Revision 2's questions, as they now stand:

| Decision | Now | Where |
|---|---|---|
| D2519 (capped normal form) | deferred | §9 |
| D2520 (one shared reader) | **yes, narrowed**: no exact-agreement contract | §4.2 |
| D2523 (output terms folded) | **yes** | §2.5, stage 1 |
| D2529 (`CAP` fixed, no escape) | deferred; the escape is D1433 | §9 |
| D2533 (the cap's definition) | deferred | §9 |
| D2534 (unconfirmed removed where the cap kept a call) | replaced by D2542 | §4.3 |
| D2535 (`decide` folded, evaluated unglued) | **yes** | §2.6, stage 1 |
| D2536 (test strategy exception) | **yes**, for the stages it names that remain (0c, 3, 6a, 6b) | §7 |
| D2537 (order) | amended by D2545 | §7 |
| D2538 (motives from opened calls) | **yes** | §4.3 |
| D2539 (programs never choose on a kept call) | moot: no call is kept | — |
| D2540 (a recovered `E-RESOURCE` never chooses) | **yes in principle**; 0c finds the places, stage 7 changes them | §4.4 |

Decided yes (Matt, 6 Nov 2026): **D2548** (what "visible" means for `match`) and **D2549** (a
visible occurrence whose motive doesn't type-check), in [§10](#10-decisions).

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [Every place that reads back unfolded](#2-every-place-that-reads-back-unfolded)
3. [What was decided before, and how other systems do it](#3-what-was-decided-before-and-how-other-systems-do-it)
4. [The design](#4-the-design)
5. [D484, retired, and why it is safe](#5-d484-retired-and-why-it-is-safe)
6. [Accessor types as written](#6-accessor-types-as-written)
7. [Stages](#7-stages)
8. [The proof migration (D2542)](#8-the-proof-migration-d2542)
9. [Deferred: the cap](#9-deferred-the-cap)
10. [Decisions](#10-decisions)
11. [What this note did not do](#11-what-this-note-did-not-do)

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

**The change.** Two rules, both small to state.

1. **Computing decides; searching acts on what you see** (D2541, D2542). Conversion, `rfl`,
   `decide`, `cases` and tests compute, as today. `rewrite`, `match`, `cases`'
   generalisation and the transport act on the goal as written, the form it is printed in.
   They look inside a definition only when nothing is visible, and the user can always look
   inside one by name with `rewrite f` (D1433) or `f.unfold`.
2. **Read back only what the question needs, and fail honestly** (D2520, D2543). Where a
   site needs to know something about the unfolded form ("does this mention `x`?", "where
   is this, when nothing is visible?", "what does this look like, for a message?"), one
   shared reader answers by walking the value as written and opening a call only when the
   answer could be inside it. It has a fixed work limit per question; running out is an
   error that names the largest call it opened, never a quiet switch to another answer.
   Terms the elaborator writes into its output (accessor types, record updates' annotations,
   `fromYes`'s goal) are read back folded, and `decide` reads its proposition back folded and
   evaluates it with gluing off.

**What it should do.** Trip-journal's goals stay as their source shows them, and its searches
mostly never read anything back unfolded, because what they look for is visible. Where
nothing is visible, the reader opens only calls whose arguments could hold the needle. Stage
0a measures whether that is enough with rule 2 on, and whether switching rule 2 off in search
read-backs (D2544) is a cheaper way. On `main`, the changes are named per stage: output terms
and accessor types read as written (hashes and Float pins move once), motives built by the
fallback come out partly folded (D2538), zonk's fallback unfolds only the calls it must, and
seven measured proofs (§8) take an extra step each because a copy they relied on was hidden
inside a call. The two "unconfirmed" warnings disappear: a goal like `settle x k 40` is
rescued by the visible occurrence, with nothing to warn about.

**Stages** (§7). 0a trip-journal's failures on the branch, with D2544's experiment; 1 output
terms folded and `decide`; 0b the remaining sites classified; 0c the recovered `E-RESOURCE`
places (D2540) and the counts stages 4 and 5 need; 4 the reader's `mentions` and
`unfold_where`, with mentions and zonk moved; 5 `shown`, with messages moved; R `rewrite f`
(D1433); M the measured proofs rewritten in forms that check under both rules; 3 the reader's
`find`; 6a `rewrite` under D2542; 6b `match`, `cases` and the transport under D2542; 7 a
recovered `E-RESOURCE` never chooses. About 15 hours of lanes, of which about 3.5 are work
revision 2 didn't plan (D1433, M, 7, D2544's experiment); like for like, about 4.5 hours fewer
than revision 2, most of it in the hardest Opus lanes (stages 2, 3, 6a and 6b: 590 minutes in
revision 2, 330 now).

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
binders, unfolded quote hits 'too large to show'". Stage 0a gets it from the error's own
note, which names the definition (`too_large_notes`, `crates/elab/src/module.rs:677`)]**

### 1.3 Why fixing the sites one at a time didn't work

- **A failed read-back still costs its steps.** `quote_as` calls `budget.step()` for every
  node (`value.rs:1998`) and fails only after `size_limit()` nodes (10,000,000,
  `crates/core/src/budget.rs:109`). An error is "recoverable" only in the sense that the
  declaration may go on (`crates/elab/src/undo.rs:126`, and only for "too large to show"
  with the operation not out of steps; running out of work is sticky). By then it has done
  ten million steps of work. Sites that swallow the error with `.ok()` (most of the message
  notes, §2.4) pay the same. **[checked]**
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
(`check.rs:648`, which is `quote` at the current level) **[checked: grep, 290 lines; the
review counts 286]**, plus the two `quote_unfolded_shown` sites (`check.rs:754`, `:894`),
which are unfolded too (review L5). They fall into five kinds by what they need from the
term. The tables give the sites the brief named and the ones I read. Stage 0b classifies the
rest, mostly `omega.rs` (42, its own `Quoter` over atoms, `omega.rs:1951`), `effects.rs`
(39, rows), `derive_induct.rs` (31), `equations.rs` (10, generated equation lemmas) and
`interfaces.rs` (11, instance search: classified first, M5).

For each kind, the question is whether the site needs the unfolded form as such, or whether
the form as written plus unfolding on demand would give the same answer.

### 2.1 Searches: find an occurrence in the normal form

These need the *answer* today's unfolded search gives (which occurrences, which instance),
and, on success, a term with those occurrences abstracted (the motive).

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
| `cases.rs:1246`, `:1284`, `:1301`, `:1330`, `:1566` | stuck values and fields | normal forms used as keys for "seen" and "known" sets: a syntactic equality test (`matching::same`, `matching.rs:1780`) |

None of them needs the whole normal form. Today they need: candidates with the needle's key,
in today's order, each compared as today; for the completeness checks, the certainty that no
other candidate exists; and on success, a motive. Under D2542 the completeness checks, today's
instance and the agreement checks go (§4.1), so what is left is the as-written search, and a
fallback that needs candidates and a motive only when nothing is visible (§4.2, D2538).
**[inferred]**

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
| `unify.rs:2597` (`both_forms`), called at `unify.rs:2791` under `cheaply` (fixed limits, size 10,000, `unify.rs:2566–2574`) | a `let`'s value, folded and unfolded, for `refold` | already bounded; the unfolded form is there because "a decision's solution is found on the unfolded goal (D484)" |

`unify.rs:2779` is the brief's "unifier's zonk". It is all-or-nothing: one call holding an
unsolved unknown sends the whole solution through `quote`. **[checked]**

### 2.4 Messages: notes on an error

All of these run on the error path, but an error built inside an attempt that is then undone
pays for them too. Most read both sides back unfolded and ignore failure:

`check.rs:754` and `:894` (`quote_unfolded_shown`), `:772` (opaque notes), `:798`, `:816`
(equation notes), `:864`, `:880` (`differ_only_in_hidden`, `differ_only_in_proofs`), `:894`
(`first_difference_note`, unfolded for display), `:921` (`with_alike_updates_note`), `:1170`
(`unrefined_hint`), `:6967` (`same_function`), `:6995` (`match_equation_note`), `:7105`
(branch notes); `rewrite.rs:1759` (`shown_computed`), `:2101` (opaque notes), `:2113`,
`:2127` (`hypothesis_holding`, every variable's type). **[checked]**

They need the normal form, but only as far as it is worth showing. A note about a value of a
million nodes helps nobody, but a note that shows the first few thousand nodes and the
difference does. **[inferred]**

### 2.5 Output terms: written into what the elaborator produces

| Site | Term |
|---|---|
| `shared.rs:246` (`accessors`) | **each record accessor's result type** |
| `shared.rs:600`, `:633`, `:644`; `records.rs:1448`, `:1470`, `:1543` | a record update's `let` types, annotations and parameters |
| `auto.rs:352` (`from_yes`) | the goal in `fromYes [p := goal] decision Trivial` |
| `bind.rs:108`, `named.rs:726–727` | binder types of elaborated lambdas |
| `lib.rs:956`, `:1036`, `:1080`, `:1375` | types of a checked input, a goal hole's target |
| `rewrite.rs:1605`, `check.rs:4980` | carrier and type terms handed to the kernel's inference |

The kernel checks every one of these up to conversion. A folded term is convertible to the
unfolded one and smaller (folded-calls.md stage 3 moved the others: "for terms the
elaboration produces, such as annotations and helper types", `check.rs:651–653`). So nothing
needs the unfolded form here. It changes hashes only. The review checked the sites for later
syntactic comparisons and found none: `check.rs:4980` and `rewrite.rs:1605` are evaluated
again with gluing off.
`equations.rs` is deliberately not in this table (§9). **[checked; cited, SW-1717 §6
D2523]**

*Corrected (SW-1757, SW-1828).* Earlier drafts listed `matching.rs:521`, `:657` and `:851`
here as scrutinee types in the motive, and `named.rs:895` as a binder type. They are
neither. The `matching.rs` terms are targets that `match`'s occurrence search then searches,
and `named.rs:895` (`dependencies`) is a mentions test (SW-1756 §5). They stay unfolded
until stages 6b and 4b ([bounded-readback-remaining.md](bounded-readback-remaining.md)
§1.2).

### 2.6 `decide` (D484 itself)

`auto.rs:774–795`: "The search sees the unfolded proposition (D484 …): it runs with gluing
off, on `prop` read back and computed again unglued. Otherwise a procedure would be matched
against a call by its arguments before unfolding (`y < 10` decided by `Nat.decLessThan y 10`
rather than `Nat.decLessEq y 9` …)". The code is `let written = cx.quote(prop)?;
g.machine.glue.set(false); cx.eval(&written)`. **[checked]**

So the unfolded read-back is not what `decide` needs. What it needs is a value with **no
glued calls**, so that procedures are matched against what the proposition computes to. With
gluing off, evaluation unfolds every definition it meets (there are no calls: `quote_folded`
"without gluing … is `quote`", `value.rs:1924`). So reading back *folded* and evaluating
with gluing off gives a value with the same normal form as today's, and forcing it at any
position gives what today's value gives there (review M3). **[inferred from the checked
code]** The folded read-back is small (calls stay calls; only calls that step at once are
forced), so this needs no cap and no size fallback. `decide_as_written` (`auto.rs:366`) stays
for what it does today, a decision that is stuck. One thing to check (stage 1): values that
are equal but stored differently, a `Chars` against a chain of `Cons` or `Nat(n)` against
`Succ`s, must be matched the same way, so stage 1 runs `decide` both ways under a debug
switch over std and compares the terms.

### 2.7 The kernel

The kernel already reads back as written where it matters (`quote_kept` in `check_case`,
`crates/core/src/check.rs:923`, and `substitute`, `:1266`, `:1346`, `:1373`). That was
goal-readback.md §6's kernel finding, since fixed. One unfolded read-back is left,
`core/src/check.rs:378`. It is out of scope: the kernel decides by computing, and D2541
keeps that as it is. Stage 0a reports whether trip-journal reaches it. **[checked]**

## 3. What was decided before, and how other systems do it

### 3.1 Decisions

- **D484** (folded-calls.md, Oct 2026): "`rewrite` and the decision search see … the unfolded
  goal, as today, so every existing proof keeps working". The reason was no regressions, not
  that the unfolded form is better. It was narrowed twice before this note. Stage 3 of
  folded-calls.md moved output terms, zonk and messages to folded read-back, "keeping the
  unfolded one for `rewrite`'s search, `refold` and `unify_index`'s occurs check"
  (folded-calls.md, stage 2's "Next"). goal-as-written.md (D2475–D2480) made `rewrite`,
  `match`, `cases` and the transport look as written first, keeping today's result as the
  check and the fallback. **[cited]** **D2541 retires its search clause**; its decision
  clause stays (§5).
- **goal-as-written.md Q4** (D2478, 6 Nov): keep today's reach into hidden copies (days 10
  and 14) rather than Lean's rule. **Reversed by D2542.** The strategy review's evidence: the
  reach was the cause of days 10 and 14's friction, it is what needs the completeness check,
  `todays_instance` and the unconfirmed paths, and Lean's rule was the fastest variant
  measured (69.1 s over AoC against 74.8 s for the check, goal-as-written.md §5.3). **[cited]**
- **D1280** (goal-readback.md §5, 26 Oct, deferred by Matt): `rewrite` and `match` see the
  unfolded goal, except that a call whose unfolding would take more than 100,000 nodes is left
  as the call. Revision 2 revived it as D2519; D2543 defers it again (§9). Two of its lessons
  still apply to the reader. A rule that cuts by *position* (inside a stuck `if`, under a
  binder) breaks proofs, because the needle, read on its own, then reads differently from its
  copy in the goal. And a shared budget whose exhaustion decides an answer "breaks the repro";
  D2543 turns that into a rule for every limit. **[cited]**
- **goal-readback.md option (a), `look`:** folded, unfolding a call when its one-level
  unfolding contains the target. Broke `std/List/Toolkit.sw`, because a target two calls deep
  was missed, "and a deeper one is a full unfolding again". **[cited]** The reader's `find`
  (§4.2) is a deeper look that is *not* a full unfolding, because it opens only calls that
  could hold the target, and it runs only when nothing is visible.
- **The lessons of goal-as-written.md's reviews:** undo every failed attempt; errors fall
  back; kernel-checked motives; no extra copies. "Agree with today's choice of instance" goes
  with D2542: the instance is the first visible one. **[cited]**

### 3.2 How other systems do it

The study ([SW-1718](../reviews/SW-1718-unfolding-comparison.md) §1–§3) found that Lean and
Agda both have record eta's rule 2 (Lean's `toCtorWhenStructure`, Agda's record patterns as
projections), and neither blows up in everyday use, because neither elaborator normalises the
goal in full; Agda's `with`, which does, has exactly this blowup and its manual warns about
it. Lean, Rocq and Agda bound unfolding by *which definitions* may unfold (transparency
levels, `Opaque`/`Strategy`, `opaque` blocks) and by laziness (`whnf`, keyed matching with
`kabstract`, lazy delta in conversion); meta solutions are filled in without unfolding
(`instantiateMVars`; smalltt never unfolds a solution). Caps on printing are common and elide
with `⋯` (Lean `pp.maxSteps` 5,000, Rocq `Printing Depth` 50); caps on work are errors that
ordinary `try` can't catch (Lean `maxHeartbeats`). Nobody has a size cap that is a function of
the call alone. **[cited]**

Revision 3 takes the others' searching rule (Lean's `rw`: what is visible, keyed by head) and
their limits (errors, not switches), and keeps Stitchwort's own default that everything
computes when something *decides* (the strategy review §1.2, §2.1): no transparency levels, no
`simp`, no lemma sets. The fallback that looks inside a definition when nothing is visible has
no direct counterpart in Lean, whose `rw` then fails; it keeps the 759 AoC rewrites that find
their left side only inside a definition (goal-as-written.md §5.3) working without an unfold
step. **[inferred]**

## 4. The design

### 4.1 The rule for searches (D2542)

`rewrite` (on the goal, `at h`, and under binders), `match` and `cases`' generalisation, and
SW-1538's transport along a match's equation all search in two steps:

1. **As written.** Read the target back folded, from the value as bound (unforced, as
   goal-as-written.md stage 1 found it must be), and find the needle there by its head as
   written, comparing by unification as the built stages 1–3 do (and solving a rule's
   unknowns by the call's arguments, D2477). If anything is found, that is the result: its
   occurrences are abstracted, the motive is checked, and nothing else is looked at. Copies
   inside calls are left as they are. For a rule with unknowns, the instance is the first
   visible one in pre-order, as Lean's `kabstract` takes it.
2. **Inside, only if nothing is visible.** The reader's `find` (§4.2) looks for the needle in
   the target's unfolding, opening only calls whose arguments could hold it, under a fixed
   work limit. Its occurrences are abstracted in the target with only the opened calls
   unfolded (D2538). Running out is the error of §4.4.

What goes from the built code: the completeness check (`hidden_copy_in`,
`rewrite/as_written.rs:415–416`), today's instance (`todays_instance`, `:288–471`), `match`'s
agreement check with today's generalisation (`matching/as_written.rs:649–690`), the
transport's agreement check (SW-1629), the unconfirmed paths and their warnings (SW-1630),
and running today's unfolded search alongside. **[cited: goal-as-written.md §6 "As built"]**

Two details are open:

- **What "visible" means for `match`** (D2548). A `match` searches several targets: the goal
  and the variables' types. The rule above treats them as one search (anything visible
  anywhere means no target is looked inside), which is what makes it one rule. SW-1628
  also built two refinements of "visible" that are not agreement with today: a scrutinee
  counts as found only where its variable survives the target's unfolding (not inside
  `keep 3 (isBig n)`, `keep a b := a`), and a closed scrutinee that computes to a constructor
  (`match h: isBig 20` on `pick (isBig 20) = 1`) is decided by computing, not generalised.
  Both are cheap (`mentions` and evaluation) and both are D2541's split: computing decides.
  D2548 keeps them.
- **A visible occurrence whose motive doesn't type-check** (D2549). 2025 day 1's
  `Part2.sw:82` rewrites `d` where `/` holds a hidden proof argument `d ≠ 0`: abstracting the
  visible `d` gives a motive that isn't type-correct, while today's unfolded one is
  (goal-as-written.md §5.3). The built stage 1 falls back when anything on the as-written
  path fails, including the motive's check. Lean fails here ("motive is not type correct"),
  a well-known Lean pain point. D2549 keeps the fallback: a visible result with no
  well-typed motive is treated as nothing visible. That is not a limit switching the
  answer: there is no as-written answer to switch from.

**E-REFL's note** (D2542). When `rfl`, or the end of a `rewrite … in` chain, fails with
E-REFL and a `rewrite` earlier in the same proof left a copy of its left side inside a call,
the error says so: "a copy of `lhs` is still inside `f …`, which the `rewrite` on line N left
as it is: rewrite that copy too, or `rewrite f` to look inside". The rewrite records its left
side as it runs (cheap: a term already built); the search for the copy runs only on the error
path, with `shown`'s budget (§4.2), so it costs nothing when the proof checks. It also tells
the migration lanes (§8) exactly where each broken proof's hidden copy is.

### 4.2 The reader: asking a question of the unfolded form without building it

One module in `crates/core` (`readback.rs`, next to `quote_as`) answers the questions the
sites ask, by walking the value **as written** (as `quote_folded` does) and unfolding a call
only when the answer could depend on what is inside it. D2520, narrowed: it is deterministic,
it gives the answers its tests describe, and every answer it gives a search is checked by
unification, `check_motive` and the kernel, as today. It does not promise to agree with a
full normal form built whole, so it has no both-ways switch as a guarantee; stage 3 runs one
once, as a measurement.

- **`mentions(value, vars, metas)`** (stage 4): whether the unfolding mentions any of these
  variables or unknowns. Exact, in both directions, because `bind.rs:95` needs "doesn't
  mention" to be true.
- **`unfold_where(value, pred)`** (stage 4): the term read back folded, except that the calls
  `pred` picks are unfolded (by the same rule, recursively). For zonk: the calls whose
  arguments mention an unsolved unknown.
- **`shown(value, budget)`** (stage 5): the unfolded form for display: unfolded up to
  `budget` nodes, then each remaining call written as the call and anything else as `⋯`
  (study S2). For messages only; never part of an elaborated term, so its dependence on
  position is harmless.
- **`find(value, needle)`** (stage 3): the occurrences of `needle` in the unfolding, in
  pre-order, each handed to the site's own comparison (a key match, then unification, as
  today), with the set of calls it opened, so the site can build the motive from the target
  with those calls unfolded (D2538). Used only by §4.1's step 2.

Revision 2's `same` (for `cases`' seen and known sets) is not needed as a reader question:
those sets compare stuck values, which are small, and stay as they are until 0b or 0c shows
one is large. **[inferred]**

**When a call can be skipped: the free-variable rule**, as revision 2 had it (review H1):

1. **The needle's relevant variables** are the variables and frozen unknowns free in its
   unfolding (not its folded form: `keep a b := a` does not need `b`), outside *proof
   positions* (`proof_position`, `unify.rs:1839–1861`: `h` in `List.get xs i h` is not
   relevant), outside *unknowns the comparison may solve* with the variables they are applied
   to (`rule_metas`, `rewrite.rs:1270–1271`, and any other unfrozen unsolved unknown), and
   outside *variables of a record type whose every field is a proof*, if the unifier has eta
   for them. They are computed again after `interfaces::refresh` re-reads the needle
   mid-search (`rewrite.rs:1395–1402`); computing them once is still safe, because a solved
   unknown only widens them. **[checked the three code positions in revision 2]**
   *(SW-1828: the last clause doesn't apply. Records whose fields are all proofs have no
   eta (`qualifies_for_eta`), so their variables stay relevant (SW-1725).)*
2. **Skipping.** If some relevant variable is mentioned by no argument of a call (solved
   unknowns replaced, as `force_solved` does), the call's unfolding can't contain an
   occurrence, and it is read as written. Otherwise it is unfolded one step (`unfold_once`,
   `value.rs:570`) and the walk goes on inside. A needle with no relevant variables (a closed
   needle, a number, a constructor) prunes nothing: correct, and bounded by §4.4's limit.
   `mentions` uses the same rule with `vars` in place of the relevant variables.
   **[inferred: the substitution lemma; it holds because definitions are closed terms]**
3. **Memoised on shared values** (study S4): per value cell and per question, "`find` found
   nothing here" and "`mentions` is false here", within one meta epoch. Only negative answers
   are remembered, as `kabstract` does, so the pre-order is kept. This makes the reader's cost
   follow the value's graph, not the tree that today's read-back writes out, which is the
   trip-journal shape (§1.2).

No head rule (review L2): an occurrence's head can come from a native's result, a dictionary
stored in a body, a definition named only in a type argument, or one opaque here but not
elsewhere. It comes back only if stage 3 measures that the free-variable rule isn't enough.

**Tests, kept from revision 2** (they test the free-variable rule, not agreement): stage 3
has one unit test for each case that broke draft 1's rule, plus two:

- *proof position:* needle `List.get xs i h`, goal `… g xs i …` where `g`'s unfolding holds
  `List.get xs i h'`; found;
- *rule unknowns:* `rewrite foo _` whose left side holds the rule's unknown, against a goal
  where the occurrence is inside a call; found, and the unknown solved;
- *folded needle variables:* needle `keep a b` (`keep a b := a`), goal holding `f a` whose
  unfolding is `a`; found;
- *refresh:* an instance solved mid-search changes the needle;
- *stored differently:* `Chars` against `Cons`, `Nat` against `Succ` (review L3).

Stage 4 has the matching ones for `mentions` (a variable dropped by `keep`; one under a proof
position; one only in an unsolved unknown's arguments).

**Why this bounds trip-journal.** Most of its searches find their needle visible and never
reach the reader. Where nothing is visible, a needle like `List.appendNewBy entries entries
(…)` (`Self.sw:78`) has the relevant variable `entries`, which the arguments of the `album =>`
bodies' helpers don't mention, so those calls are never opened. A needle that mentions only
`trip`, in a goal where everything mentions `trip`, is where the reader opens much; then the
memo and the work limit bound it, and running out is an error naming the call, with
`rewrite f` as the way on. Whether that happens, and whether D2544's rule-2-off read-back makes
it go away, is stage 0a's measurement. **[inferred]**

**Undo.** The reader only reads. It solves no unknown, and the comparisons it hands
candidates to are the sites' own, inside the snapshots they already take. Its memo is keyed
by the meta epoch, so an undone solution can't leave a stale answer. **[checked in revision
2]**

### 4.3 Each site

| Kind (§2) | Today | With this design | Changes on `main` |
|---|---|---|---|
| **Searches** (§2.1) | as written first, then a completeness check and today's search over the whole read-back | §4.1: the as-written result whenever there is one; otherwise `find`, with the motive from the opened calls (D2538). No completeness check, no today's instance, no agreement checks, no unconfirmed paths. `cases`' seen and known sets unchanged. | the proofs of §8 need a step; motives and next goals partly folded where the fallback runs; instances are the first visible ones; the two warnings and their examples go |
| **Mentions** (§2.2) | read back whole, look | `mentions`: exact, so `bind.rs:95` stays as permissive as today. `KNOWN_CAP`'s "too large means may" (`unify.rs:978`) stays (§4.4). | none |
| **Zonk** (§2.3) | `unify.rs:2779` re-reads the whole solution unfolded | `unfold_where(solution, args mention an unsolved unknown)`. `refold` gets the same mixed form of a `let`'s value as a third form beside `both_forms`' two, so it still finds the `let`. | solution terms smaller where the fallback fires; hashes there move |
| **Messages** (§2.4) | each note reads both sides back | each side read once per error, as `shown(value, NOTE_BUDGET)` (10,000 nodes, as `cheaply`), shared by every note through a cache on the error being built. A large side is elided with `⋯`, not dropped. `first_difference_note` locates the difference by walking the two values, so a difference inside an elided part is shown. | note text where a side is over 10,000 nodes (`⋯`) |
| **Output terms** (§2.5) | `quote` | `quote_folded` (D2523) | hashes (§6) |
| **`decide`** (§2.6) | `quote` of the whole proposition, re-evaluated unglued | `quote_folded`, re-evaluated unglued, search unchanged (D2535) | none expected; `fromYes` hashes |

**Zonk, and smalltt's alternative** (study S5). smalltt never unfolds a meta solution: it
writes an `Irrelevant` placeholder where a variable is out of scope but vanishes on
unfolding. Stitchwort's kernel checks every elaborated term, and a placeholder is not a term
it can type, so `unfold_where` unfolds the calls instead.

**Goal-as-written's stage 4 examples.** `examples/accept/as-written-unconfirmed.sw` checks
with no warning (the visible occurrence is the result), so it is renamed for what it now shows
(a literal-driven goal rewritten as written). `examples/reject/as-written-unconfirmed-slow-check.sw`
stays a reject, with §4.4's error in place of the motive-check budget's. Day 11's
`settledExactly` checks with no warning. **[inferred]**

### 4.4 Limits (D2543, D2540)

Every limit on this path fails; none chooses.

- **The reader's work limit.** Each question runs under fixed limits of its own, as `cheaply`
  does (`unify.rs:2566–2574`): a work limit and a size limit that don't depend on the
  enclosing operation. Running out is an error: `E-RESOURCE` with a note naming the largest
  call the reader opened ("looking inside `withPhotosOf trip.albums album` took more than
  … steps") and the ways on: `rewrite f` or `f.unfold` to open one definition by name, or
  `opaque`. It is not recovered by the site, and it does not make the site try something
  else. The limit's value is a constant chosen in stage 3 from 0a's and 0c's numbers, as
  `cheaply`'s 10,000 was; not a user setting.
- **`E-REWRITE-BUDGET`** (`rewrite.rs:38`) and the motive check's budget
  (`UNCONFIRMED_BUDGET`, `rewrite.rs:82`): both stay errors. The budget constant is renamed
  for what it bounds (the motive check) when the unconfirmed paths go (6a). **[checked]**
- **`KNOWN_CAP`** (`unify.rs:973`, 4,096): "too large" counts as "may mention", which only
  makes the unifier postpone, never accept. It is not on a search path and is left as it is.
  *(SW-1828: that is true of `mentions_unknown` only, and stage 4a makes it exact (D2611).
  `on_pending`'s use of the same cap falls back to an exact occurs check, so it doesn't
  choose.)*
- **A recovered `E-RESOURCE`** (D2540, study S6). Today a read-back that runs out of size is
  recoverable (`undo.rs:126`), and sites that swallow it with `.ok()` can then take a
  different branch, so a result depends on where a shared budget ran out. After stages 4–6b
  the size limit is rarely reached from §2's sites, and the searches' own recovery paths are
  gone with the unconfirmed paths. Stage 0c lists the declarations where a recovered
  `E-RESOURCE` still changes what is elaborated, on `main` and the branch; stage 7 makes each
  such site fail the declaration instead, as Lean's runtime limits do
  (`tryCatchRuntimeEx`), and the "too large to show" error stops being recoverable.

## 5. D484, retired, and why it is safe

**What D484 becomes** (D2541, D2542). "Deciding computes: conversion, `rfl`, `decide`,
`byDecision`, `cases`, tests and counterexamples see through every definition that isn't
opaque. Searching acts on what is visible: `rewrite`, `match`, `cases`' generalisation and
the transport use the goal as written, and look inside definitions only when nothing is
visible, opening only calls that could hold what they look for." `decide` keeps D484's
decision clause exactly (§2.6): its procedures are matched against what the proposition
computes to. The promise "every existing proof keeps working" is given up for the proofs
of §8, which D2542 accepted.

**Soundness.** Nothing here touches the kernel's rules. Every motive is still type-checked
(`check_motive`, `rewrite.rs:1585`, `matching.rs:1587`), every term the elaborator writes is
still checked by the kernel, and a folded and an unfolded term are convertible. A search that
rewrites fewer copies leaves a goal that is harder to close, never a false one closed; a wrong
answer from the reader could make a proof fail, but it can't make a false statement check.
For *programs*, nothing chooses on a partial answer: there is no kept call (D2539 is moot),
and §4.4 makes every limit an error. **[inferred, as goal-as-written.md §4]**

**What changes for users, and what doesn't.**

1. *Predictability.* One rule a user can apply by reading the goal: "it rewrites what you see;
   if you see nothing, it looks inside". No node counts, no hidden-copy check.
2. *Days 10 and 14* are fixed: the search no longer reaches into a hidden copy when a
   visible one exists (goal-as-written.md §1.2's case (c)). **[cited]**
3. *The cost* is the proofs that relied on the reach (§8): each takes a step naming the
   hidden copy or opening the call, and E-REFL's note points at the copy.
4. *Inside definitions* still works when nothing is visible: the 759 AoC rewrites that found
   their left side only in the computed goal keep working, unless they also had a visible
   copy (those are §8's).

**Time.** On `main`, a search that finds its needle visible does no unfolded read-back at
all, where today it also reads back for the completeness check and today's instance. The
fallback opens a subset of what today's read-back builds and visits a shared value once.
Lean's rule measured 69.1 s over AoC, against 74.8 s for the completeness check and 67.8 s for
the search before stage 1 (goal-as-written.md §5.3, a shared machine). **[cited; stages 3 and
6a measure std, AoC and the roguelike, within D2536]**

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
  limit. Stage 0a says whether it does.

**For users.** The type of `w.pinsFit` shows as written, in hovers, in goals that list it,
and in "this has type …" messages. A `rewrite … at w.pinsFit` finds what the user wrote
as-written (goal-as-written.md; D2542), and looks inside `pinFits` only when nothing is
visible. A proof that rewrote inside the computed form of an accessor's type while a copy was
also visible is one of D2542's migrations (§8), found by stages 6a and 6b's measurement.
**[inferred]** Nothing else changes: the
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
  and `fromYes`'s goal move the same way. Not a cost (migration cost doesn't count), but the
  stage's lane re-records them.

**A check for the stage:** whether gluing is on when `accessors` runs. If it isn't,
`quote_folded` is `quote` (`value.rs:1924`: "Without gluing … this is `quote`"), and the
field type must be evaluated with gluing on first. Data declarations are elaborated inside
`check_component`, which runs under `glued` (`module.rs:404`), so I expect it is on.
**[inferred]**

## 7. Stages

Each stage is one lane, merged to `main` on its own, and says what it changes on `main`
and which snapshots it expects to move. Model choice follows CLAUDE.md: Opus for the
unifier, `rewrite`/`match` and core read-back (D2506); Sonnet with an Opus review where a
stage changes kernel terms (D2364). Estimates are from similar lanes (the goal-as-written
stages took about 120 min per consumer) and from the strategy review's guesses for the
narrowed stages; none is measured. Stage letters keep revision 2's numbers where the stage
survives; R (`rewrite f`), M (the migration) and 7 are new; 2 is deferred (§9).

| Order | Stage | What changes on `main` | Tests | Model | Opus review | Est. (min) | Needs |
|---|---|---|---|---|---|---|---|
| 1 | **0a** trip-journal's failures on `lane/SW-1642`, with D2544's experiment | nothing (branch only) | trip-journal only | Sonnet | — | 60 | — |
| 2 | **1** output terms folded; `decide` folded, evaluated unglued | hashes of accessors and dependents, record updates, `fromYes`; Float pins | targeted: accessor-type snapshots, `and-or-not.sw`, float gate, `*_bound_to_the_prelude`, `decide` both ways over std once | Sonnet | yes (kernel terms) | 75 | D2523, D2535 |
| 2 | **0b** the remaining sites classified (no build) | nothing (a table in this note) | none | Sonnet | — | 60 | — |
| 2 | **0c** recovered `E-RESOURCE`s that change what is elaborated; zonk fallback count; message sides over 10,000 | nothing (metrics behind an env var) | one background run of std, AoC, rogue, examples, on `main` and the branch (D2536) | Sonnet | — | 45 | D2536 |
| 3 | **4** `readback.rs` with `mentions` and `unfold_where`; mentions and zonk moved | zonk's solution terms where its fallback fired | `mentions` unit tests, SW-323's `ignorable` tests, zonk's tests in `unify.rs` | Opus (the unifier, D2506) | — | 90 | 0b |
| 3 | **5** `shown`; messages moved | note text where a side is over 10,000 nodes | E-REFL and E-TYPE-MISMATCH snapshots unchanged; a new large-side snapshot | Sonnet | — | 60 | 4 |
| 4 | **R** `rewrite f`: one step of `f` by name (D1433) | a new rule form; no existing term moves | new accept and reject examples; guide and `syntax.md` examples | Opus (a tactic, D2506) | yes (generates `J` terms) | 90 | — |
| 5 | **M** the measured proofs rewritten (§8) | seven declarations' proof terms; their hashes | each declaration checked on its own | Sonnet | — | 45 | R |
| 5 | **3** the reader's `find` | nothing (used by no site yet) | §4.2's five unit tests; one both-ways measurement over std (D2536) | Opus | — | 120 | 4, D2520 |
| 6 | **6a** `rewrite` under D2542 | motives where the fallback runs; first visible instance; `W-REWRITE-UNCONFIRMED` gone; E-REFL's note; any further broken proofs fixed | goal-as-written stage 1 repros, `as-written-unconfirmed.sw` renamed, day 11's `settledExactly`; one background run of std, AoC, rogue (D2536) | Opus | yes (motives) | 100 | 3, M, D2549 |
| 7 | **6b** `match`, `cases` and the transport under D2542 | `match` motives and arms where the fallback runs; `W-MATCH-UNCONFIRMED` gone | `match-equation-as-written.sw`, goal-as-written's stage 2 repros, `as-written-unconfirmed-slow-check.sw`; one background run (D2536) | Opus | yes (motives) | 110 | 6a, D2548 |
| 8 | **7** a recovered `E-RESOURCE` never chooses (D2540) | the sites 0c listed fail instead of recovering | 0c's declarations, one by one | Sonnet | yes (elaboration choices) | 45 | 0c, 6b |

Rows with the same order number can run side by side. In all, about 900 minutes (15 hours):
Opus lanes 510 minutes (4, R, 3, 6a, 6b), Sonnet 390. Revision 2's like-for-like stages came to
965 minutes; the same work here is about 690, and R, M, 7 and the D2544 experiment add about
210 that revision 2 didn't plan.

**The order** is D2545's (0a; then 1, 0b, 4 and 5; then D1433; then 3, 6a and 6b), with the
three stages it doesn't name placed by me, as sequencing: 0c alongside 0b, since it builds
only metrics and 4 and 5 use its counts; M after R, since three of its fixes use `rewrite f`,
alongside 3; and 7 last, since 6a and 6b remove most of the recovering sites it would
otherwise change. 4 comes before 3, as D2545 orders, so the reader module is created in 4
(with `mentions` and `unfold_where`) and `find` is added to it in 3.

**Per stage.**

- **0a. Trip-journal's failures, on the branch** (D2544). On `lane/SW-1642`, a counter or
  backtrace on every read-back over 1,000,000 nodes, trip-journal only. Out: which sites fail;
  which definitions (the error's note, `module.rs:677`); whether it also runs out of *work*;
  whether accessor types and `decide` are among the failures; how large the folded read-backs
  are; whether the kernel's `check.rs:378` or `substitute` is reached; and how many of the
  failing searches find their needle as written (those need no reader at all under D2542).
  Then D2544's experiment, in the same scratch run: the read-backs that searches use treat a
  `case` on an unknown record as stuck, as `matches_at_once` already does for the folded form
  (`value.rs:584`); conversion keeps rule 2. Out: whether trip-journal's searches then stay
  small, and whether anything else changes (a needle and its goal both go through the same
  read-back, so no inconsistency is expected; the run checks it). If it works, it is adopted
  on the branch, as part of SW-1642's work, not as a stage on `main`: rule 2 exists only
  there. *Risk:* none to behaviour.
- **1. Output terms folded and `decide`** (§2.5, §6, §2.6). As revision 2: `shared.rs:246`
  and the rest of §2.5's table to `quote_folded`; `decide` reads back folded and evaluates
  unglued, with a both-ways debug switch over std comparing the decisions' terms. Float pins,
  hash snapshots and the bound-to-the-prelude tests updated. Accept: accessor types print as
  declared; `examples/accept/and-or-not.sw` keeps `Nat.decLessEq y 9`. *Risk:* a proof that
  relied on an accessor's type being in normal form for a syntactic test.

  **Left unfolded in stage 1b.** Stage 1b (SW-1748) folded the remaining output terms of
  §2.5. These sites were deliberately left unfolded; a later stage should not fold them
  until it does the work named. Lines are current on `main` (grep).

  | Site | Why it stays unfolded | Stage |
  |---|---|---|
  | `derive_induct.rs:427` (`field_type`; `quote` at `:432`) | `classify` matches the head of the field type, so a type written as a call (`Children A`) would hide it. Fold the output only once `classify` reads a separate unfolded copy (SW-1747 item 7). | 1, later |
  | `derive_induct.rs:1257` (`move_to`; `quote` at `:1259`) | Re-evaluates with `unused` placeholder slots that must agree with `pred_levels`' unfolded reading; it needs a real substitution first. | 4 |
  | `derive_induct.rs:629` (`pred_levels`; `quote` at `:632`), `effects.rs:616` (`same_results`; `:619`), `:3692` (`row_in_result`; `:3699`), `:3997` (`written_outside`; `:4010`), `:5105` (`partial_mismatch`; `:5118`), `interfaces.rs:1399` (`scanned`) | Mentions tests: they read the term back to walk its variables, so they need `mentions`. | 4 |
  | `effects.rs:3985` (`unsettled`; `quote` at `:3986`, `zonk_keeping` at `:3987`) | Zonk: checks the zonked type for an unknown nothing has solved. | 4 |
  | `effects.rs:4133` (`escapes`; `quote` at `:4135`, `:4142`) | Message text: builds the `E-EFFECT-ESCAPE` note from the result type. | 5 |
  | `families.rs:678` (`enter`; `quote` at `:702`), `rows.rs:248` (`refresh_at`; `quote` at `:250`) | Round trips whose results feed unification, so folding them could change what is solved. | 4 |
  | `rewrite.rs:574` (`discharge`; `quote` at `:588`) | Round trip feeding the premise hypothesis search, so folding it could change what is found. | 6a |

- **0b. The remaining sites classified** (no build). The ~200 unread sites into §2's kinds, as
  a table appended to this note: `equations.rs` (stays unfolded or folded per site; §11),
  `omega.rs`, `effects.rs`, `derive_induct.rs`, `interfaces.rs`. `interfaces.rs` is no longer
  first (D2539 is moot), but instance search is still a place where a limit must fail rather
  than choose (§4.4), so 0b marks any site there that recovers.
  **Done (SW-1747):** all 288 sites are in [SW-1747-stage-0b-sites.md](../reviews/SW-1747-stage-0b-sites.md).
  Stage 1: 126, 4: 41, 5: 28, 6a: 18, 6b: 20, stay unfolded 6, no stage 22 (omega and ring
  atom identity), not a read-back 27. Its findings: a gap, stage 1's size, and `scanned`'s
  100,000-node cap in instance search.
- **0c. The measurements** (narrowed; no behaviour change). `STITCHWORT_READBACK_METRICS`:
  per unfolded read-back, its site and node count; recovered `E-RESOURCE`s that change what is
  elaborated (D2540's places); how often zonk's whole-solution fallback fires; message sides
  over 10,000 nodes. Over std, AoC, the roguelike and the examples, on `main` and on
  `lane/SW-1642`, one background run each, stopped at 6 minutes (D2536). Revision 2's cap
  measurements (the largest capped call, kept calls by key and by cell) are dropped with the
  cap; the largest single-call unfolding is still logged, as the evidence §9 asks for.
- **4. The reader, part 1: `mentions` and `unfold_where`; mentions and zonk moved** (§2.2,
  §2.3): `check.rs:3889`, `bind.rs:95/99`, `matching.rs:434`, `lib.rs:4954`,
  `rewrite.rs:707/1690`, `matching.rs:1685`, `cases.rs:1582`, `unify.rs:978/177`;
  `unify.rs:2779` to `unfold_where`, with `refold`'s third form. The free-variable rule, the
  memo, the fixed work limit (§4.4). *Moves:* solution terms where zonk's fallback fired (0c
  counts them).
- **5. The reader, part 2: `shown`; messages moved** (§2.4), one read-back per side per error,
  eliding with `⋯`.
- **R. `rewrite f`** (D1433; goal-as-written.md option D and stage 5; folded-goals.md option
  D). A rule naming a definition means its one-step equation, as Lean's `rw [f]` and
  ssreflect's `rw /f`: the visible calls of `f` (as written, by §4.1's rule) are replaced by
  one step of their unfolding, and the next goal is read back folded, so calls that step at
  once show their result. For a definition with arms, the step is the arm the arguments
  select, which needs the arguments to select one (otherwise an error suggesting `match`).
  It is the normal way to look inside a definition under D2542, and the escape revision 2
  wanted for D2529. A user-visible feature: `docs/syntax.md` ("rewrite"), the language
  guide's proofs chapter with a checked example, and a feature-tour page if it reads well
  there. *Moves:* nothing existing.
- **M. The measured proofs rewritten** (§8). Each of the declarations in §8's table rewritten
  in a form that checks under today's rule *and* under D2542's, so it can merge before 6a and
  6a's own run starts clean. Checked one declaration at a time. The orchestrator checks that
  no statement changed (D2436).
- **3. The reader, part 3: `find`** (§4.2). Pre-order occurrences handed to the site's
  comparison, the opened calls returned, relevant variables recomputed after `refresh`, the
  work limit's error. Used by no site yet. One both-ways measurement over std (`find`
  against a whole read-back and a syntactic search), reported, not enforced.
- **6a. `rewrite` under D2542** (§4.1). In `rewrite_once` and `rewrite/under.rs`: the
  as-written result whenever there is one; otherwise `find` with motives from the opened
  calls (D2538); a visible result whose motive fails falls back as today (D2549). Removed:
  `hidden_copy_in`, `todays_instance`, the unconfirmed path and `W-REWRITE-UNCONFIRMED`, the
  unfolded search alongside. Added: E-REFL's note (§4.1). Then one background run of std, AoC
  and the roguelike (D2536): every declaration that fails is fixed in this lane as in §8,
  with E-REFL's note to find the copy. Docs: `docs/syntax.md` "rewrite", the proving guide's
  §3 on what `rewrite` searches and its E-REWRITE-NOTHING and warning entries, the language
  guide's proofs chapter; folded-calls.md's D484 entry gets a line pointing to §5.
- **6b. `match`, `cases` and the transport under D2542.** `generalised_now`, `normals`, the
  transport test (`along_match_equation_now`): the as-written generalisation whenever the
  scrutinee is visible in any target, with D2548's two refinements; otherwise `find`.
  Removed: the agreement checks (`matching/as_written.rs:649–690`, SW-1629's), the unconfirmed
  path and `W-MATCH-UNCONFIRMED`. Kept: the `let` rule (a `let`'s copy is never abstracted,
  since it would forget its value), the motive check. Then the same background run and
  fixes as 6a. Docs: `docs/syntax.md` "Generalised `match`", the proving guide's `match`
  entries.
- **7. A recovered `E-RESOURCE` never chooses** (D2540). Each site 0c listed (less those 6a
  and 6b removed) fails the declaration instead of recovering, and "too large to show"
  stops being recoverable in `undo.rs:126`. Checked on 0c's declarations.

**What unblocks SW-1667.** Correctness: trip-journal on the branch elaborates with no "too
large to show". That needs, for each kind of site 0a finds failing, the stage that moves that
kind: 1 if accessors, record updates or `decide` fail; 4 if mentions or zonk; 5 if messages;
6a/6b if searches whose needle is not visible. Searches whose needle is visible are fixed by
6a/6b too, but D2544's experiment may fix them earlier on the branch. Speed: trip-journal
takes at most about twice its time on `main`. SW-1667 resumes as soon as both hold (D2545),
which 0a's report can put as early as after stage 1, or as late as after 6b.

## 8. The proof migration (D2542)

**The proofs.** From the two measurements of Lean's rule:

- `rewrite`: goal-as-written.md §5.3's prototype in `lean` mode over `aoc/`, release build
  from `cb58d7916`: "Lean's rule (B) breaks five declarations: 2020 day 17 `Neighbours.sw:41`,
  2025 day 1 `Part2.sw:82` and `:94`, 2025 day 8 `Labels.sw:107` and `:153`. Each needed a
  hidden copy rewritten (in day 8, inside `Map.Raw.fromListChecked`'s unfolding, where `rfl`
  then failed)". **[cited]**
- `match`: folded-goals.md's scratch patch without the check: `Result.traverseCons` in
  `std/Result/Result.sw` and `List.foldMaxMem`, then in `std/List/Toolkit.sw`. **[cited]**

The lines are the same on `main` at `2991bb684` (`List.foldMaxMem` has moved to
`std/List/Lemmas.sw`). **[checked]** The table names the declaration, the step and the hidden
copy as far as the source shows it. The copies are my reading of the source, not run; rows 5 and
7's are not established. Stage M checks its fixes under today's rule; 6a and 6b's runs
confirm them under D2542.

| # | Declaration (file, line of the step) | The step | The hidden copy | Fix | Stage |
|---|---|---|---|---|---|
| 1 | `labelledAtStart`, field `stored` (`aoc/src/Aoc/Year2025/Day08/Proofs/Labels.sw:107`) | `rewrite storedAtStart n b h in rfl` | the goal `(Circuits.separate n).labels.get b = Some ((Circuits.separate n).labelOf b)` has the left side visible on the left, and a copy inside `labelOf b` (the source note's "inside `Map.Raw.fromListChecked`'s unfolding") | rewrite the visible copy with the lemma about it: `rewrite labelAtStart n b h in storedAtStart n b h` (`labelAtStart` is at `:103`). Under either rule `labelOf b` is visible, and what is left is `storedAtStart`'s statement | M |
| 2 | `labelledMoved`, field `stored` (`Labels.sw:153`) | `rewrite movedStored c f s n inv.stored b h in rfl` | the same shape: a copy inside `(moved c f s).labelOf b` | `rewrite movedLabel c f s n inv.stored b h in movedStored c f s n inv.stored b h` (`movedLabel` is at `:134`) | M |
| 3 | `stepRight` (`aoc/src/Aoc/Year2025/Day01/Proofs/Part2.sw:82`) | `_ = (Succ a + n) / d := rewrite (omega: d = Succ a)` | not a hidden copy: `/` holds a hidden proof argument `d ≠ 0`, so the motive that abstracts the visible `d` isn't type-correct (goal-as-written.md §5.3) | none needed if D2549 is yes (the built fallback keeps it checking, as it does today). If no: rewrite the other side, `rewrite same` (the arm's `same: Succ a = d`), which replaces the visible `Succ a` and leaves `d`, and so the proof argument, alone | 6a, only if D2549 is no |
| 4 | `rightCount` (`Part2.sw:94`) | `rewrite zerosLandedOnCons …, rightCount (Dial.move dial (Right 1)) k, Mod.valueOfInt (dial.position.toInt + Nat.toInt 1)` | `Mod.valueOfInt`'s left side `(Mod.ofInt …).value` is visible in the division, and a copy is inside `Dial.isZero (Dial.move dial (Right 1))`, whose unfolding is `Mod.isZero` and then `.value == 0` | open the two calls first, so both copies are visible: `…, rightCount …, Dial.isZero, Mod.isZero, Mod.valueOfInt …` with R's `rewrite f` | M |
| 5 | `countWithin1`, second cons arm (`aoc/src/Aoc/Year2020/Day17/Proofs/Neighbours.sw:41`) | `rewrite countPrefixed (x - 1) …, countPrefixed x …, countPrefixed (x + 1) …, countWithin1 xs ys in windowAnd …` | not established from the source: one of the four rules has a visible copy and a hidden one, most likely inside `List.sumBy` (from `List.countFlatMap`'s right side) | in 6a: E-REFL's note names the copy; then one more rewrite of that copy, or `rewrite List.sumBy` first so all three summands are visible | 6a |
| 6 | `Result.traverseCons` (`crates/elab/src/std/Result/Result.sw:71`) | `match e: f x with …` | the goal `Result.traverse [x, ..xs] f = Result.flatMap (f x) …` has `f x` visible on the right and a copy inside `Result.traverse` on the left, so the left side doesn't compute in the arms and the next `rewrite` finds nothing | open `Result.traverse` first: `rewrite Result.traverse in match e: f x with …`. Its unfolding `Result.traverseLoop f [] [x, ..xs]` steps at once to the loop's `match f x`, so the copy is visible to the `match` under either rule | M |
| 7 | `List.foldMaxMem` (`crates/elab/src/std/List/Lemmas.sw:2206`) | `match h: Nat.leq start y with …` inside the `Inl e` arm | `e: List.foldLeft ys (Nat.max start y) Nat.max = …` holds `Nat.leq start y` only inside `Nat.max`, and on 28 Oct the scrutinee was found elsewhere first, so `e` was not refined. Whether it is still visible in the goal as `main` reads it back now is not established: if nothing is visible anywhere, the fallback refines `e` and nothing breaks | split first, recurse second: `match h: Nat.leq start y` before `List.foldMaxMem ys (Nat.max start y)`, so no hypothesis holds the copy yet; in each arm `Nat.max start y` computes to `y` or `start`, and the recursive call is made at that value | M |

So M rewrites five (1, 2, 4, 6, 7) in forms that check under both rules; 6a takes row 5,
where the copy has to be found by running, and row 3 only if D2549 is no.

**The seven are a lower bound.** The `rewrite` measurement read std from the prelude cache
(so std's own rewrites weren't measured), predates the AoC days merged since `cb58d7916`, and
ran a prototype without `match`. The `match` measurement is from 28 Oct, before the 2020
days. So 6a and 6b each start with one background run (D2536) and fix what else breaks, the
same way, in their own lane: rewrite the visible copy with a lemma about it, or open the call
with `rewrite f`. Their estimates include about 20 minutes for this; if the run finds more
than five more, the lane stops and reports (CLAUDE.md, the 1.5× rule) rather than sweeping.

## 9. Deferred: the cap

Revision 2's capped normal form (its §4.1: a call whose own capped unfolding is over 100,000
nodes is kept as the call; D2519, D2533) and its fixed `CAP` with no escape (D2529) are
deferred by D2543. Its stage 2 is not planned. The reasons, from the strategy review (§2.2,
§3):

- **Nothing on `main` reaches it.** D1280 measured that nothing in std, AoC or the roguelike
  is kept at 100,000 (goal-readback.md §5). Its purpose was to keep D484's search clause
  above the cap and to bound trip-journal; D2541 retires the clause, and whether the reader
  and D2544 bound trip-journal is 0a's measurement.
- **A user can't see it.** "Except inside a call whose unfolding is over 100,000 nodes" is a
  rule in node counts, deterministic but unpredictable, and the study found no system with
  such a cap (SW-1718 §3.3).
- **It changes answers rather than failing.** D2543's rule is that limits fail.
- **Its cost.** The recursive size test, the cache by call and epoch, and the language
  constant were the plan's most delicate code (D1280's 6× slowdown on rogue2q before a cache).

**What would bring it back:** a proof, on `main` or the branch, that needs to see inside a
call too large for the reader's work limit, *and* can't be written with `rewrite f`,
`f.unfold` or `opaque`. Stage 0c still logs the largest single-call unfolding per site, so the
evidence collects without a lane of its own. Revision 2's §4.1 and D2519–D2533 text are in
the history (`git show 2991bb684:docs/proposals/bounded-readback.md`).

## 10. Decisions

D2541–D2545 and the earlier questions are recorded under [Decided](#decided). Two further
questions, both decided yes by Matt on 6 Nov 2026, raised by writing §4.1 for the code SW-1628 and SW-1627 built:

- **D2548: what "visible" means for `match`** (6b). (1) A `match` is one search over all its
  targets (the goal and the variables' types): if the scrutinee is visible in any of them, no
  target is looked inside. (2) SW-1628's two refinements stay: a scrutinee counts as visible
  only where its variable survives the target's unfolding (not inside `keep 3 (isBig n)`),
  and a closed scrutinee that computes to a constructor is decided by computing rather than
  generalised (`match h: isBig 20` on `pick (isBig 20) = 1`). [rec: yes to both. (1) is what
  keeps the rule one rule; looking inside per target might keep `List.foldMaxMem` as it is (§8 row
  7), but would bring back days 10 and 14's reach for hypotheses. (2) is D2541's split applied to `match`:
  these are cases where computing decides, and both are cheap (`mentions`, evaluation); without
  them a `match` would generalise occurrences the arms can't use.]
- **D2549: a visible occurrence whose motive doesn't type-check** (6a, 6b). Treat it as
  nothing visible and look inside, as the built stage 1 does on any failure of the as-written
  path, rather than fail as Lean does ("motive is not type correct"). [rec: yes. It is not a
  limit choosing an answer, since there is no well-typed as-written answer; it keeps
  `Part2.sw:82` and the four "folded-error" rewrites of goal-as-written.md §5.3 checking with
  no edit; and Lean's error here is one of its best-known frustrations. If no, row 3 of §8 is
  rewritten in 6a, and those four rewrites are found by 6a's run.]

## 11. What this note did not do

- It ran nothing (D2518, SW-1722, SW-1728). The size of trip-journal's read-backs, whether
  D2544's experiment works, how many searches find their needle visible, the reader's speed
  and the full list of proofs D2542 breaks are stage 0a's, 0c's, 3's, 6a's and 6b's
  measurements. The estimates in §7 are not measured.
- It did not re-run goal-as-written's prototype for the `match` half of D2542, or on std.
  §8's seven come from the two earlier measurements and are a lower bound.
- §8 rows 1, 2, 4 and 6's hidden copies are read from the source, not confirmed by a run;
  rows 5 and 7's are not established.
- It classified about 90 of the 290 unfolded read-back sites by reading them (revision 2).
  The rest are stage 0b's (done: [SW-1747-stage-0b-sites.md](../reviews/SW-1747-stage-0b-sites.md)). `equations.rs` is narrower than draft 1 feared (review Q4): the
  sites that could change something are its binder types (`equations.rs:2833`),
  `bool_equation`'s right side (`:2532`), `uniqueness`'s sides (`:4445–4446`) and
  `mentions_computation` (`:5064–5072`). Stage 1 leaves the file alone; a later stage that
  folds its binder types checks that `rewrite f.eq_k` proofs are unchanged.
- From the study: not the head rule's stored reachability (S3), nor an inferred
  "abbreviation" status for keyed searches (S8, the strategy review's option (c)), nor
  `decide` reducing lazily with no read-back at all (S1), nor occurrence selection
  (`rewrite (at := 2)`, goal-as-written.md option E). Each is a backlog idea for if D2542's
  rule proves too weak.
- It didn't move SW-1712 or SW-1728 on the board: the brief said not to edit
  `board/tickets.json`.
