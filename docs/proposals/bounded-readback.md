# Proposal: bounded read-back: the elaborator looks at goals as written and unfolds only what it needs

**Revision 2** (SW-1722, 6 Nov 2026), after the independent review
([SW-1717](../reviews/SW-1717-bounded-readback-review.md), "proceed with changes") and the
comparative study ([SW-1718](../reviews/SW-1718-unfolding-comparison.md)). What changed: the
reader prunes by the needle's *relevant* variables, with three planned tests (H1); the cap has
one, recursive definition, under fixed limits, cached by the call and the meta epoch (H2, M4)
and fixed in the language; stage 6 removes the "unconfirmed" paths only where the cap kept a
call, not for literal-driven goals or an exhausted search budget (H3); stage 0 measures on
`lane/SW-1642` as well, across AoC, the roguelike and the examples (H4), and starts with a
30-minute stage 0a on trip-journal; `decide` reads back folded and evaluates with gluing off,
with no cap, in stage 1 (M3); every stage names what it changes on `main` (M1, M2); `cases`
keeps exact comparison; programs never silently pick a different instance (M5); messages
elide with `⋯` instead of dropping notes (study S2); the reader memoises negative answers
(S4). Estimates rechecked (stage 3 200 min, stage 6 split as 6a and 6b). §8's questions are
restated: D2519, D2520, D2523 and D2529 keep their numbers; D2521, D2522, D2524 and D2528
are replaced; D2533–D2540 are new.

**Status:** draft 2, design only, stopped for Matt's decisions ([§8](#8-decisions)). Ticket
SW-1712, from D2514 (Matt, 6 Nov 2026: "bound unfolded readback by making the elaborator's
searches look at goals as written, starting with a short design note on Opus that revisits
D484; accessor types read back as written too"). Unblocks record eta (SW-1642, SW-1667).
Draft 1 was written against `main` at `e0f9d7809` and `lane/SW-1642` at `c91991954`; revision
2's new checks are against `main` at `0d0e12b79` (nothing under `crates/` that this note cites
moved). All `file:line` citations are `main`'s unless marked "(branch)". Migration cost
(hashes, snapshots, pins, sweeps) is not counted; options are judged by where they end up.

**Why a note of its own, not a section of goal-as-written.md.** That note is about two
tactics (`rewrite`, `match`) and is decided and mostly built. This one covers every unfolded
read-back in the elaborator: the unifier, implicit arguments, error notes, `decide`, record
accessors and the searches. It revisits D484 as a whole and revives D1280 (goal-readback.md).
goal-as-written.md stays the record of stages 1–4; §4.3 here says what changes in them.

Related notes: [goal-as-written.md](goal-as-written.md) (stages 1–4, SW-1627–SW-1630),
[goal-readback.md](goal-readback.md) (the size cap, D1280, deferred 26 Oct),
[folded-calls.md](folded-calls.md) (glued calls, D483, D484),
[record-eta.md](record-eta.md) (on `lane/SW-1642`; rule 2, §6.4),
[folded-goals.md](folded-goals.md) (SW-742). Reviews:
[SW-1717](../reviews/SW-1717-bounded-readback-review.md) (findings H1–H4, M1–M6, L1–L5),
[SW-1718](../reviews/SW-1718-unfolding-comparison.md) (suggestions S1–S8).

Labels:

- **[checked]**: read in this repository at the place given.
- **[cited]**: read in the note or ticket named.
- **[inferred]**: my reasoning from checked or cited facts.

Nothing here was run: both lanes were read-and-write only (D2518, SW-1722). Every claim that
needs a measurement says so, and stage 0 ([§7](#7-stages)) makes the measurements.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [Every place that reads back unfolded](#2-every-place-that-reads-back-unfolded)
3. [What was decided before, and how other systems do it](#3-what-was-decided-before-and-how-other-systems-do-it)
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
call whose own unfolding is too large is kept as the call**. "Its own unfolding" is read by
the same rule, so the innermost large calls are the ones kept, and a call's size is
measured under fixed limits of its own, so the same call is kept or not wherever it sits
(§4.1). That one thing is never built whole. Each site asks it a question ("where does this
occur?", "does this mention `x`?", "are these the same?", "what is it, if it's small?").
One shared reader answers by walking the value **as written**. It unfolds a call only when
the answer could depend on what is inside: a call whose arguments mention none of the
variables that an occurrence of the needle must contain can't hide one, so it is never
opened (§4.2). Terms the elaborator writes into its output (record accessors' types, a record
update's annotations, `fromYes`'s goal) are read back folded, as written, and `decide` reads
its proposition back folded and evaluates it with gluing off, which needs no cap at all.

**What it should do.** Below the cap every search gives today's answer, because pruning
only skips calls that can't hold the answer, and the walk keeps today's order. Where the cap
keeps a call, the search sees the call as written, as Lean always does. Two things still
change on `main` even below the cap, and are named as such: motives built by the fallback
search come out partly folded (D2538), and zonk's fallback writes only the calls it must
unfolded (stage 4). Whether anything reaches the cap, on `main` *and with record eta*, is
stage 0's measurement, not an assumption. Trip-journal's goals stay as their source shows
them. Accessor types read as their source writes them, so their hashes move once, and so do
the hashes of `Float`'s natives pinned in `crates/core/src/float.rs:81`.

**Stages.** 0a trip-journal's failures, on the branch (30 min); 0b the remaining sites
classified; 0c the measurements across AoC, the roguelike and the examples, on `main` and the
branch; 1 output terms folded and `decide` (M3); 2 the capped read-back as `Ctx::quote`'s
meaning; 3 the reader, used by nothing yet; then the sites move onto it: 4 mentions and zonk,
5 messages, 6a `rewrite`'s searches, 6b `match`, `cases` and the transport. SW-1667 resumes
once every kind of site that 0a finds failing has moved, and trip-journal takes at most
twice its time on `main` (D2537). The review expects that to mean after stage 6 (M6), and
the plan assumes it.

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

None of them needs the whole normal form. They need: candidates with the needle's key, in
today's order, each compared as today; for the completeness checks, the certainty that no
other candidate exists; and on success, a motive (§4.3, D2538). **[inferred]**

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
| `bind.rs:108`, `named.rs:726–727`, `:895` | binder types of elaborated lambdas |
| `lib.rs:956`, `:1036`, `:1080`, `:1375` | types of a checked input, a goal hole's target |
| `matching.rs:521`, `:657`, `:851` | scrutinee types in the motive |
| `rewrite.rs:1605`, `check.rs:4980` | carrier and type terms handed to the kernel's inference |

The kernel checks every one of these up to conversion. A folded term is convertible to the
unfolded one and smaller (folded-calls.md stage 3 moved the others: "for terms the
elaboration produces, such as annotations and helper types", `check.rs:651–653`). So nothing
needs the unfolded form here. It changes hashes only. The review checked the sites for later
syntactic comparisons and found none: `check.rs:4980` and `rewrite.rs:1605` are evaluated
again with gluing off, and the `matching.rs` ones are motive types the kernel checks.
`equations.rs` is deliberately not in this table (§9). **[checked; cited, SW-1717 §6
D2523]**

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
`core/src/check.rs:378`. It is out of scope, and the cap never applies to the kernel
(D2519); stage 0a reports whether trip-journal reaches it. **[checked]**

## 3. What was decided before, and how other systems do it

### 3.1 Decisions

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
  write out is left as the call". Its scratch version read a call's unfolding by the same
  capped rule ("sizes counted while reading back", goal-readback.md §4's table), so inner
  large calls were kept and outer ones stayed visible. Measured then: at 100,000, **nothing in
  std, AoC or the roguelike is kept folded** and times don't move, but at 10,000 one AoC
  proof breaks (`Year2025/Day08/Proofs/Part2.sw:287`). Its lessons apply here. First, a rule
  that cuts by *position* (inside a stuck `if`, under a binder) breaks proofs, because the
  needle, read on its own, then reads differently from its copy in the goal. Second, a shared
  budget whose exhaustion decides which call is kept "breaks the repro: which call is kept
  then depends on where the budget ran out". The kept call must be a function of the call
  alone. Third, a call that steps at once can't be kept, because the folded read-back expands
  it again elsewhere. Its cost, measured: each kept call wastes up to 100,000 nodes of
  read-back each time it is met (rogue2q 18.7 s against 2.9 s); a per-cell cache saved little
  ("the kept calls are mostly fresh cells"), so it proposed a cache keyed by the call.
  **[cited]** That measurement covered only D1280's own sites, before record eta, partly with
  `STW_KGLUE`, so it does not carry over (review H4): stage 0c measures again.
- **goal-readback.md option (a), `look`:** folded, unfolding a call when its one-level
  unfolding contains the target. Broke `std/List/Toolkit.sw`, because a target two calls deep
  was missed, "and a deeper one is a full unfolding again". **[cited]** §4.2 is a deeper
  look that is *not* a full unfolding, because it opens only calls that could hold the
  target.
- **The lessons of goal-as-written.md's reviews:** agree with today's choice of instance; no
  extra copies; undo every failed attempt; errors fall back; kernel-checked motives. **[cited]**
  §4 keeps each.

### 3.2 How other systems do it

The study ([SW-1718](../reviews/SW-1718-unfolding-comparison.md) §1–§3) found that Lean and
Agda both have record eta's rule 2 (Lean's `toCtorWhenStructure`, Agda's record patterns as
projections), and neither blows up in everyday use, because neither elaborator normalises the
goal in full; Agda's `with`, which does, has exactly this blowup and its manual warns about
it. Lean, Rocq and Agda bound unfolding not by size but by *which definitions* may unfold
(transparency levels, `Opaque`/`Strategy`, `opaque` blocks) and by laziness (`whnf`, keyed
matching with `kabstract`, lazy delta in conversion); meta solutions are filled in without
unfolding (`instantiateMVars`, smalltt never unfolds a solution). Caps on printing are common
and elide with `⋯` (Lean `pp.maxSteps` 5,000, Rocq `Printing Depth` 50); caps on work are
errors that ordinary `try` can't catch (Lean `maxHeartbeats`). Nobody has a size cap that is
a function of the call alone; Idris 2's fuel and 25-application meta threshold are the
nearest and depend on position. So this note's core (look as written, open a call only if
the answer could be inside, output terms folded) is what the others do, and its cap goes
beyond precedent in the direction D1280 chose: keeping D484's promise that searches see
through definitions, which none of the others make. From the study, this revision takes
eliding in messages (S2), memoising the reader on shared values as `kabstract` does (S4), a
note on smalltt's zonk (S5), a stage 0 count for recovered `E-RESOURCE` (S6) and the escape
hatch precedent for D2529 (S7); §8 and §9 say what it leaves.

## 4. The design

### 4.1 One meaning for "unfolded": the capped normal form

Every unfolded read-back in the elaborator's classified sites (§2.1–§2.4; not the kernel, not
`decide`, not output terms) means the same thing from now on:

> **The capped normal form** of a value is its normal form (as `quote` gives today), except
> that a glued call `f a⃗` is written as the call, its arguments read by this same rule, when
> **the capped normal form of its own unfolding** would have more than `CAP` nodes. A call
> that steps at once by matching (`matches_at_once`, `value.rs:584`) is never kept.
> `CAP` is 100,000.

The definition is recursive (review H2). Inside a call's unfolding, inner calls over the cap
are already kept, so they count as their folded size, and the call itself is kept only if
what is left still exceeds `CAP`. That keeps the *innermost* large calls and leaves the
small structure around them visible, which is what D1280 measured and what trip-journal
needs (the `album =>` bodies opened, the large helpers inside them kept). The rejected
alternative, keeping a call when its *full* unfolding is over `CAP` (what draft 1's "computed
with `quote_at_most`" would have done, since `quote_at_most` reads fully unfolded,
`value.rs:1917`), keeps the outermost call and hides everything small inside it. D2533.

Three rules make "a function of the call alone" true in the code, not just in the definition:

1. **Fixed limits.** The size test runs inside its own attempt with fixed limits, as
   `cheaply` does (`unify.rs:2566–2574`, budget's `attempt`, build-independent since SW-962):
   size `CAP + 1`, and a work limit that is a fixed multiple of it. Never the enclosing
   operation's limits: `quote_as` drops a cap not below the current size limit
   (`cap.filter(|&cap| cap < limit)`, `value.rs:1993`), and many read-backs run inside
   `cheaply`'s size 10,000 (`omega.rs:2365`, `:2386`, `ring.rs:944`). There the same call
   would be "an error", not "kept", and a needle read inside an attempt would differ from its
   goal read outside. Running out of the test's own work limit counts as "over the cap"; the
   test never takes from or exhausts the enclosing budget beyond its fixed cost. **[checked
   the two code facts; the rest is the design]**
2. **The cache key.** The answer is cached per declaration by the call: its definition and
   its arguments read back folded (D1280's proposal, goal-readback.md §5), together with the
   meta epoch, dropped when solutions are undone, as `Unfolding` does (`value.rs:56–71`).
   Not by the call's cell: D1280 measured that "the kept calls are mostly fresh cells", and
   on the branch `project_call` makes a new `Unfolding` cell for every field
   (`value.rs` (branch):1820–1830), so `(f x).i` would always miss. On the branch the key
   includes the spine's projections (`Frame::CallField`, review L4). **[checked]**
3. **Fixed in the language.** `CAP` decides what goes into elaborated terms, and so hashes.
   It is a constant in `crates/core`, not a field of `Limits` a user or test harness can
   change, so the check cache needs no key for it (review Q3). Unit tests that need a small
   cap use D1280's repro (`grow x 40`) at the real cap rather than a smaller one. D2529.

**What is not bounded.** Calls that step at once are never kept (D1280's third lesson), so a
recursion driven by a number literal (`settle x k 1000`, whose case on the rounds meets a
literal at every level, `value.rs:584–604`) has a capped normal form as large as today's
normal form, and still ends in `E-RESOURCE`. The folded read-back looks through those calls
too (`Readback::Folded`, `value.rs:1952`). Stage 4 of goal-as-written.md is what rescues such
goals today (`examples/reject/as-written-unconfirmed-slow-check.sw:19–21`, `settle x k 40`),
and it stays for them (D2534). Outside these calls, the capped normal form of a goal is
bounded by the size of its as-written layer times `CAP`. **[inferred]**

The capped normal form is a *definition*. It doesn't have to be built.

### 4.2 The reader: asking the capped normal form a question without building it

One module in `crates/core` (`readback.rs`, next to `quote_as`) answers the questions the
sites ask, by walking the value **as written** (as `quote_folded` does) and unfolding a call
only when the answer could depend on what is inside it:

- **`find(value, needle)`**: the occurrences of `needle` in the capped normal form, in
  pre-order, each handed to the site's own comparison (a key match, then `same` or
  unification, as today). It returns, with the occurrences, the set of calls it opened, so
  the site can build the motive from the goal with those calls unfolded (§4.3).
- **`mentions(value, vars, metas)`**: whether the capped normal form mentions any of these
  variables or unknowns.
- **`same(a, b)`**: whether the two capped normal forms are equal as terms (today's
  `matching::same` on two read-backs). Two calls with the same definition and arguments
  equal as terms are equal without opening; otherwise both are opened. This is for `cases`'
  seen and known sets, which keep exact comparison (§4.3).
- **`unfold_where(value, pred)`**: the term read back folded, except that the calls `pred`
  picks are unfolded (by the same rule, recursively). This is for zonk: the calls whose
  arguments mention an unsolved unknown.
- **`shown(value, budget)`**: the capped normal form for display: unfolded up to `budget`
  nodes, then each remaining call written as the call and anything else as `⋯` (study S2).
  For messages only; never part of an elaborated term, so its dependence on position is
  harmless.

**When a call can be skipped.** For a glued call `f a₁ … aₙ` (or a closure, which is a body
and an environment), only one rule, the free-variable rule. The draft's "heads" rule (skip a
call whose definition can't reach the needle's head) is left out of stage 3 entirely: an
occurrence's head can also come from a native's result, a dictionary stored in a body, a
definition named only in a type argument, or one opaque here but not elsewhere (review L2).
It comes back only if stage 3 measures that the free-variable rule isn't enough, and then
with the study's S3 (a stored per-definition fact).

1. **The needle's relevant variables.** Today's search compares each keyed candidate by
   **unification** (`Search::decide`, `rewrite.rs:1404–1408`), not by syntax, and
   unification looks past some positions and solves some unknowns. So the variables that an
   occurrence *must* contain are fewer than the needle's free variables. The **relevant
   variables** of a needle are the variables and frozen unknowns free in **its capped
   normal form** (not its folded form: `keep a b := a` does not need `b`), **outside**:
   - *proof positions*, which the unifier treats as equal without looking inside
     (`proof_position`, `unify.rs:1839–1861`); so `h` in `List.get xs i h` is not
     relevant, and a candidate `List.get xs i h'` inside `g xs i` is still found;
   - *unknowns the comparison may solve*, with the variables they are applied to: the
     rule's own unknowns (`rule_metas`, `rewrite.rs:1270–1271`) and any other unfrozen
     unsolved unknown in the needle, since a solution may ignore its arguments; in
     `rewrite foo _`, `_` contributes nothing;
   - *variables of a record type whose every field is a proof or of such a type*, if the
     unifier has eta for them, since such a variable converts to a constructor that doesn't
     mention it. **[inferred; stage 3 checks whether the branch's unifier does this]**

   They are computed again after `interfaces::refresh` re-reads the needle mid-search
   (`rewrite.rs:1395–1402`), so a solved instance can only widen them. A needle unknown
   solved mid-walk also widens them; computing them once is still safe, because it only
   prunes less (review §2). **[checked the three code positions; the rule is the review's H1
   fix]**
2. **Skipping.** If some relevant variable of the needle is mentioned by no argument of the
   call (with solved unknowns replaced, as `force_solved` does), the call's capped normal form
   can't contain an occurrence, and the call is read as written. Otherwise it is unfolded one
   step (`unfold_once`, `value.rs:570`, which keeps the calls it returns as calls) and the
   walk goes on inside. A needle with no relevant variables (a closed needle, a number, a
   constructor) prunes nothing: today's cost, but correct. Unsolved unknowns in the *goal* are
   applied to every variable in scope (`fresh_meta`, `check.rs:955–967`), so an argument
   holding one opens the call: conservative. **[inferred: the substitution lemma; it holds
   because definitions are closed terms]**
   `mentions` uses the same rule with `vars` in place of the relevant variables.
3. **The cap.** A call over `CAP` (§4.1) is read as written: that is the definition, not a
   heuristic of the reader.
4. **Memoised on shared values** (study S4). A shared value is visited once per question:
   the reader remembers, per value cell and per question, "`find` found nothing here" and
   "`mentions` is false here", within one meta epoch. Only negative answers are remembered,
   as `kabstract` does, so a positive `find` is walked again and the pre-order is kept. This
   makes the reader's cost follow the value's graph, not the tree that today's read-back
   writes out, which is exactly the trip-journal shape (§1.2).

Under these rules the reader opens every call whose unfolding could change the answer, in
the order the full read-back would visit them, so its answers are meant to equal those on the
capped normal form built whole. That is a claim **checked by a both-ways switch**, not one
that "can't" fail: stage 3 runs every question both ways (on the reader and on `quote_capped`'s
term) under a debug switch and panics on a difference. Because std may not contain the cases
that broke draft 1's rule, stage 3 also has **one planned unit test for each**:

- *proof position:* needle `List.get xs i h`, goal `… g xs i …` where `g`'s unfolding holds
  `List.get xs i h'`; the occurrence is found;
- *rule unknowns:* `rewrite foo _` whose left side holds the rule's unknown, against a goal
  where the occurrence is inside a call; found, and the unknown solved as today;
- *folded needle variables:* needle `keep a b` (`keep a b := a`), goal holding `f a` whose
  unfolding is `a`; found;

and a fourth for `refresh` (an instance solved mid-search changes the needle), and one for
values stored differently (`Chars` against `Cons`, `Nat` against `Succ`, near the cap; review
L3).

Why this bounds trip-journal: a needle like `List.appendNewBy entries entries (…)`
(`Self.sw:78`) has the relevant variable `entries`, which the arguments of the `album =>`
bodies' helpers don't mention, so those calls are never opened, however large their
unfolding. A needle that mentions only `trip`, in a goal where everything mentions `trip`,
is where the reader opens much and the cap and the memo do the bounding. **[inferred:
stage 0a measures how much is opened]**

**Undo.** The reader only reads. It solves no unknown, and the comparisons it hands
candidates to are the sites' own, inside the snapshots they already take (`hidden_copy`,
`rewrite/as_written.rs:390`; `todays_instance`, `:448`). "Undo every failed attempt" holds as
it does now. Its memo and the cap cache are keyed by the meta epoch, so an undone solution
can't leave a stale answer. **[checked]**

### 4.3 Each site

| Kind (§2) | Today | With this design | Changes on `main` below the cap |
|---|---|---|---|
| **Searches** (§2.1) | read back whole, search the term | `rewrite`, `match`, `cases` and the transport keep their as-written search first (goal-as-written.md stages 1–3). The completeness check (`hidden_copy_in`), today's instance (`todays_instance`), the survival and agreement checks (`matching/as_written.rs:649–690`), `generalised_now`, the transport test and the fallback search use `find`. On success the motive is built from the goal with only the opened calls unfolded (D2538). `cases`' seen and known sets use `same`, so they keep exact comparison. | motives and next goals partly folded where the fallback search runs (D2538); none in `cases` |
| **Mentions** (§2.2) | read back whole, look | `mentions`: exact, in both directions, so `bind.rs:95` stays as permissive as today. `KNOWN_CAP`'s "too large means may" (`unify.rs:978`) stays, harmless. | none |
| **Zonk** (§2.3) | `unify.rs:2779` re-reads the whole solution unfolded | `unfold_where(solution, args mention an unsolved unknown not kept)`: the calls today's fallback must unfold, folded everywhere else. `refold` gets the same mixed form of a `let`'s value as a third form beside `both_forms`' two, so it still finds the `let`. | solution terms smaller where the fallback fires; hashes there move |
| **Messages** (§2.4) | each note reads both sides back | each side read once per error, as `shown(value, NOTE_BUDGET)` (10,000 nodes, as `cheaply`), shared by every note through a cache on the error being built. A large side is elided with `⋯`, not dropped. `first_difference_note` locates the difference by walking the two values, so a difference inside an elided part is shown, never reported as "no difference". | note text where a side is over 10,000 nodes (`⋯`) |
| **Output terms** (§2.5) | `quote` | `quote_folded`. | hashes (§6) |
| **`decide`** (§2.6) | `quote` of the whole proposition, re-evaluated unglued | `quote_folded`, re-evaluated unglued, search unchanged. No cap, no size fallback. `from_yes`'s goal folded (§2.5). | none expected; `fromYes` hashes (§2.5) |

**Zonk, and smalltt's alternative** (study S5). smalltt never unfolds a meta solution: it
checks it up to unfolding and writes an `Irrelevant` placeholder where a variable is out of
scope but vanishes on unfolding. That keeps solutions folded everywhere, but Stitchwort's
kernel checks every elaborated term, and a placeholder is not a term it can type. So
`unfold_where` unfolds the calls instead.

**Programs** (review M5). Above the cap, a kept call can change *which* well-typed term the
elaborator picks: an instance (`interfaces.rs`, unclassified), whether a default fires
(`lib.rs:4954`). The kernel accepts any well-typed dictionary, so a program could compute
something else with no error. Proofs are safe (any proof of the goal is a proof); programs are
not. So instance search and defaults never choose on a capped form that kept a call: where
their read-back keeps one, they fail with the "left as it is" note and ask for an
annotation, rather than choose. This happens only above the cap (D2539). Stage 0b classifies
`interfaces.rs` before stage 2 switches `Ctx::quote`.

**Stage 4's paths** (goal-as-written.md, "unconfirmed"). Where the search ran on a capped
normal form that kept a call, its answer is complete by §4.1's definition, so for that cause
there is nothing unconfirmed to warn about: `W-REWRITE-UNCONFIRMED`/`W-MATCH-UNCONFIRMED` go,
and D1280's note takes their place, on failure only: "`f a b` was left as it is: its unfolding
is larger than 100,000 nodes". The paths stay for their two other causes, which the cap
doesn't touch (review H3): a call that steps at once whose unfolding still overflows
(`settle x k 40`), and an exhausted search budget (`E-REWRITE-BUDGET`,
`rewrite/as_written.rs:27–35`). D2534.

**A recovered `E-RESOURCE`** (study S6). Today a read-back that runs out of size is
recoverable (`undo.rs:126`), and sites that swallow it with `.ok()` can then take a different
branch, so a result depends on where a shared budget ran out: what D1280 ruled out for the
cap. After stage 6 the size limit should almost never be reached from §2's sites. Stage 0c
counts the declarations where a recovered `E-RESOURCE` changes what is elaborated on `main`
and the branch. If there are none, D2540 asks to make it a rule that it fails the declaration
instead, as Lean's runtime limits do (`tryCatchRuntimeEx`).

## 5. D484, revisited, and why it is safe

**What D484 becomes.** "The elaborator's searches look at the goal as written first. Where
they need what a call computes to, they look inside that call only, and never inside a call
whose own unfolding, with its large inner calls kept, is larger than 100,000 nodes. Below
that size, what they find is what they found by unfolding the whole goal." D484's promise
("every existing proof keeps working") is kept wherever no call in the proof is that large,
and with D2538 the next goal after a fallback search is shown partly folded. `decide` keeps
D484 exactly, with no size condition (§2.6).

**Soundness.** Nothing here touches the kernel's rules. Every motive is still type-checked
(`check_motive`, `rewrite.rs:1585`, `matching.rs:1587`), every term the elaborator writes is
still checked by the kernel, and a folded and an unfolded term are convertible. A wrong
answer from the reader could make a proof fail or pick a different (still checked) term, but
it can't make a false statement check. For *programs*, a different well-typed term can mean a
different result; that is why instance search and defaults don't choose on a form with a kept
call (§4.3, D2539). **[inferred, as goal-as-written.md §4; review §1]**

**Completeness and agreement with today.** Four properties, each tested in its stage:

1. *The reader agrees with the capped normal form.* For every question, the reader gives the
   answer the capped normal form built whole gives: same occurrences, same order, same bit.
   Checked by the both-ways switch and the H1 unit tests (§4.2), not assumed. With it, "agree
   with today's choice of instance" holds: the first occurrence in pre-order is the same one.
   "No extra copies" holds too: the completeness check sees exactly the copies today's
   search would replace.
2. *Below the cap, the capped normal form is the normal form.* By definition.
3. *Nothing reaches the cap, on `main` and with record eta, outside trip-journal.* This is a
   measurement, stage 0c's: the largest capped single-call unfolding met by any classified
   read-back over std, AoC, the roguelike and the examples, on `main` and on `lane/SW-1642`.
   D1280's margin (at 10,000 one AoC proof broke, at 100,000 none) was before record eta and
   on fewer sites (review H4). If 0c finds a call over the cap outside trip-journal, that
   proof is looked at before stage 2 lands.
4. *Each stage's term changes are named.* §4.3's last column; each stage says which
   `hash_stability` snapshots it expects to move, and the snapshots show it.

With these, a proof that checks today on `main` checks with the same result, except for the
term changes in §4.3's last column. The behaviour changes only where some call's capped
unfolding exceeds the cap: today such a goal either fails with `E-RESOURCE` (above
10,000,000 in all) or succeeds slowly between the two bounds. The second case is the
regression risk, the same one D1280 accepted, and stage 0c says whether it is empty.
**[inferred]**

**What doesn't come back.** Lean's rule (rewrite only what is visible) stays rejected for
calls below the cap: the completeness check still reaches into hidden copies (days 10 and 14,
`Result.traverseCons`, `List.foldMaxMem`; goal-as-written.md Q4).

**Time.** On `main`, the reader opens a subset of what today's read-back builds, and with the
memo it visits a shared value once, so it should be faster than today wherever it replaces a
whole read-back. The catch is each cap test, which costs up to `CAP` nodes per large call,
once per declaration per call (by its key) and epoch. **[inferred; stage 3 measures std, AoC
and the roguelike, within D2536]**

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
  and `fromYes`'s goal move the same way. Not a cost (migration cost doesn't count), but the
  stage's lane re-records them.

**A check for the stage:** whether gluing is on when `accessors` runs. If it isn't,
`quote_folded` is `quote` (`value.rs:1924`: "Without gluing … this is `quote`"), and the
field type must be evaluated with gluing on first. Data declarations are elaborated inside
`check_component`, which runs under `glued` (`module.rs:404`), so I expect it is on.
**[inferred]**

## 7. Stages

Each stage is one lane, merged to `main` on its own. Each says what it changes on `main`
(§4.3's last column) and which snapshots it expects to move. Stages that change elaborated
terms or search behaviour get an Opus review (D2364). Estimates are from similar lanes: the
goal-as-written stages took about 120 min per consumer.

- **0a. Trip-journal's failures, on the branch.** On `lane/SW-1642`, a counter or backtrace
  on every read-back over 1,000,000 nodes, trip-journal only. Out: which sites fail; which
  definitions (the error's note, `module.rs:677`); whether it also runs out of *work*, not
  just size; whether accessor types and `decide` are among the failures; how large the folded
  read-backs are; whether the kernel's `check.rs:378` or `substitute` is reached. Sonnet,
  30 min, one targeted run. *Risk:* none to behaviour. **First, before anything else.**
- **0b. The remaining sites classified** (no build). The ~200 unread sites into §2's kinds, as
  a table appended to this note: `interfaces.rs` first (M5), then `equations.rs` (stays
  unfolded or folded per site; §9), `omega.rs`, `effects.rs`, `derive_induct.rs`. Sonnet,
  60 min, alongside 0a or 1.
- **0c. The measurements** (no behaviour change). `STITCHWORT_READBACK_METRICS` (as
  `STITCHWORT_MATCH_METRICS`): per unfolded read-back, its site and node count; the largest
  capped single-call unfolding; the largest unfolding of a call that steps at once (H3); how
  often the same kept call is met again, by key against by cell (M4); message sides over
  10,000 nodes; recovered `E-RESOURCE`s that change what is elaborated (S6). Over std, AoC,
  the roguelike and the examples, on `main` and on `lane/SW-1642` (H4), within D2536. Out: is
  100,000 still safe with record eta; D2540's count. Sonnet, 75 min. Before stage 2 lands.
- **1. Output terms folded and `decide`** (§2.5, §6, §2.6). `shared.rs:246` and the rest of
  §2.5's table to `quote_folded`; `decide` reads back folded and evaluates unglued (M3), with
  a both-ways debug switch over std comparing the decisions' terms. Float pins, hash
  snapshots and the bound-to-the-prelude tests updated. Accept: accessor types print as
  declared (a snapshot of `Float.valid`'s and of a dependent field's type);
  `examples/accept/and-or-not.sw` keeps `Nat.decLessEq y 9`; the float gate and examples'
  hash snapshots re-recorded. *Moves:* hashes of accessors and their dependents, record
  updates, `fromYes`. Sonnet, Opus review (kernel terms change), 75 min. Can start now; its
  priority for SW-1667 depends on 0a. *Risk:* a proof that relied on an accessor's type being
  in normal form for a syntactic test; goal-as-written.md's fallbacks should cover that.
- **2. The capped normal form, built whole** (§4.1). `quote_capped` in `value.rs`: the
  recursive rule, the size test under fixed limits, the cache by key and epoch, never keeping
  a call that steps at once, `CAP` a constant. `Ctx::quote` and the free `quote` calls in the
  classified sites use it. No laziness yet. Unit tests: D1280's repro (`grow x 40`);
  "the result is the same wherever the call sits", inside and outside a `cheaply` attempt,
  and with values stored differently (L3); innermost kept, outer visible. The lane also runs
  trip-journal on a scratch merge into `lane/SW-1642`, extending `quote_capped` for projected
  calls (`Frame::CallField`, L4); that extension is handed to SW-1667 as a commit. *Moves:*
  nothing on `main` if 0c found nothing over the cap. Opus (core read-back), 120 min. Needs
  0b's `interfaces.rs` classification and 0c. *Risk:* time, 6× on rogue2q in D1280 before a
  working cache.
- **3. The reader** (§4.2). `readback.rs`: `find` (with opened calls), `mentions`, `same`,
  `unfold_where`, `shown`; relevant variables; the free-variable rule; the cap; the memo. No
  head rule. Tests: the five unit tests of §4.2 and the both-ways switch over every read-back
  of std. Used by no site yet, so it changes nothing. Opus, 200 min: it must match today's
  pre-order exactly, interleave with unification and `refresh`, and return what the motive
  needs.
- **4. Mentions and zonk onto the reader** (§2.2, §2.3): `check.rs:3889`, `bind.rs:95/99`,
  `matching.rs:434`, `lib.rs:4954`, `rewrite.rs:707/1690`, `matching.rs:1685`,
  `cases.rs:1582`, `unify.rs:978/177`; `unify.rs:2779` to `unfold_where`, with `refold`'s
  third form. Accept: the SW-323 tests (`ignorable`), zonk's tests in `unify.rs`. *Moves:*
  solution terms where zonk's fallback fired (0c counts them). Sonnet, Opus review, 75 min.
- **5. Messages onto `shown`** (§2.4), one read-back per side per error, eliding with `⋯`.
  Accept: E-REFL and E-TYPE-MISMATCH snapshots unchanged below 10,000 nodes; a new snapshot
  with a large side shows `⋯` and the difference. *Moves:* note text only. Sonnet, 60 min.
- **6a. `rewrite`'s searches onto `find`**: the completeness check, today's instance, the
  fallback search, `rewrite/under.rs`, the flipped-rule message; motives from opened calls
  (D2538); the unconfirmed path removed only where the cap kept a call, with the "left as it
  is" note (D2534). Accept: goal-as-written.md's `rewrite` accept examples and stage 1
  repros unchanged; `examples/accept/as-written-unconfirmed.sw` still warns where its cause
  is the search budget or a literal; day 11's `settledExactly` still checking. *Moves:*
  motives where the fallback runs. Opus, 120 min. Both-ways switch over std, AoC and the
  roguelike once (D2536).
- **6b. `match`, `cases` and the transport onto `find` and `same`**: `generalised_now`, the
  survival and agreement checks, `normals`, the transport test, `cases`' sets by `same`; the
  `match` unconfirmed path as in 6a. Accept: `examples/accept/match-equation-as-written.sw`,
  the stage 2 repros, `examples/reject/as-written-unconfirmed-slow-check.sw` unchanged (its
  cause is a literal). *Moves:* `match` motives where the fallback runs. Opus, 150 min (three
  consumers). Both-ways switch as 6a.

Draft 1's stage 7 (`decide`) is now part of stage 1.

Then: folded-calls.md's D484 entry and goal-as-written.md's stage 4 get a line pointing here.
`docs/syntax.md` ("rewrite", "Generalised `match`") says that a call larger than the cap is
looked at as written. That is a user-visible rule, so the language guide's proofs chapter
says it too (stage 6a's lane).

**What unblocks SW-1667.** Correctness: trip-journal on the branch elaborates with no "too
large to show". That needs stage 2 plus, for each kind of site 0a finds failing, the stage
that moves that kind: 1 if accessors, record updates or `decide` fail; 4 if mentions or zonk;
5 if messages; 6a/6b if searches. Speed: trip-journal takes at most about twice its time on
`main`. Without the reader each kept call costs up to `CAP` per read-back that meets it
(M6), so the plan expects SW-1667 to resume after 6b, and resumes it earlier only if 0a and
the stage 2 scratch run show it can. Stages 3 to 6b continue on `main` in any case (D2537).

| Stage | Model | Est. | Needs |
|---|---|---|---|
| 0a | Sonnet | 30 | — |
| 0b | Sonnet | 60 | — |
| 0c | Sonnet | 75 | D2536 |
| 1 | Sonnet + Opus review | 75 | D2523, D2535 |
| 2 | Opus | 120 | 0b (`interfaces.rs`), 0c, D2519, D2533 |
| 3 | Opus | 200 | D2520 |
| 4 | Sonnet + Opus review | 75 | 2, 3 |
| 5 | Sonnet | 60 | 3 |
| 6a | Opus | 120 | 2, 3, D2534, D2538 |
| 6b | Opus | 150 | 6a |

About 16 hours of lanes in all, of which 0a, 0b and 1 can start at once.

## 8. Decisions

Unchanged numbers keep their meaning; replaced ones say by what. The review's four missing
questions are D2533 (the cap's definition), D2538 (motives), D2539 (programs) and D2534
(stage 4's paths).

- **D2519** (kept). Make every unfolded read-back in the elaborator's **classified** sites
  (§2.1–§2.4) mean the **capped normal form**: today's unfolded form, except that a call
  whose own unfolding is over 100,000 nodes is kept as the call. Not the kernel; not `decide`
  (D2535); not output terms (D2523). This revives D1280, deferred on 26 Oct, and extends it
  from `rewrite`/`match` to every classified site. [rec: yes. It is a function of the call
  alone, so needles and goals read alike, which no other system manages (§3.2). Stage 0c
  checks the cap is safe with record eta before stage 2 lands.]
- **D2520** (kept). Answer the sites' questions with **one shared reader** that walks the goal
  as written and opens a call only when an occurrence could be inside (its arguments mention
  every relevant variable of the needle, §4.2), with no head rule for now, and its answers
  checked against the capped normal form built whole by a both-ways switch and unit tests.
  [rec: yes. It is what makes "look as written, unfold only what's needed" exact rather than
  a heuristic, unlike goal-readback.md's one-level `look`.]
- **D2521** (withdrawn, replaced by D2534).
- **D2522** (withdrawn, replaced by D2535).
- **D2523** (kept). Read back folded **all** the output terms of §2.5, not only accessor types
  (D2514): a record update's annotations, `fromYes`'s goal, elaborated binder types,
  scrutinee types in motives, kernel inference inputs. Not `equations.rs`. Hashes and Float
  pins move in stage 1. [rec: yes. Same reason as accessors, the same stage, and one hash
  churn instead of several; the review found no later syntactic use of these terms.]
- **D2524** (withdrawn, replaced by D2536).
- **D2528** (withdrawn, replaced by D2537).
- **D2529** (kept). `CAP` stays fixed at 100,000 with no per-proof syntax to lift it (D1281,
  deferred with D1280), and it is a constant of the language, not a user-settable limit.
  Every other system has a per-proof escape (study §3.6); here it is the "unfold this by
  name" kind, `rewrite f` or `f.unfold` (D1433, still open), as Lean's `unfold` and
  ssreflect's `rw /f`. [rec: yes, until a proof needs more. A numeric setting would make
  hashes depend on it; precedent says an escape is needed, not a number. If a proof needs to
  see inside a kept call before D1433 is built, that is when to decide D1433.]
- **D2533** (new; the cap's definition). A call is kept when **the capped normal form of its
  own unfolding** (inner large calls already kept) is over `CAP`, so the innermost large
  calls are kept and what surrounds them stays visible; the size test runs under fixed limits
  of its own; its answer is cached by the call's definition and arguments read back folded,
  and the meta epoch. [rec: yes. It is the rule D1280 measured, the one trip-journal needs,
  and the only one under which the same call is kept wherever it sits. The alternative, by
  the call's full unfolding, hides everything inside the outermost large call.]
- **D2534** (new; replaces D2521). Remove `W-REWRITE-UNCONFIRMED` and `W-MATCH-UNCONFIRMED`
  only where the cause is a call the cap kept (stage 6a/6b), with D1280's note on a failed
  search in their place: "`f a b` was left as it is: its unfolding is larger than 100,000
  nodes". Keep stage 4's paths and warnings for their other two causes: a call that steps at
  once whose unfolding overflows (a literal-driven recursion), and an exhausted search
  budget. [rec: yes. Removing them all would turn some of today's warnings back into
  `E-RESOURCE` (review H3). Attaching the note to a *later* `E-REFL` in the same proof is a
  good idea for a follow-up ticket, not this plan.]
- **D2535** (new; replaces D2522). `decide` reads the proposition back **folded** and
  evaluates it with gluing off, then searches as today. No size threshold, and
  `decide_as_written` only for what it does today (a stuck decision). It moves to stage 1.
  [rec: yes. The code reads back unfolded only to get a value with no glued calls, which
  evaluating unglued already gives (§2.6), so it makes today's decisions (`y < 10` still by
  `Nat.decLessEq y 9`) without the blowup. Stage 1's both-ways switch confirms it. Lean's way,
  reducing the decision lazily with no read-back at all (study S1), is a later option.]
- **D2536** (new; replaces D2524). Test strategy, as an exception to the lane test budget: 0c,
  2, 3, 6a and 6b each run one check of std, AoC, the roguelike and the examples in the
  background (metrics or the both-ways switch on), on `main`; 0c and 2 also on
  `lane/SW-1642` (or a scratch merge into it); each run stopped at 6 minutes, as D2507's
  verifier is. 0a runs trip-journal only. [rec: yes. "Nothing changes on `main`" and "the cap
  is safe with record eta" are measured claims, and these are the stages that rest on them.]
- **D2537** (new; replaces D2528). Order: 0a first; 0b and 1 alongside; 0c before 2; then 3,
  4, 5, 6a, 6b. SW-1667 resumes once every kind of site that 0a finds failing has moved and
  trip-journal takes at most twice its time on `main`, expected after 6b; the stages continue
  on `main` in any case. [rec: yes. 0a costs 30 minutes and decides how much of the rest
  record eta waits for; planning for 6b avoids a resume that stalls (review M6).]
- **D2538** (new; motives). Where the fallback search runs, the motive (and so the `J` term,
  its hash, and the next goal) is built from the goal with only the calls the reader opened
  unfolded, not from today's whole normal form, so it comes out partly folded, on `main` too.
  [rec: yes. It is checked by `check_motive` and the kernel, it is the kind of change
  goal-as-written already accepted, and the user sees a next goal close to what they wrote.
  The alternative, building the whole capped normal form on success, keeps today's terms but
  pays a whole read-back per `rewrite`, which is the cost this note removes.]
- **D2539** (new; programs). Instance search and defaults never choose on a read-back that
  kept a call: there they fail with the "left as it is" note and ask for an annotation.
  Proof searches may use kept calls. [rec: yes. Above the cap a kept call could pick a
  different well-typed instance and change what a program computes with no error; an error
  costs little, since stage 0c is expected to find no such case, and nothing is silent.]
- **D2540** (new; deferred to stage 0c). A recovered `E-RESOURCE` should never choose between
  alternatives: where a size limit is still reached from §2's sites, the declaration fails
  instead of the error being undone and another path taken (study S6, Lean's runtime limits).
  [rec: decide after 0c: yes if it finds no declaration on `main` or the branch that depends
  on recovering; otherwise look at those first.]

## 9. What this note did not do

- It ran nothing (D2518, SW-1722). The size of trip-journal's read-backs, the definition that
  first passes the limit, the largest unfolding on `main` and with record eta, and the
  reader's speed are stage 0's or stage 3's measurements.
- It classified about 90 of the 290 unfolded read-back sites by reading them. The rest,
  mostly `omega.rs`, `effects.rs`, `derive_induct.rs`, `equations.rs` and `interfaces.rs`,
  are stage 0b's. `equations.rs` is narrower than draft 1 feared (review Q4): a lemma's left
  side is the definition applied to patterns, which read back the same either way. The sites
  that could change something are its binder types (`equations.rs:2833`), `bool_equation`'s
  right side (`:2532`), `uniqueness`'s sides (`:4445–4446`) and `mentions_computation`
  (`:5064–5072`), which decides whether an equation exists. Stage 1 leaves the file alone; a
  later stage that folds its binder types checks that `rewrite f.eq_k` proofs are unchanged.
- It doesn't revisit record eta's rule 2 itself (for instance, not firing under binders in
  the elaborator). D2514 chose to bound the read-backs instead.
- From the study: it doesn't take the head rule's stored reachability (S3), since the head
  rule is out of stage 3; or an inferred "abbreviation" status for keyed searches (S8),
  which changes what "as written" means and is a backlog idea; or per-declaration opacity
  beyond the existing `opaque def`, which every other system has but which the cap makes
  unnecessary for speed (study §3.4).
- It didn't check whether the branch's unifier has eta for records with only proof fields
  (§4.2 rule 1's third exclusion); stage 3 does.
