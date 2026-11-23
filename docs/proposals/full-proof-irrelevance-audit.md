# Full proof irrelevance: the same-type audit, redone for E2 (SW-4672)

**Status:** audit note, Fable paper lane SW-4672, 23 November 2026. It redoes §7.4 of
[proof-irrelevance.md](proof-irrelevance.md) (October, positional skips) for the end state
Matt chose in D3721, E2 of [full-proof-irrelevance.md](full-proof-irrelevance.md), whose
stages 4 and 5 wait on it. Nothing was built and no probe was run (section 9 says why). The
code was read at `71e566111`.

Marks: **[read]** I read the code cited today; **[listed]** I saw the call with a few lines
around it and classified it from those, without tracing its callers; **[inferred]** my
reasoning from what I read; **[not checked]** not looked at.

## 1. Summary

**The question.** Rule I of E2 says: when the checker compares two values and both are proofs,
they are equal, and it doesn't look inside. That is only right if the two proofs prove the same
statement, which the comparison can't see for itself: it has no types, only values. So every
place that starts a comparison has to hand it two values of one type. October checked that for
the rule of the time (proofs skipped at known positions). This note checks it again for rule I,
over today's code.

**The answer: stages 4 and 5 can go ahead.** I found no place where rule I would make the
kernel accept something false. The kernel itself starts a comparison in eleven places, all read
today, and all compare two types, or two values whose type it has just fixed. The elaborator
starts comparisons in about 330 places; some of those do compare values of different types, but
whatever the elaborator concludes the kernel checks again, so the cost of a wrong "equal"
there is a confusing error, never a false theorem.

**What changes from October.** Under today's rule a comparison of two values of different
types can only go wrong below a shared constructor (`MkBox p` against `MkBox q`). Under rule I
there is one new way: **the two values handed over are themselves proofs** (`h1: A` against
`h2: B` is "different" today and "equal" under rule I). So the audit reduces to: who can hand
the comparison two *proofs* of possibly different statements? Comparing two types is always
safe, because a type is never a proof (section 2).

**Conditions.** Five things to carry into the stage briefs, the first two for stage 4 (rules K
and S), the rest for stage 5 (rule I everywhere):

1. **Rule K needs a comparison inside evaluation, and evaluation has no count of the variables
   in scope** (finding A, the one that could become a soundness bug if missed). The comparison
   makes fresh variables from that count; a count that is too low can make two different
   functions look equal. Stage 4's design has to say where the count comes from.
2. **Two stuck casts, or two stuck matches on a proof, must be compared without handing their
   two proofs to rule I** (finding B): compare the casts' ends, then the motives, then the
   bases. Today they are compared through the proof's own head, which rule I removes.
3. **The "one side a proof, the other not" tripwire can't be on for the elaborator's calls**
   (finding C): a handful of them legitimately compare values of different types. On for the
   kernel's own calls only.
4. **In the unifier's one rule that pairs arguments of possibly different types, "both sides
   are marked as proofs" isn't enough to keep solutions well typed** (finding D): there, skip
   by rule I only when the two types are known and agree.
5. **Searches for an occurrence (`rewrite`, lemma search, the syntactic matchers) must not
   apply rule I to a whole candidate** (finding E), or a needle that is a proof matches every
   proof in the goal. Proofs are skipped only below a head that already matched.

Undoing failed unifications still holds (section 7), with one new thing to keep on the same
footing as today's: a cast that fired because of a solution later taken back.

**How far this audit goes.** The kernel's call sites and the body of the kernel's comparison
were read in full. Of the elaborator's roughly 95 calls of `conv` all were looked at with their
surrounding lines and about 20 read properly; of its roughly 230 calls of the unifier all were
listed, and about 15 read properly. Section 9 lists what was not checked. Because an unread
elaborator site can't be a soundness problem, I think that is the right depth for the time; but
it means "no elaborator site produces a confusing error under rule I" is **not** established.
Stage 3's marks make it measurable instead (section 8, first ticket).

## 2. What the precondition is under E2

*Types are never proofs.* A proof is a value whose type is a proposition. A type's own type is
a sort, and a sort is not a proposition; with unique sorts (`docs/core.md`, "Universes") that
holds for a variable `P: Prop`, a call `f a: Prop`, a cast between types and a match that
returns a type, since each is marked from its own type's sort. So a caller that compares two
types can never trigger rule I at the top, whatever the two types are **[inferred from the
note's section 4.3]**.

*Below the top, most pairs are typed by what is above them.* As October argued: parts at the
same position under a shared head have one declared type once the earlier parts are equal, and
the comparison takes parts left to right and stops at the first difference
(`value.rs:3977` `conv_with`; `:4650` `spine_pairs`) **[read]**. That covers constructors'
fields, data types' arguments, the arguments of one variable, definition, unknown or quotient
form, `Eq`'s type before its sides (`value.rs:4412`), a function type's domain before its
codomain, and bodies under one fresh variable. Rule I at such a pair is between two proofs of
one statement.

*Where that argument doesn't reach* is the subject of sections 3 to 6:

- the two values a caller hands over (the top);
- pairs the comparison forms without a shared head: two stuck eliminations of different proofs
  (section 4), and in the unifier `?m a` against `f b` (section 6);
- callers that go on after a difference, so later parts' types have already diverged
  (`unify_what_agrees`, `data_auto.rs:202`, the queue's postponed pairs).

*Soundness and well-typedness are different bars.* For the kernel the bar is soundness: its
comparison answering "equal" must be true in the model (each proposition has at most one
proof). For the elaborator the bar is lower: a wrong "equal" yields a term the kernel refuses,
or an ill-typed solution for an unknown. The second matters only because the elaborator
evaluates solutions before the kernel sees them, and ill-typed *data* has crashed the evaluator
before (SW-919, SW-924, `unify.rs:2683-2686`). An ill-typed *proof* can't, provided nothing in
the evaluator ever takes a proof apart; that is exactly rules K, S and F, and it becomes a
requirement on how stage 4 builds rule S's stand-ins (finding D).

## 3. The kernel's own calls

All **[read]**. `reference::conv` (`reference.rs:907`) has no caller outside tests; it mirrors
`value::conv` rule for rule (`:925-1408`, structure only, **[listed]**).

| Call | Compares | One type? |
|---|---|---|
| `check.rs:649`, `:691` | an inferred type against the expected one | both are types |
| `check.rs:746` | a constructor's result indices against the expected type's, in order, stopping at the first that differs | yes: index `k`'s type depends on the parameters (shared) and earlier indices (equal by then). Unchanged since October |
| `check.rs:815` | the two sides of an expected `Eq(ty, a, b)`, for `byComputing` | yes: `Eq` is formed at one `ty`. **This is where rule I makes `p = q` check for two proofs**, as intended |
| `unify_index.rs:181` | a binder's type with the left values against the same with the right values | both are types |
| `unify_index.rs:191` | the two sides of an index equation | yes: `:178-185` compares the two types first whenever the binder's type mentions an earlier binder; otherwise it is one type under the shared `base`. Under rule I an equation between proofs is always deleted here, as the E2 note says |
| `native.rs:507`, `nat_add.rs:422`, `float.rs:625`, `partial.rs:419` | a declared type against the shape a built-in expects | both are types |
| `pretty.rs:2491` | a written decision against the computed one, for display | both `Decidable p` for one `p`; display only |

`check.rs` has no other test of equality that decides acceptance (no `same_value`, no
`identical`; its one `unify` at `:1504` is `unify_index`) **[read by grep]**. The quotient
forms are typed through ordinary function types and reach `:649`/`:691` like anything else.

**Result: every kernel call is homogeneous.** The tripwire (one side marked a proof, the other
visibly data) can be on for these.

## 4. Inside the kernel's comparison

`conv_step`, `recurse`, `spine_pairs`, `stuck_same`, `stuck_different`, `same_stuck_trees` and
`same_trees_of` were read in full (`value.rs:4224-5068`); `native::compare`, the tree memo's
`identical` and `shape_hash` were not.

| Where | Pairs it forms | Under rule I |
|---|---|---|
| Glued calls of one definition, by arguments (`:4234`, `recurse` `Calls`); folded dictionaries (`Folded`); hidden opaque calls (`Sealed`); partial applications (`Underapplied`); the over-applied folded head (`same_spines` compares whole spines of equal length, `:4139`) | argument `k` against argument `k` of one definition, left to right, stopping at the first difference | typed by the definition's telescope. Fine. The shortcut mode goes; nothing here depends on it for typing |
| `CallMemo`, `Found::Equal` (`:4242`, SW-4647) | none: answers a pair of calls already compared | the key is the two unfolding cells' addresses, the level and the mode, so the same two values; a value has one type. The comment's claim "convertible depends only on them, the level and the mode" stays true in the kernel under rules I, K and S, which read only the values and their marks. Fine |
| Two neutral values with one head (`:4421`) | spine against spine | arguments typed by the head. **`Elim::J`: see finding B** |
| `Data` against `Data`, `Ctor` against `Ctor` (`:4390`, `:4401`) | arguments, fields | typed by the declaration; this is the case October covered |
| Lambda against lambda, eta (`:4367-4385`), `push_eta` (`:4724`), `codomains` (`:4019`) | bodies under one fresh variable | one type for both, so one mark for the variable: take it from the lambda, the function type or the definition's own lambda (`underapplied`, `:4743`). If two lambdas disagree on the mark, the precondition was broken |
| Record eta, rule 1 (`:4486`) | each field against the unknown's projection | typed by the constructor, given the top-level precondition (the code's own comment says so). A proof record never gets here: both sides are proofs first. Fine |
| Numbers and compact lists (`:4290`, `:4329`) | bases of sums; characters | `Nat`, `Char`. Fine |
| `same_trees_of`: two definitions stuck on a `case` (`:5025-5045`) | the two scrutinees; then branches with shared fresh fields; then leaves | **the scrutinees needn't have one type** (two different definitions; only the data type is known to be the same, `:5014`). See below |
| Quotient forms (`Head::Quot`, `value.rs:396`) | arguments of one form, left to right | typed by the form. `Quot.lift`'s proof argument is compared structurally today (no definition, so no inert marks); under rule I it is skipped. Fine |

**The scrutinee pair in `same_trees_of`** is the one place the kernel's comparison hands itself
two values whose types it hasn't fixed. It is harmless today and stays so for data: both
scrutinees are neutral (a constructor would have taken its branch, `:4861`), two neutral values
are equal only with one head and equal arguments, and then they have one type **[inferred]**.
Both are of one data type, so both are proofs or neither is: the tripwire can't fire here. If
both are proofs (a match on a proof that rule S couldn't fire: an indexed proposition whose
indices aren't yet equal), rule I would call two proofs of different statements equal. I
believe that is still true in the model (each call equals its only branch whenever its
scrutinee exists at all, so the calls are equal when the branches are) **[inferred]**, but it
shouldn't rest on rule I's precondition being quietly false. Finding B.

**Finding A: rule K's comparison has no level (stage 4; high if missed).** `conv` takes
`level`, the number of variables in scope, and makes its fresh variables from it
(`Value::var(level)`, `value.rs:4029`, `:4348`, `:4728`). That is a second precondition beside
same-type: `level` must be above every free variable of the two values. Every caller today has
a context to take it from. Rule K asks "are the cast's two ends equal?" *while computing a
head*, and evaluation has no level: `eval(g, env, term)`, `force(g, value)` (`value.rs:848`,
`:867`), and `Ev` holds none (`ev.rs:154`) **[read]**. The same goes for rule S's check of an
indexed proposition's indices. A level that is too low is unsound, not just incomplete: with a
free variable `v5` in scope, comparing `z => z` with `z => v5` at level 5 names the fresh
variable `v5` and answers "equal". Ways out, for stage 4's design to choose:

- fresh variables for comparisons started by the evaluator come from a reserved range no
  context reaches (levels from, say, 2^40 up, with contexts asserted below it). Simple, and the
  results of such a comparison are never read back, so nothing downstream sees the odd levels;
- or the cast is only ever "re-read" at sites that have a level (`conv`, the unifier, the
  kernel's `check`), and a `case` or native that meets a stuck cast during evaluation leaves it
  stuck. That loses computation (`run`-like evaluation inside the checker would stall on a
  cast), so I prefer the first;
- or compute a bound by walking the two ends for their highest free variable (closures
  included): correct, but a cost at every cast.

The reference evaluator needs the same answer. Confidence that the gap exists: high. Size: part
of stage 4's design, not a lane of its own.

**Finding B: stuck eliminations of two different proofs (stage 4; medium).** Today a stuck
`J P d p` is the neutral value "`p`'s head, `p`'s arguments, then `J{motive, base}`"
(`value.rs:2151`), so two stuck casts are compared head first: equal heads and arguments make
`p ≡ p'`, hence one `Eq` type, hence the two motives have one type, and only then are motive
and base compared (`spine_pairs`, `:4669-4682`) **[read]**. Rule I removes the first step (the
proofs are not looked at), and with it the reason the motives have one type: a motive is a
lambda, compared by going under its binders with no type at hand, so `y e => F y` at element
type `t` against the same text at `t'` would be compared under one shared fresh `y`. So:

- two stuck data casts are compared as: element type, the two ends (the cast carries them
  under E2), then motive, then base, left to right; the proofs never. Then every pair is
  homogeneous by construction;
- in `same_trees_of`, when the `case`'s data type is a proposition, skip the scrutinee
  comparison, as the code already does for a `case` with no possible branch (`:5017-5027`,
  whose comment gives the same reason), and for an indexed proposition compare the scrutinees'
  types' indices instead if a design keeps them at hand;
- rule K's own test is homogeneous as it stands: the ends `x`, `y` are both of the cast's
  element type. For rule S on an indexed proposition, compare the scrutinee's type with the
  constructor's result type as two whole types (or index by index, stopping at the first
  difference, as `check.rs:746` does), not the indices as an unordered set.

I could not construct an unsound comparison from getting this wrong (the casts are the
identity in the model whatever their proofs), so medium; but it is the one place where the new
rule deletes the step an existing invariant rested on.

## 5. The elaborator's calls of `conv`

About 95 outside tests (`grep` for `conv(` and `conv_now(` in `crates/elab/src`), all
**[listed]**, the ones named in the second and third groups **[read]**. None can affect
soundness: what the elaborator builds is checked by the kernel.

**Types against types** (the large majority; safe by section 2): a hypothesis's type against a
goal or a fact (`cases.rs:1506`, `:1518`, `:1558`, `:2078`, `:2509`, `:2525`, `:2528`, `:2602`,
`:2674`, `:3812`; `facts.rs:397`, `:858`, `:946`, `:1005`; `build.rs:97`; `goals.rs:462`,
`:2283`; `check.rs:1278`, `:2441`, `:4329`; `walk/mod.rs:586`, `:1153`, `:1995`;
`walk/two.rs:223`; `matching/as_written.rs:540`, `:683`; `rewrite.rs:1562`, `:2792`), declared
types against each other (`assume.rs:419`, `partial.rs:750`, `lib.rs:2983`, `congruence.rs:552`,
`shared.rs:177`, `derive.rs:244`, `dot.rs:284`, `reading.rs:198`, `:1045`, `:1955`,
`interfaces.rs:767`, `:1297`).

**Values of one type, for a reason at the site:** the two sides of an `Eq`
(`cases.rs:1453`, `:1486`, `:2504`; `omega.rs:274`; `facts.rs:930`, `:958`, `:1493`;
`walk/leaf.rs:65`; `counterexample/inputs.rs:459`; `equations.rs:6620`); tests of type `Bool`
(`cases.rs:1804`, `auto.rs:796`); atoms of one carrier (`ring.rs:958`, `omega.rs:2540`, the
carrier checked first, as in October); an instance written against the one found for the same
goal (`interfaces.rs:695`); a constructor equation's fields, dependent ones left out first
(`cases.rs:2052`, `:2189`, as October); the same term evaluated in two environments
(`equations.rs:2944`, `:4575`, `rewrite/as_written.rs:783`); rows at the same argument
positions (`partial.rs:805-806`); predicates' arguments in order (`derive_induct.rs:2592`); the
unifier's sum rule (`unify.rs:1255`, both `Nat`); `byComputing`'s two sides read back
(`check.rs:7268`).

The gold standard is `matching/as_written.rs:632-663` (`is_occurrence`): it asks the kernel for
the candidate's type and compares types **before** values, and says why in its comment.

**Values whose types the site does not fix** (finding C lists them): `data_auto.rs:202` (a
data type's arguments pairwise, going on after a difference; words a note only, as October
found); `check.rs:5283` (two environments position by position, to decide whether a `?`'s
statement can be shown); `walk/two.rs:157` (two scrutinees of one data type, parameters not
compared) and `:303-307` (an equation's sides against two variables found by name);
`cases.rs:3385` (a value against the values already known, **[listed]** only).

**Two that rule I turns into "always yes":** `equations.rs:2944` (does the left side change
when a proof variable becomes `byComputing`?) and `:4575` (`proof_is_inert_in`: does a branch
give the same value for two proofs `h`?). Both exist because of the positional rule and can be
deleted in stage 5. Until then they need their fresh variables marked as proofs (they make
variables beyond the context, `Value::var(depth)`), or they answer as today; either is safe.

**Finding C: the tripwire and the elaborator (stage 5; medium for the plan, no soundness
weight).** The E2 note wants "one side a proof and the other visibly not" to be an internal
error in test builds. `value::conv` is one function for the kernel and for these 95 callers,
and the third group above can legitimately hand it a proof against data. So: the tripwire is
armed by the kernel's own evaluation context (`Ev::kernel`, `ev.rs:164`) and by the reference
evaluator, and off for the elaborator, where the answer is a quiet "different". And "visibly
data" must mean a constructor of a data type in `Type`, a number, a sort or a type former, not
"a variable with no mark": an elaborator-made variable with no mark is the safe default
(losing an equality), and must not trip anything.

## 6. The unifier

### 6.1 Callers

About 230 outside tests and `unify.rs` itself, in 37 files, all **[listed]**. By far the most
are "the type found against the type expected" (`check.rs`'s 46, `numbers.rs`, `dot.rs`,
`records.rs`, `effects.rs`'s result and row types, `calc.rs:74`, `facts.rs`, `walk/*` against a
hypothesis's type). Values of one type: a placeholder against the checked argument it stands
for (`check.rs:4930`, `:5023`, `:5146`, `queue.rs:1544`, `interfaces.rs:1086`, `auto.rs:203`,
`:284`, `:1674`, `rewrite.rs:919`); the two sides of an `Eq` (`check.rs:7290`, `:7321`,
`auto.rs:389`, `calc.rs:289`); a named parameter against the one inferred (`check.rs:10396`,
typed by the telescope); ability labels' arguments and row tails (`effects.rs:796-868`, as
October: one ability's telescope; `Sig` has no parameters). Two do it the right way round,
types first and then values: `auto.rs:911` and `rewrite.rs:984`.

**Abilities and `Quot`** add nothing new: rows are compared as values of type `Sig` or as
arguments of one ability, and the elaborator's `quot.rs:252` compares types.

**Searches** are the family where the two sides are a pattern and an arbitrary candidate:

| Site | Types first? |
|---|---|
| `rewrite.rs:2315-2372` (the main search) | yes: the position's type against the carrier, then `has_carrier` (`:2467`) asks the kernel for the candidate's type **[read]** |
| `search.rs:1719`, `:1948`, `:1960` (lemma search) | when both types are known (`types_agree`, `search.rs:200`: an unknown type "doesn't rule a match out") **[read]** |
| `rewrite/as_written.rs:470`, `rewrite/repeatedly.rs:1879`, `rewrite/under.rs:340` | no: candidates are chosen by head (`key`) **[read]** |
| `closing.rs:481`, `:784`, `:874-876`, `:995` | no: a pattern against a lemma's side or conclusion **[listed]** |

**Callers that go on after a difference**, so later pairs' types may already have diverged:
`unify_what_agrees` (`unify.rs:143`, used on the way to an error message; its doc says a
solution beside a clash "may have the wrong type") and `unify_waiting` (`:109`), which sets a
blocked pair aside and unifies the rest. Both do this today at proof positions; rule I changes
the number of positions, not the kind of exposure.

### 6.2 Where the unifier itself pairs values whose types needn't agree

**`first_order` (`unify.rs:2687`)** **[read]**: `?m … x` against `f … y`, with `x` not a
variable, pairs `x` with `y` and then `?m …` with `f …`. The code says "unlike every other rule
here, this one pairs values that needn't have the same type". Its guards: `learn_types` unifies
the two types when both are fully known (`:2756`); `apart` refuses when both are known and
differ (`:2778`; "`false` whenever either type is unknown"); `NO_ETA` turns record eta off
while `x` and `y` are compared (`:2301`).

The E2 note's rule for this spot (section 4.3) is "the skip needs both sides marked". That is
**enough for soundness** (the kernel checks the result) and **enough for the evaluator's
safety**, on one condition: nothing ever takes a proof value apart. An ill-typed proof solution
(`?p := h` with `h` proving something else) then flows through evaluation as an opaque blank.
The condition is rules K, S and F as written; the place to be careful is rule S's stand-in for
"that field of the proof". If it is built as a projection, it must not index into a literal
constructor of some other proposition (the scrutinee's data type is checked before fields are
taken in `walk_tree`, `value.rs:4859`: "another type's constructor ... selects nothing"; the
stand-in needs the same care).

It is **not enough for well-typed solutions**. With `h1: A` and `h2: B`, today `?m h1 = f h2`
fails at `h1` against `h2` and the caller tries something else or postpones. Under rule I with
only the marks, the pair is "equal", and the rule goes on to solve `?m := f` when the types
weren't known in full (so `apart` said nothing): an ill-typed solution for a *data* unknown,
found where today there was none, reported later as a type mismatch somewhere else.

**Finding D (stage 5; low to medium, no soundness weight).** Inside `first_order` (that is,
while `NO_ETA` is set and the pair is the top of the nested comparison), apply rule I only when
`learn_types` unified the two types; otherwise treat the two proofs as today's code treats two
data values it can't relate: equal if identical (`same_value`), else the pairing fails. That
keeps every solution `first_order` finds today (identical proofs still pair) and adds none that
is ill-typed. Size: small, inside stage 5's unifier work.

**Record eta in the unifier** **[read]**: rule 1 (`unify.rs:2099-2112`, `push_fields` `:2132`)
pairs a constructor's fields with an unknown value's projections, typed by the constructor
given the same-type precondition, and is off inside `first_order`. A proof field against a
projection of a proof field is always "both marked", so the marks test adds nothing here; what
protects it is the precondition and `NO_ETA`, as today. `same_field_records` (`:2312`) pairs
the two *records* of `?b.items` and `b.items`: one data type, parameters not known equal. It
is a first try, undone if it fails, its solutions noted as lossy. A record with a projection
has a data field, so the records are never proofs, and proofs below them sit under one
constructor: the exposure is the positional one of today, unchanged by rule I. `same_field_types`
and `same_field_calls` (`:2904`, `:2972`) pair type parameters of one data type; their bodies
were **[not checked]**.

**Stuck trees and spines** in the unifier share the kernel's code (`same_stuck_trees`) and
shape (`spine_pairs`, `unify.rs:2572`); finding B applies to both.

**`proof_position` (`unify.rs:2635`)** is today's rule and rule I's too: a bare solvable unknown
on one side is solved with the other, otherwise nothing is looked at. Its solution is well
typed exactly when the pair is homogeneous, so it inherits whatever the pairing site
guarantees. With finding D it is homogeneous everywhere except after a clash in
`unify_what_agrees` (an error path) and beside a postponed pair in `unify_waiting` (as today).

### 6.3 Searches and the syntactic matchers

`matching::same` and `same_shifted` (`matching.rs:3043-3075`) are exact identity of terms
**[read]**; `rewrite`'s search tries them first, then unification. SW-4661 and the E2 note
(section 6.2) plan to make the syntactic matchers "compare modulo proofs, using the same
marks". `occurs` (`matching.rs:3030`) runs `same_shifted` over **every subterm** of the goal
against the needle: values of every type.

**Finding E (stage 5 and SW-4661; low, no soundness weight).** If rule I is applied to a whole
candidate, a needle that is a proof matches every proof in the goal, the motive abstracts all
of them, and the kernel refuses it ("the motive is not type correct") where today the search
finds the one occurrence or none. The same goes for the unifier-backed searches that don't
check types first (table in 6.1) and for `solve_abstracting` (`unify.rs:3203`), which looks for
occurrences of one stuck computation. The rule to write down once:

- at the root of a candidate, no rule I: a needle and a candidate that are both proofs match
  only if identical, or after their types were compared (`is_occurrence` is the model);
- below a head that already matched (`App(f, a)` against `App(f, b)` with the `f`s matched
  first, a constructor's fields, a data type's arguments), proofs are skipped by their marks:
  there the types are fixed by the head. `same_shifted` already goes function before argument
  (`:3073`);
- a `rewrite` whose left side is itself a proof does nothing useful under E2 (every such
  equation holds by `byComputing`); it could simply be refused with a message. Orchestrator's
  call or stage 5's, not Matt's, unless he wants the wording.

The equation generator's own matcher (`equations.rs:6527`, `same_but_proofs` `:7756`)
**[read]** skips proofs only in a matched constructor's fields and already stops at indexed
families "which may compare values of different types" (`:6555`, D2185). Fine as it is, and
it becomes an instance of the rule above.

## 7. Undoing failed unifications

**Still holds** **[read: `undo.rs:1-175`, `unify.rs:2553` `undo_since`, `:2635`
`proof_position`]**. The argument is October's and gets simpler:

- Rule I solves *fewer* unknowns than today: nothing inside a proof is solved, and a skipped
  pair leaves no state at all. The one solution it does make (a bare proof unknown against the
  other side) goes through `solve` and so onto `meta_trail`, where `undo_since` and
  `Snapshot::restore` take it back, as `proof_position` already does itself when `solve` fails
  part-way (`:2642-2646`).
- `same_arguments_solving_nothing` (U1, `:2529`) keeps working: it sees the trail grow and
  undoes (`:2545-2547`).
- The remembered answers (`CallMemo`, the tree memo) are safe: an "equal" found by rule I
  doesn't depend on any solution, and "different" is only remembered for pairs with no unknown
  in them (`value.rs:5077-5089`).

Three things E2 adds that must be put on the same footing, none of them a hole today:

1. **A metavariable's mark** ("its type is a proposition", "unknown" until the type's sort is
   solved). If it is stored once computed, it is state that a taken-back solution can make
   stale. Derive it from the type on demand, or record its changes on the trail. Going from
   "unknown" to "proof" only adds equalities, which is the direction the tree memo's "equal"
   entries already allow.
2. **A cast that fired because of a solution.** In the elaborator rule K's test can succeed
   because an unknown in the ends was solved inside an attempt. The value computed from it (in
   a glued call's kept unfolding, say) must not outlive the attempt. The E2 note says casts are
   re-read "as kept unfoldings are (`meta_epoch`)"; taking a solution back already starts a new
   epoch (`metas_taken_back`, `unify.rs:2557`). I did not trace how kept unfoldings use the
   epoch, so this is a requirement stated, not a property checked **[not checked]**.
3. **Rule K's test must solve nothing.** It runs inside evaluation; a comparison there that
   solved an unknown would be a solution with no caller to undo it. It must be `conv`-like
   (read-only), never the unifier.

## 8. Findings, and what to put in the stage briefs

| | Finding | Stage | Severity | Confidence | Fix, size |
|---|---|---|---|---|---|
| A | Rule K (and rule S's index test) compares inside evaluation, which has no level for fresh variables; a low level is unsound | 4 | high if missed | high | choose a source of fresh variables (a reserved range is my pick); part of stage 4's design |
| B | Two stuck casts or stuck proof matches: don't pass the proofs to rule I; compare ends, then motive, then base; skip a proposition's scrutinee in `same_trees_of` | 4 | medium | medium (sound in the model either way, I believe) | S, in stage 4; same in `reference.rs` and `unify.rs` |
| C | The tripwire fires on legitimate elaborator calls (`data_auto.rs:202`, `check.rs:5283`, `walk/two.rs:157`, `:303`, `cases.rs:3385`, head-keyed searches, `first_order`) | 5 | medium for the plan | high | arm it for the kernel and the reference evaluator only; "visibly data" excludes unmarked variables; S |
| D | `first_order`: marks alone let rule I pair proofs of different statements and then solve a data unknown ill-typed | 5 | low to medium | medium | rule I there only after `learn_types` agreed; else identical or fail; S. Rule S's stand-ins must tolerate an ill-typed proof |
| E | Searches and syntactic matchers: rule I at a candidate's root matches every proof | 5, SW-4661 | low | high | no rule I at the root; skip proofs only below a matched head; S to M |
| F | `equations.rs:2944`, `:4575` become always-true and can go | 5 | cleanup | high | S |
| G | Undo: metavariable marks derived or trailed; fired casts follow `meta_epoch`; rule K's test read-only | 3 to 5 | medium if missed | medium | requirements for the briefs |

Already true today and not changed by E2 (no action): `data_auto.rs:202` compares past a
difference (wording only); `unify_what_agrees` and `unify_waiting` go on past a clash or a
postponed pair; `same_field_records` pairs records whose parameters aren't known equal.

**Tickets to file**

1. *Into stage 3 (SW-4671), or a small follow-up once its marks exist (Opus, 30 min):* a
   counter under the same switch as the note's others: top-level calls of `value::conv` and
   `unify` **where both sides are marked proofs**, by caller (`#[track_caller]`), over std,
   `tools/fmt`, AoC and the roguelike (the verifier's or Overmind's run, not the lane's). I
   expect `check.rs:815`, `unify_index.rs:191`, the placeholder calls of section 6.1 and
   nothing else. Any other caller that shows up is one this audit only listed; read it then.
   This turns "I listed 300 elaborator sites" into a measurement.
2. *Stage 4's brief:* findings A and B as design conditions, and G's items 2 and 3. Tests: a
   comparison of two functions that differ only by a free variable, reached through a cast's
   ends (finding A's shape); two stuck casts along different hypotheses with equal ends, motive
   and base (equal) and with different ends (different).
3. *Stage 5's brief:* findings C, D, E, F and G's item 1. Tests: `?m h1 = f h2` with `h1`,
   `h2` proving different statements solves nothing; a `rewrite` whose needle is a proof with
   two unrelated proofs in the goal.
4. *Doc comments, with stage 5 (Sonnet, small):* `value::conv`, `reference::conv` and
   `unify::unify` state the precondition as "proofs are skipped by position"; reword for rule
   I, add the level precondition next to it, and list the callers of section 5's third group
   as the known exceptions.

**Calls I made:** to judge elaborator sites by "can it confuse" rather than "is it sound", since
the kernel re-checks; to list rather than trace the unifier's 230 callers; to run no probes.
No question here is Matt's.

## 9. What I did not check

- **No probe was run.** Every finding is about a rule that isn't built: on today's binary
  `h1` against `h2` is simply "different", so a probe can show nothing about rule I. Ticket 1
  is the substitute.
- The unifier's callers were classified from the call and a few lines around it; about 15 were
  read. `check.rs`'s 46, `effects.rs`'s 26, `numbers.rs`, `queue.rs` and `rows.rs` were not
  traced one by one.
- Inside the unifier: `solve`, renaming and pruning; `values_differ` and the unfolding rules;
  the bodies of `same_field_types`, `same_field_calls`, `unify_abstracting` and
  `unify_by_unknown_arguments`; `interfaces::unify_guessing_instance`.
- `reference.rs`'s comparison line by line (its structure matches `value.rs`); `native::compare`;
  the tree memo's `identical` and `shape_hash`.
- That finding B's shortcut (not comparing the proofs of two stuck eliminations) is sound in
  the model: argued in a paragraph, not proved.
- Whether rules K and S, landed under D1′ in stage 4 with the shortcut mode still in place,
  keep "equal arguments in shortcut mode give equal unfoldings": rule K would test its ends in
  one mode inside an unfolding compared in another. Not a same-type question; it belongs to
  stage 4's review.
- How kept unfoldings use `meta_epoch` (section 7, item 2), and the kernel's branch refinement
  against a cast that was stuck before an index was solved (already open in the E2 note).
- Line numbers are as of `71e566111`; SW-4671 (marks) is being built beside this and will move
  them.
