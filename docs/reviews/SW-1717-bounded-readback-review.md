# Review: bounded read-back (docs/proposals/bounded-readback.md)

**Ticket:** SW-1717, reviewing SW-1712's note (D2514). **Reviewer:** Opus, read-only (nothing
built or run), 6 Nov 2026. **Checked against:** `main` at `99de783dd` (the note was written at
`e0f9d7809`; between the two only `omega.rs` and a driver test changed under `crates/`) and
`lane/SW-1642` at `c91991954`. Line numbers are `main`'s unless marked (branch). Where I
couldn't settle a point without running something, I say so.

## Verdict: proceed with changes

The direction is right. One meaning for "unfolded" (D1280's capped normal form), a reader that
answers each site's question without building that form, and output terms read back folded:
together they deal with the real problem, which is that every unfolded read-back pays up to ten
million steps whether or not it succeeds. Nothing in the design lets a false statement check:
every motive and every elaborated term still goes through the kernel, and a kept call is
convertible to its unfolding.

But four claims the plan relies on don't hold as written:

1. **The reader's skipping rule is not exact.** I found three counterexamples (proof
   positions, the rule's own unknowns, and a needle whose variables are read off its folded
   form). All three are easy to fix, but stage 3 can't be called "speed only, can't change
   results" until they are fixed.
2. **The cap is defined in two incompatible ways**, and one of them keeps the outermost large
   call rather than the innermost.
3. **The cap never keeps a call that steps at once**, so the capped normal form is not bounded
   for recursion driven by a number literal (`settle x k 1000`). Removing stage 4's
   "unconfirmed" paths (D2521) would therefore take away the only thing that rescues those
   goals today.
4. **"Nothing reaches the cap" was measured on the wrong tree.** It matters once record eta
   is on `main`, not before. Stage 0 measures AoC, the roguelike and the examples only on
   `main`.

Stages 0 and 1 can start now. Stage 2 should wait until the cap's definition is fixed (H2).
Stage 3 should wait until the skipping rule is fixed (H1). D2521 and D2522 should be changed
(§Decisions).

## Findings, by severity

### High

**H1. The free-variable skipping rule misses occurrences that today's search finds.**
The note says a call whose arguments don't mention a variable of the needle "can't hide it",
so the reader's answers equal the ones it would get on the fully built form
(bounded-readback.md:333–341, :351–354). But today's search doesn't compare by syntax alone. It
compares each keyed candidate by **unification** (`Search::decide`, rewrite.rs:1404–1408, and
`unify_solving_arguments`), and unification ignores some positions and solves some unknowns.
Three counterexamples:

- *Proof positions.* The unifier treats a proof position as equal without looking inside
  (`proof_position`, unify.rs:1839–1861: "Otherwise the position is opaque: equal"). Take the
  needle `List.get xs i h`, where `h: i < xs.length`, and a goal holding `g xs i`, whose
  unfolding builds `List.get xs i h'` with its own proof `h'`. The arguments of `g xs i`
  don't mention `h`, so the reader skips the call. Today the search unfolds it, the key
  `List.get/3` matches, `h` against `h'` is a proof position, and the candidate is an
  occurrence. Indexing with a bounds proof is common in AoC, so this case is ordinary.
- *The rule's unknowns.* In `rewrite foo _`, the left side holds an unknown made for the rule
  (`rule_metas`, rewrite.rs:1270–1271), and the comparison solves it. No argument anywhere
  mentions that unknown, so a literal reading of rule 1 ("if the needle mentions … an unknown
  that no argument mentions", :335–336) skips every call.
- *Variables of the needle as written.* If the needle's variables are read from its folded
  form, `keep a b` (with `keep a b := a`) counts `b`. A call `f a` whose unfolding holds `a`
  doesn't mention `b`, so it is skipped and `a` is missed. The note itself makes this
  over-approximation point about mentions (:198–202), but rule 1 doesn't say which form the
  needle's variables come from.

A fourth, smaller case: with `by_instances` the left side is computed again mid-search, once
instances are solved (`interfaces::refresh`, rewrite.rs:1395–1402). Its variables can change
part-way through the walk.

*Fix.* Prune only by the needle's *relevant* variables. Those are the variables of its capped
normal form, outside proof positions, not counting unknowns the comparison may solve, and
computed again after `refresh`. `generalised_now`'s "unifies solving nothing" (stage 2 of
goal-as-written.md) and the transport have the same proof-position exposure. Stage 3's
both-ways debug switch would catch these only if std happens to contain such a case, so add a
unit test for each of the three above.

**H2. The cap has two definitions in the note, and they keep different calls.** §4.1 says a
call is kept if "its own unfolding would read back to more than `CAP` nodes", computed "with
`quote_at_most`'s cap … on the call's unfolding alone" (bounded-readback.md:299–308).
`quote_at_most` reads back **fully unfolded**, with a size cap (value.rs:1917–1919, mode
`Readback::Unfolded`). By that definition, any call that has a large call anywhere inside it is
itself over the cap. So the *outermost* call is kept, and with it everything small inside,
including what the proof needs. D1280's scratch version was recursive instead: it read a
call's unfolding by the same capped rule, so inner large calls were kept and the outer one
stayed visible (goal-readback.md:260, :340, "sizes counted while reading back", "recursed per
call"). Only the recursive definition is the one D1280 measured. It is also the only one that
fits the note's own example (`album =>` bodies opened, the helpers inside kept).

Two more things belong in the definition, because both decide what goes into elaborated terms:

- *Fixed limits.* The cap test must run under its own fixed limits (an attempt like `cheaply`,
  unify.rs:2566–2574), never the enclosing operation's. `quote_as` drops a cap that isn't
  below the current size limit (`cap.filter(|&cap| cap < limit)`, value.rs:1993), and the
  elaborator runs read-backs inside attempts whose size limit is 10,000 (`cheaply`,
  `omega.rs:2365`, `:2386`, `ring.rs:944`). Inside one of those, the same call would be "an
  error", not "kept". A needle read inside an attempt and a goal read outside it would then
  differ, which breaks D1280's consistency property. Attempts' limits are build-independent
  for exactly this reason (budget.rs:303–310, SW-962).
- *The meta epoch.* A call's size changes when an unknown in its arguments is solved, so the
  cached answer must be dropped when solutions are undone. `Unfolding` already does this for
  unfoldings (value.rs:56–71).

**H3. Calls that step at once are never kept, so the capped form is unbounded where stage 4
rescues goals today.** Rule: "A call that steps at once by matching (`matches_at_once`) is
never kept" (bounded-readback.md:300–301; D1280 had to exclude these, goal-readback.md:265).
A recursion driven by a literal steps at once at every level: in `settle x k 40` and
`settle … 1000`, the case on the rounds argument meets a number every time (value.rs:584–604).
So the capped normal form of such a goal is exactly today's normal form, and today that is
`E-RESOURCE`. The accept example for stage 4 works only because it writes the limit as a
definition (`def limit: Nat := 1000`, examples/accept/as-written-unconfirmed.sw:21–24); that
argument is a call, so `settle x k limit` doesn't step at once and could be kept.
examples/reject/as-written-unconfirmed-slow-check.sw:19–21 uses the literal `40` inside
`inner`.

Stage 4 is also reached when the **search budget** runs out (`E-REWRITE-BUDGET`), not only the
size limit (rewrite/as_written.rs:27–35). The cap does nothing about that budget.

So D2521's claim that after stage 6 "there is nothing left unconfirmed to warn about"
(bounded-readback.md:379–384) is false for literal-driven goals and for exhausted search
budgets. Removing those paths would turn some of today's warnings back into `E-RESOURCE`. Keep
them for those two causes. (Also, `quote_folded` looks through calls that step at once too, so
"as written" is not bounded either. Stage 0 should measure folded read-back sizes as well.)

**H4. The cap's safety was measured before record eta, and on a narrower set of sites.**
§5's property 3, "On `main` nothing reaches the cap" (bounded-readback.md:408–411), is what
"stages 2 to 7 change nothing on `main`" rests on (:479–480). Three problems:

- *Record eta is the reason for the change.* Rule 2 makes unfoldings much larger under binders,
  everywhere, and AoC writes its domain types as records (D2363). The claim that matters is
  "nothing reaches the cap *with record eta*". Stage 0 runs AoC, the roguelike and the
  examples only on `main` (:486–488).
- *D1280 measured only its own sites.* Its measurement covered the read-backs in its §1 table
  (goal-readback.md:198–199: "used at every elaborator site in the table of §1"). That table
  doesn't include the unifier's mentions, `ignorable_arguments`, `cases`, messages, `decide`,
  goal-as-written's completeness and agreement checks (which came later), or the ~200
  unclassified sites. The note extends the cap to all of these (:303).
- *It wasn't a plain measurement.* It ran with its own scratch semantics, and it used
  `STW_KGLUE` for the repro and rogue2q (goal-readback.md:198–205).

So D1280's 26 Oct measurement doesn't carry over. Stage 0 is the right place to measure again,
but it must measure on `lane/SW-1642` as well (§Stages).

### Medium

**M1. The reader has no way to build the motive.** `find` returns the occurrences
(bounded-readback.md:319–321). But `rewrite` and `match` also have to *abstract* them, and
today they do that by rewriting the read-back term (`Search::visit` under `replace_with`,
rewrite.rs:1316–1350). With the reader, the term that gets abstracted is the goal with only the
opened calls unfolded. That term is not today's normal form. So on `main`, stage 6 changes
the `J` motives (and so hashes and next goals) wherever today's fallback search runs. That
contradicts "3 the lazy reader … can't change results" (:79–81) and "stages 2 to 7 change
nothing on `main`" (:479–480). It is sound: `check_motive` and the kernel check the motive.
But the note should either say that motives come out partly folded, and accept it (it is the
kind of change goal-as-written already accepted), or build the motive from the capped normal
form on the success path. That costs time, but only once per `rewrite`.

**M2. Other stages also change behaviour on `main`.** None of these is wrong, but each should
be named and measured, not assumed away:

- *Stage 4, zonk.* `unfold_where` writes a different solution term from today's. Today's
  fallback unfolds the **whole** solution (unify.rs:2777–2780), so elaborated terms and their
  hashes move wherever that fallback fires. It also interacts with `refold`
  (unify.rs:2591–2608), which looks for a `let`'s value in its folded or unfolded form, and a
  mixed term holds neither.
- *Stage 5, messages.* `NOTE_CAP` is 10,000 nodes in all, so notes disappear for sides between
  10,000 and 10,000,000 nodes (:518–521, which accepts this).
- *Stage 6, `cases`.* It moves the "seen" and "known" sets from equal normal forms
  (`matching::same`, cases.rs:1246–1249) to `conv_now` (:372). Conversion ignores proofs and
  uses eta, so `cases` can now treat as the same two values it used to keep apart.
- *Stage 7, `decide`.* The 100,000-node threshold applies to the proposition as a whole, not to
  one call (:532–534, :566–571). A proposition between 100,000 and 10,000,000 nodes with no
  single large call would switch to `decide_as_written`, which can pick a different decision.

D2524's both-ways switch checks the reader's answers; it doesn't catch changed terms. The
`hash_stability` snapshots do, so each stage should say which snapshots it expects to move.

**M3. `decide` doesn't need a cap.** `decide` reads the proposition back unfolded only to
compute it again with gluing off (auto.rs:783–795). Its comment gives the reason: with gluing
on, a decision procedure "would be matched against a call by its arguments". So the fix is to
switch gluing off, not to use the unfolded term. Reading back folded (`quote_folded`) and then
evaluating with gluing off gives a value with no calls, whose forced forms are those of today's
term, so the search sees the same thing. This should make exactly today's decisions, with no
size threshold and no fallback to `decide_as_written` for size. It also avoids the read-back
blow-up in trip-journal. `from_yes`'s goal can be folded as stage 1 proposes. **[inferred]**
One thing to check: two lists that are equal but stored differently (`Chars` against a chain
of `Cons`) must unify the same way, so stage 7 should run its both-ways comparison.

**M4. The cache is keyed the way D1280 found didn't work.** §4.1 says the answer is "cached per
declaration by the call's cell, as D1280 proposed" (bounded-readback.md:307–309). D1280
*measured* remembering "too big" per cell, and found it saved little: "the kept calls are
mostly fresh cells" (goal-readback.md:261). What it proposed instead was "a cache keyed by the
call (its definition and its arguments read back folded)" (:296–298). It is worse on the
branch: `project_call` makes a new `Unfolding` cell for every field
(`crates/core/src/value.rs` (branch):1820–1830), so a cell-keyed cache misses every
`(f x).i`. Use D1280's key, together with the meta epoch (H2).

**M5. Above the cap, a program's meaning can change and the kernel will still accept it.**
Proofs are safe: any proof of the stated goal is a proof. Programs are different. A capped
read-back can change *which* well-typed term the elaborator picks:

- *Instance search.* `find_ready_dictionaries` read the goal unfolded when D1280 looked
  (goal-readback.md:79), and `interfaces.rs`'s 11 sites aren't classified yet. Seeing
  `Key x` kept instead of its unfolding `Nat` could pick a different instance.
- *Defaults.* `lib.rs:4954` decides whether a default fires.
- *Decisions.* `decide` (M3).

The kernel accepts any well-typed dictionary. If instances aren't coherent, a program would
then compute something else, with no error. This happens only above the cap. Still, stage 0
should classify `interfaces.rs` before stage 2 switches `Ctx::quote`, and the note should say
whether instance search may see kept calls.

**M6. Stage 2 alone may not unblock SW-1667 in reasonable time.** Without the reader, each
kept call costs up to `CAP` nodes every time a read-back meets it. On rogue2q that was 9,917
kept calls and 6× the time (goal-readback.md:292–294), measured with a cache that didn't help
(M4) and with `STW_KGLUE`. Trip-journal under eta could easily be worse, because every
`album =>` body is a candidate. D2528's "twice the time on `main`" test is the right guard.
But plan for "SW-1667 waits for stage 6" as the likely outcome, not the exception.

### Low

**L1. The risk from equation lemmas is smaller than flagged.** See Q4.

**L2. The head rule (rule 2) needs more care than "reachable from `f`'s body".** An
occurrence's head can also come from a native's result, from a dictionary stored in a body,
from a definition named only in a type argument, or from a definition that is opaque in this
module but not elsewhere (`body_seen`). It is marked optional (:342–347). Leave it out of
stage 3 entirely until stage 0 shows that the free-variable rule alone isn't enough.

**L3. Which calls are kept depends on how values are stored.** The size of a call's unfolding
depends on how its arguments are represented: a number as `Nat(n)` or as a chain of `Succ`, a
list of characters as `Chars` or as a chain of `Cons`. So two convertible copies of a call
with sizes near the cap can be kept differently. This is an edge case, but stage 2's unit test
"the result is the same wherever the call sits" should include it.

**L4. The branch adds projected calls.** On `lane/SW-1642`, a call's spine can end in
projections (`Frame::CallField`, `is_call_field`; branch value.rs:614–622). `quote_capped` and
the reader are written against `main`, so SW-1667's rebase must extend both. Say so in stage 2
and in D2528's plan.

**L5. The citations are accurate.** I spot-checked 45 file:line citations against `main`, and
all point at the code the note describes. The count of unfolded read-backs is right: 286 lines
by my grep against "about 290". It leaves out the two `quote_unfolded_shown` sites
(check.rs:754, :894), which are also unfolded.

## Answers to the brief's questions

### 1. Soundness

There is no path to a false statement that checks. Every motive is type-checked
(`check_motive`, rewrite.rs:1585, matching.rs:1587) and every term goes through the kernel. A
kept call is the call itself, convertible to its unfolding. The reader solves nothing outside
the sites' own snapshots (bounded-readback.md:363–366, and as_written.rs:390 and :448 confirm
it). Output terms read back folded are convertible to today's. For accessors, the kernel checks
the accessor's body against its declared type, so the folded type means the same thing.

Where meaning *can* change, the kernel will accept the result anyway:

- the choice of instance, default or decision in a **program**, above the cap (M5);
- which copies a `match` or `rewrite` abstracts (M1, H1). For proofs this affects only the next
  goal; for a `match` in a program it affects only the motive, not what runs.

None of these touches the kernel. The note's soundness paragraph (:394–398) should mention the
program case.

### 2. The equivalence claim

It is not true as stated (H1). The brief asked about four kinds of case:

- **Closures and let-bound values.** These are fine. A closure's free variables are its
  environment's, and a `let` in the context sits in `cx.env` as its value, not as a variable,
  so the needle and the goal see the same thing. The only cost is walking environments, which
  can be large.
- **Metavariables.** Unsolved unknowns are applied to every plain variable in scope
  (`fresh_meta`, check.rs:955–967), and lifted helpers' frozen unknowns are too (lift.rs:6–8).
  So an argument holding an unknown mentions everything, and the reader opens the call. That
  is conservative, and it means pruning does nothing while a goal has open unknowns. The real
  problem is the *needle's* unknowns (H1). A subtler point: a needle unknown solved
  mid-walk enlarges the needle's variables. Computing them once is still safe, because it
  only prunes less.
- **Definitions that reach the target through their own constants.** These are fine for the
  free-variable rule. A closed needle has no variables, so nothing is skipped: today's cost,
  but correct. They are a problem for the head rule (L2).
- **Occurrences produced by computing** (`a + 0` becoming `a`, `two` becoming `2`). These are
  fine. Both forms start from the same value, and arithmetic on literals is done when the
  value is built. `Nat.add a 0` steps at once, so the as-written walk forces it too. Needles
  keyed by a number or constructor get no pruning (no variables), and the head rule doesn't
  apply to them as written. The examples I tried break only a head rule extended to such keys
  (`def two := 1 + 1`; the needle `2` isn't in `two`'s body).

The counterexamples are proof positions, the rule's unknowns, and needle variables read from
the folded form (H1).

### 3. The cap

- **From one run to the next.** The result is deterministic only if the cap test runs under
  fixed limits of its own and its cache is keyed by the epoch (H2). As specified,
  `quote_at_most` takes its limits from the enclosing operation, so the same call can be kept
  in one place and not in another. That would also undermine
  `a_namespace_checked_alone_has_the_same_hashes`, the test SW-1667 has to pass.
- **Hashes and the check cache.** Kept calls end up in motives and output terms, so hashes
  depend on `CAP`. If `CAP` is a field of `Limits` that a user or a test can change, it must
  be part of whatever the check cache's key covers, or fixed. I didn't find where the driver
  keys its cache, so this needs checking.
- **Error text.** Today's `E-RESOURCE` "too large to show" names the definition
  (module.rs:677). The proposed "left as it is" note replaces it only on failure. Notes
  disappear between 10,000 and 10,000,000 nodes (M2).
- **`decide`.** The 100,000-node threshold is a second, total cap (M2), and M3 removes the need
  for it.
- **Is D1280 still valid?** No (H4). Record eta changes the sizes; D1280 covered only its own
  sites; goal-as-written added unfolded read-backs of motives (`hidden_copy_in`,
  as_written.rs:415–416). Stage 0 must measure on the branch.

### 4. D484 and the generated equation lemmas

The risk is real but narrow. A lemma's left side is the definition applied to the arm's
*patterns* (equations.rs:2783–2790). Patterns are constructors and variables, so they read back
the same folded or unfolded, and the key `rewrite f.eq` searches with is `f` either way. The
sites that could change something are:

- binder types (equations.rs:2833);
- the Boolean right side in `bool_equation` (:2532, which already reads the left side folded);
- `uniqueness`'s sides (:4445–4446);
- `mentions_computation`, which decides *whether* an equation is generated (:5064–5072). A kept
  call would read as "mentions computation" and change which equations exist.

What stage 1 should do: leave equations.rs alone. §2.5's table doesn't include it, and that is
right. Stage 0 classifies its 10 sites: they are "mentions"-like, or patterns, not output
terms. If a later stage folds the binder types, its lane should check that `rewrite f.eq_k`
proofs in std and AoC are unchanged.

### 5. Stages

**Order.** Stages 0 → 1 → 2 → 3 → 4–7 is right in outline. Two changes:

- Put the `decide` change (M3) with stage 1. It is small, keeps today's decisions, and removes
  one blow-up site.
- Fix H1 and H2 in the note before stages 2 and 3 start.

**A smaller first step for SW-1667.** "Stage 0a" (Sonnet, about 30 min): trip-journal only, on
`lane/SW-1642`, with a backtrace or counter on each read-back over a million nodes (as
goal-readback.md did). It answers:

- which sites fail;
- which definitions are involved;
- whether trip-journal also runs out of *work*, not just size;
- whether accessor types are among the failures;
- how large the folded read-backs are.

Then stage 1, only if 0a shows output terms among the failures. Then stage 2 developed
against the branch, because nothing on `main` reaches the cap except D1280's repro, so `main`
can't test it. The full classification of the ~200 remaining sites (0b) can run alongside.

**Is stage 0 measuring the right things?** Mostly. It should also measure:

- AoC, the roguelike and the examples on `lane/SW-1642` (H4);
- the largest unfolding of a call that steps at once, since those can never be kept (H3);
- how often the same kept call is met again, with D1280's key against the cell (M4);
- the sizes of `decide`'s propositions and of message sides over 10,000 on `main` (M2);
- whether the kernel's read-backs (core/src/check.rs:378, and `substitute`) are reached in
  trip-journal.

**Estimates.** Stage 3 (150 min) is optimistic. It has to match today's pre-order exactly,
interleave with unification, and answer the motive question (M1). 200 min is more realistic.
Stage 6 (150 min) should be split into 6a and 6b from the start. goal-as-written took one
lane of about 120 min per consumer.

### 6. The questions

- **D2519** (the capped normal form everywhere). **Agree, with conditions:**
  - the recursive definition (H2);
  - fixed limits and an epoch-keyed cache keyed by definition and folded arguments (H2, M4);
  - the kernel excluded;
  - applied only to classified sites, with `interfaces.rs` classified first (M5);
  - stage 0 run on the branch (H4).
- **D2520** (one shared reader). **Agree with the direction.** But the exactness claim needs
  H1's fixes, and the motive question (M1) needs an answer. Call stage 3 "checked to match by
  the both-ways switch", not "can't change results", and leave the head rule out of it.
- **D2521** (remove the unconfirmed warnings). **Disagree as framed.** Keep stage 4's paths for
  calls that step at once and for an exhausted search budget (H3). Drop the warning only
  where the cap kept a call. The "left as it is" note on failure is good. Consider also
  attaching it to a *later* `E-REFL` or `E-REWRITE-NOTHING` in the same proof, when an earlier
  search kept a call whose arguments mention its needle's variables. That is where the user
  sees the effect.
- **D2522** (`decide` keeps D484 below 100,000). **Replace it** with M3: read back folded,
  evaluate with gluing off, search as today. That makes the same decisions with no size
  threshold. Keep `decide_as_written` for what it does today (a decision that is stuck), not
  as a size fallback.
- **D2523** (all output terms folded). **Agree.** I checked the sites for anything that would
  compare these terms by syntax later: `check.rs:4980` and `rewrite.rs:1605` evaluate them
  again with gluing off, and `matching.rs:521`, `:657` and `:851` are motive types the kernel
  checks. Not equations.rs (Q4).
- **D2524** (a test exception for stages 0, 3 and 6). **Agree.** Add stage 2: it is the stage
  that switches `Ctx::quote`, and its "nothing changes" claim is exactly the measured one. Add
  the branch runs from H4.
- **D2528** (order and resuming SW-1667). **Agree,** with stage 0a as the first step and
  M3 added to stage 1. Be ready for SW-1667 to wait for stage 6 (M6).
- **D2529** (`CAP` fixed, no syntax). **Agree.** Add "fixed in the language, not a user-settable
  limit" (Q3, check cache), and keep it in `Limits` only for tests.

**Missing questions:**

1. **The definition of the cap.** Kept by the size of the call's capped unfolding (recursive)
   or of its full unfolding? This decides what users see, so it belongs in D2519's wording,
   not in an implementation note (H2).
2. **Motives built by the reader.** May they come out partly folded, so that `J` terms and
   hashes move at stage 6? Or must they match today's (M1)?
3. **Programs.** May instance search and defaults see kept calls (M5)?
4. **Stage 4's paths.** Do they stay for calls that step at once and for an exhausted search
   budget (H3)? This is part of D2521, but as a separate question.

(D2525–D2527 are absent from the note's numbering. That's fine if the numbers went to other
tickets. I didn't check.)
