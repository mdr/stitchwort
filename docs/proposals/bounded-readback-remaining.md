# Bounded read-back: the remaining work, as one staged plan

**SW-1828**, 7 Nov 2026, from D2585. Design only: nothing was built or run. A companion to
[bounded-readback.md](bounded-readback.md) (revision 3), whose direction it keeps: D2541
("compute to decide, search what you see"), D2542 (searches rewrite what is visible), D2543
("limits fail and never choose"). This note says where the work stands after the stages
merged since revision 3, says what each limit that chooses should become, settles the
`omega`/`ring` gap, and orders what is left into lanes with briefs. Its questions are D2610 to
D2614 (§6).

Written against `main` at `c302f9714`, after record eta (SW-1642, SW-1667), SW-1779, SW-1782
and SW-1800 merged. Line numbers are `main`'s at that commit (grep). Labels as in the main
note: **[checked]** (read here), **[cited]** (from the ticket or review named), **[inferred]**
(my reasoning).

## Contents

1. [Where things stand](#1-where-things-stand)
2. [What changed since revision 3](#2-what-changed-since-revision-3)
3. [The limits that choose](#3-the-limits-that-choose)
4. [Omega and ring atoms](#4-omega-and-ring-atoms)
5. [The stages](#5-the-stages)
6. [Questions for Matt](#6-questions-for-matt)
7. [Tickets this plan settles or absorbs](#7-tickets-this-plan-settles-or-absorbs)
8. [What this note did not do](#8-what-this-note-did-not-do)

## 1. Where things stand

### 1.1 Stages done

| Stage | Ticket | What it delivered |
|---|---|---|
| 0a | SW-1740 | Trip-journal's failures on the record-eta branch: one in `accessors` (`pinFits` unfolding `Float` arithmetic on unknown bits), then 33 in `Trip.Proofs` (`rewrite_once` 21, `ignorable_arguments` 13, zonk 9, `generalised_now` 8, notes 10, `decide` 1). D2544's experiment was not adopted. **[cited]** |
| — | SW-1744 | The cause: rule 2 opened `Float.add`'s record patterns on unknowns. Fixed on the branch by D2551 (a definition with a native keeps its record patterns stuck). Trip-journal then checked in about 4.0 s against 3.1 s on `main`. So SW-1667 no longer waited on stages 1 to 6b (D2552). **[cited]** |
| 1 | SW-1746 | Accessor types, record updates, `fromYes` and the §2.5 terms read back folded. `decide` reads back folded and evaluates unglued; `STITCHWORT_DECIDE_BOTH` checks it. Float pins and 70 snapshots moved. **[cited]** |
| 0b | SW-1747 | All 288 sites classified ([SW-1747-stage-0b-sites.md](../reviews/SW-1747-stage-0b-sites.md)). Found the `omega`/`ring` gap, the size of stage 1, and `scanned`'s cap. **[cited]** |
| 1b | SW-1748 | 69 more output sites folded (`effects.rs` 31, `derive_induct.rs` 28, `interfaces.rs` 10), plus the `omega`/`ring` emit round trips. Instance terms now name their definitions (`Char.decEq x y`). 37 std hashes moved. The sites it left unfolded on purpose are in the main note's stage 1 text (SW-1785). **[cited]** |
| — | SW-1779 | `ignorable_arguments` reads types back folded (D2567). Most of AoC's 18% fewer steps came from this. Also: `declare_def` checks signatures glued, and `interfaces::locals` looks at the head glued first. **[cited]** |
| — | SW-1782 | A cached unfolding records the modes it was computed in, so a folded read-back with gluing on is never handed an unglued unfolding. 317 order-dependent hashes became 0 under the instrumentation. **[cited]** |

So about 200 unfolded read-back sites remain in `crates/elab/src`, down from 290. That is
the grep of `quote(`, `cx.quote(` and `quote_at_most(` without the folded and shown forms,
less about 30 that aren't sites (omega's own `Quoter::quote`, tests, `goals.rs`'s closure).
**[checked]**

### 1.2 What is left, by site

"Consequence" is what a user meets today when the site's term is large. With record eta on
`main`, that is likelier than when revision 3 was written: rule 2 opens record patterns under
binders. The kinds are: an **E-RESOURCE** ("a value was too large to show", or out of work);
a **wrong goal shown** (a goal or motive printed computed, not as written); a **silent
choice** (the answer depends on a limit); and **slowness** (up to ten million nodes built and
thrown away).

| Sites (`main`) | Kind | Consequence | Stage (§5) |
|---|---|---|---|
| About 30 output sites stages 1 and 1b didn't reach: `auto.rs` 520, 652, 754; `defaults.rs` 534, 598, 1005, 1239; `partial.rs` 647, 656, 785; `calc.rs:107`; `pipe.rs:125`; `numbers.rs:1449`; `derive.rs` 700, 805, 810; `goals.rs` 1180, 1184; `cases.rs` 953, 978, 992, 1072 (`take_apart`); `check.rs:2395`; `bind.rs:437`; `counterexample/inputs.rs:354`; `equations/induct.rs` 975, 1454, 1812 (head shape only) | output | E-RESOURCE or slowness where the term is large; elaborated terms larger than needed (hashes) | **1c** |
| `interfaces.rs:1399` `scanned` (8 callers) | mentions, with a cap | **silent choice** above 100,000 nodes: reads folded, so it can report an unknown that the unfolding drops, or miss a stuck projection (§3.1); slowness up to 100,000 nodes per call, every round | **4a** |
| `unify.rs:979` `mentions_unknown` (`KNOWN_CAP`) | mentions, with a cap | **silent choice**: over 4,096 nodes counts as "may mention", so `plus_rule` doesn't solve `?m + a = t` and the pair waits or fails (§3.2) | **4a** |
| `unify.rs:178` `on_pending` | mentions, with a cap | none: past the cap it falls back to an exact occurs check (§3.3) | 4a (simplify only) |
| `check.rs:3885` `ignorable_arguments` | mentions | none on size since SW-1779; a failed folded read-back still answers "nothing ignorable" (`.ok()?`) | **4b** |
| `bind.rs` 95, 99; `matching.rs` 434, 1778; `lib.rs:4960`; `rewrite.rs` 707, 1501, 1691; `cases.rs` 875, 1585; `queue.rs` 506, 1100; `named.rs:895`; `derive.rs` 330, 486, 594; `derive_show.rs:241`; `derive_induct.rs:632` with `move_to` (1259); `effects.rs` 619, 3699, 4010, 5118; `equations.rs` 5064, 5072 (a constant, not a variable) | mentions | E-RESOURCE or slowness; `rewrite.rs:707` and `lib.rs:4960` also make a **silent choice**: a failed read-back counts as "no unknown" or "no dependency" | **4b** |
| `unify.rs:2894` (`zonk_changed`'s whole-solution fallback), `unify.rs:2712` (`both_forms`), `effects.rs:3986` (`unsettled`), `families.rs:702`, `rows.rs:250`; `check.rs:4980` `proof_expected` with an unknown inside a call (SW-1758) | zonk | slowness and larger terms: one call that holds an unsolved unknown sends the whole solution through the unfolded read-back | **4c** |
| 28 message sites (main note §2.4, SW-1747's `shown` rows), `check.rs:1066` (`unknown_notes`, through `scanned`), `omega.rs` 2544, 2555 (near-miss hints) | shown | slowness on error paths, and inside undone attempts. Four sites (`effects.rs` 4135, 4142; `induct_match.rs:429`; `rewrite.rs:1919–1920`) let an **E-RESOURCE replace the intended error** | **5** |
| `omega.rs` (21 sites), `ring.rs:932` | same | E-RESOURCE when an atom is large; **silent choice**: the conversion fallback runs under a fixed 20,000-step limit and running out counts as "different atoms" (§4) | **O** |
| `rewrite.rs` 739–805, 1095, 1191, 1225, 1435; `rewrite/as_written.rs` (5); `rewrite/under.rs` (6); `rewrite.rs:588` (`discharge`) | find | **wrong goal shown** (next goals read back unfolded: `List.range` shows as `rangeFrom`, SW-1387); the reach into hidden copies (days 10 and 14); `W-REWRITE-UNCONFIRMED`; E-RESOURCE; slowness | **3, 6a** |
| `matching.rs` 512, 521, 657, 779, 851, 933, 936, 1428, 1687; `matching/as_written.rs:658`; `check.rs` 1322, 1323, 1336, 1531; `cases.rs` 1157, 1246, 1284, 1301, 1330, 1569; `induct_match.rs` 172, 320, 322 | find, same | **wrong goal shown** (motives unfolded: `resolveOutOfWalls`' proof term 4.6k → 106k nodes, SW-1762); `W-MATCH-UNCONFIRMED`; E-RESOURCE; `check.rs:1531` and `cases.rs:1157` make a **silent choice** (a failure counts as "not equal" or "skip the equation") | **3, 6b** |
| The five recovered sites (`rewrite.rs:739`, `matching.rs` 779, 933, 936, `matching/as_written.rs:658`) and `undo.rs`'s recoverable "too large to show" | recovered E-RESOURCE | **silent choice**: the result depends on where a shared budget ran out | **6a, 6b** remove them; **7** closes the door |
| `equations.rs` 2532, 2787, 2827, 2833, 4445, 4446 | output, kept unfolded | none (deliberate, main note §11) | none |
| `derive_induct.rs:432` (`field_type`) | output | none today; folding it waits until `classify` reads a separate copy | later, not planned |

**Correction to the main note's §2.5 (SW-1757).** `matching.rs` 521, 657 and 851 are not
output terms the kernel checks: they are scrutinee types that `match`'s occurrence search
then searches. And `named.rs:895` (`dependencies`) is a mentions test, not a binder type.
Stage 1 was right to leave them, and they move in 6b and 4b. The main note's table now says
so. **[cited: SW-1756 §5; checked at the lines above]**

## 2. What changed since revision 3

**Record eta is on `main`** (SW-1642, SW-1667, merged 7 Nov).

- *Glued projections.* A field of a glued call stays a call: `project_call`
  (`core/src/value.rs:1924`) pushes `Elim::Proj(d, i)` onto the call's spine and shares the
  base call's unfolding (`Unfolding { kept, base }`). Read back folded, it is `(f x).i`. For
  the reader (stage 4a) this means:
  - a call's *arguments* are its `Elim::App`s only;
  - a projection adds no variable, so the free-variable rule is unchanged;
  - opening a field call opens the base call (`Frame::CallField`) and projects, so the memo
    must key on the base call's cell, or two fields of one call are explored twice.

  **[checked]**
- *Rule 2 under binders.* With record eta on, the unfolded read-back of any goal that passes
  a record to a helper under a binder runs through the helper. D2551 holds only definitions
  with a native (`eta_held`, `value.rs:1958`; today only `Float.add`). Every unfolded site
  left in §1.2 is therefore more exposed on `main` than it was on 6 Nov. The first measured
  cost is SW-1762 (`Rogue.Proofs` +28%, nearly all `resolveOutOfWalls`, through `match`'s
  motive). SW-1829 is still open (whole AoC doesn't finish in 6 minutes after the merge,
  against about 69 s before). If its cause is one of §1.2's sites, that site's stage moves
  to the front. **[cited]**
- *SW-1725, records whose fields are all proofs.* Such records have no eta.
  `qualifies_for_eta` (`core/src/check.rs:2255`) needs a field whose sort isn't `Prop`, and
  the unifier uses the same flag (`is_eta_type`). So the main note's skipping rule (§4.2,
  rule 1) loses its last clause: a variable of such a record type stays relevant, as any
  other variable does. That is the conservative direction: the reader opens more calls,
  and never misses one. SW-1725 can close with this answer. **[checked]**

**SW-1779 and SW-1782.**

- `ignorable_arguments` now reads back folded, with no cap (§3.4).
- An unfolding cached with gluing off no longer serves a folded read-back with gluing on. So
  whether a value was forced unglued first (by `decide`, or by an instrumentation's
  conversion) no longer changes what an elaborated term says. Stage 6b was the most exposed
  to that (SW-1784 §4). It is now safe to compare hashes before and after a lane's change
  without worrying about evaluation order. One way it still shows is step counts, which
  stay history-dependent (SW-1791 §2). The reader's work limit (§3) counts steps, so it can
  run out at slightly different points depending on what was forced first. The limit must
  be set with room above the largest measured question, not at its edge. **[cited]**

**SW-1800, the dot caches.** The dot-call caches were keyed by syntax addresses, which
could be freed and reused within a declaration, so a cached failure could be returned for
other syntax. They are now emptied before each declaration. The reader's memo (main note
§4.2, rule 3: "per value cell and per question ... within one meta epoch") has the same
hazard if it keys by a cell's address. So it must either hold the `Rc` of each cell it keys
on, which keeps the address from being reused, or live for one question only.
Recommendation: one memo per top-level question, holding the `Rc`s, dropped when the
question ends. That is also all it needs: the sharing it exploits is within one value.
**[inferred from SW-1800's finding]**

## 3. The limits that choose

D2543: a limit fails with a message naming the call, and never switches to another answer.
SW-1750 named four sites, and SW-1739 one of them. Reading them on `main`, two choose and two
don't. Reading around them, I found three more that choose, and some limits that choose
only how a term is written, or which candidate a search tries next (§3.6).

### 3.1 `scanned` (`interfaces.rs:1399`): chooses

`scanned(v)` reads back `v`'s normal form up to `SCAN_LIMIT` (100,000 nodes) and, past
that, reads it back folded. It came in with 2024 day 6 (`87a9a3f6c`): applying
`Set.containsFilter` to the program's huge filter ran out while looking for `auto`
dictionaries. The repros are `examples/accept/lemma-on-large-normal-form.sw` and its reject
twin. **[checked]** Its callers ask four different questions:

| Caller | Question | Folded past the limit gives |
|---|---|---|
| `unsolved_in` (1417), `search_pending_in` (`queue.rs:858`), the `outside` set (`queue.rs:1651`), `find_ready_dictionaries`' unknowns (1728) | which unsolved unknowns `v`'s unfolding mentions | a superset: an unknown that a call's unfolding drops is reported, so an obligation waits, or is reported unsolved, where the small case goes on |
| `stuck_on_found` (1695), `find_ready_dictionaries`' `stale` | does the unfolding contain an interface projection applied to a found dictionary | a subset: a stuck projection inside a call is missed, so `refresh` isn't run and a later comparison sees the stale form |
| `refresh` (1410) | `v` with solutions substituted, computed again | the same value, written differently: no difference in meaning |
| `unknown_notes` (`check.rs:1066`) | which `?N` to explain in a message | display only |

**What it should do.** All three questions that decide something are answered exactly by
one read-back: **`unfold_where(v, a call whose arguments mention an unknown, solved or
not)`**. That is the main note's §4.2 primitive with zonk's predicate, widened to solved
unknowns. It is exact by the substitution lemma the reader rests on: definitions are closed,
so a call whose arguments mention no unknown has an unfolding with no unknown, and so no
projection stuck on one. **[inferred]** Then:

- the unknown questions collect `Term::Meta`s from it, as today;
- `stuck_on_found` runs `stuck_term` on it, as today;
- `refresh` evaluates it;
- `unknown_notes` reads folded, since only the printed `?N`s matter.

The cap goes. A question that runs over the reader's fixed work limit is `E-RESOURCE`
naming the largest call opened ("looking for unknowns inside `Set.contains (s.filter
(keep x)) key` took more than … steps").

**What it may break, and why I expect it doesn't.** It breaks a program only where a call
whose arguments hold an unknown has an unfolding too large for the reader. In
`lemma-on-large-normal-form.sw` the huge part is `keep x key`, whose arguments are variables
and hold no unknown, so it is never opened. The unknown is `Set.contains`'s `Ord`
dictionary, and its unfolding on an unknown set `s` is stuck at once. 2024 day 6's
`Part2.sw` has the same shape (the program's filter, applied through
`Set.containsFilter`). Both are named as tests in 4a. Stage 0c counts how often the cap
fires on std, AoC and the roguelike today, which finds any other program that relies on
it. **[inferred; 0c measures]**

### 3.2 `mentions_unknown` (`unify.rs:979`, `KNOWN_CAP`): chooses

`stuck_sum` (`unify.rs:864`, SW-896) solves `?m + a = t` by reading `+`'s rules backwards,
only "when `a` mentions no unknown". `mentions_unknown` reads `a` back unfolded up to 4,096
nodes, and past that answers "may mention" (`true`). So with a large known side, the plus
rule doesn't fire, and the pair waits or fails where a small one is solved. It is never
unsound, but it is a limit that chooses. **[checked]**

**What it should do.** Answer exactly, cheaply. If `a`'s folded read-back has no unknown,
the answer is "no", exactly: the unfolding's unknowns are among the folded form's. Only if it
has one does the question need the unfolding, and then only of the calls whose arguments
hold one: `unfold_where(a, args mention an unknown)`. No cap. Running out is `E-RESOURCE`.
**[inferred]** At risk: none known. A program that relies on the cap is one where the plus
rule *must not* fire on a large known side to type-check, which is not a shape I can find by
reading. 0c counts how often the cap fires.

### 3.3 `on_pending` (`unify.rs:178`, the same `KNOWN_CAP`) and `normals` (`matching.rs:1428`): don't choose

- **`on_pending`.** Past 4,096 nodes it doesn't guess. It checks each pending unknown with
  `mentions_meta`, an occurs check, which is exact. The cap only chooses between two exact
  methods. Under D2543 it can stay. Stage 4a may replace both with the reader's `mentions`,
  for one code path, but needn't. **[checked]** So SW-1739, as worded ("KNOWN_CAP answers
  'may mention' when it runs out"), is true of `mentions_unknown` only.
- **`normals`.** It reads a single scrutinee's normal form back only up to the size of the
  largest term it is looked for in (SW-982). A normal form larger than every target can't
  occur in any of them syntactically, so `None` ("not found") is the exact answer, not a
  guess. The cap is a proof of absence, not a limit. It stays as it is until 6b replaces the
  search. **[checked: the doc comment at `matching.rs:1372–1392` gives the argument]**
  SW-1747 put it among the four sites that choose. That is a misreading, and the main
  note's §4.4 needn't list it.

### 3.4 `ignorable_arguments` and the held `lane/SW-1743`

`lane/SW-1743` (`340435397`) read the normal form up to 4,096 nodes and, past that, folded.
The answer then depended on the cap, which is why it wasn't merged. SW-1779 (D2567) has
since done the D2543-consistent version on `main`: always folded, no cap. The folded form's
variables are a superset of the unfolding's, so the rule is fixed and conservative. At worst
an argument isn't ignorable where the unfolding would allow it, and its `auto` proof is then
searched for instead of solved by unification. **[checked at `check.rs:3885–3923`; cited
SW-1786 "Fix 1"]**

**The right fix, then, is already merged.** What is left:

1. The branch is superseded. Delete it (`git branch -D lane/SW-1743` and the worktree) and
   close SW-1743 as done by SW-1779. Its one useful piece, the test
   `a_large_type_still_marks_the_variables_it_mentions`, is covered by `main`'s
   `resources::a_doubling_hypothesis_is_never_unfolded_in_full`.
2. `.ok()?` turns a failed folded read-back into "nothing ignorable". That is a swallowed
   resource error deciding an answer, which D2540 rules out. It should propagate (stage 4b).
3. Don't make it exact with the reader. Exactness would need to open every call whose
   arguments mention a variable, to see whether it drops it, which is SW-1779's
   exponential case again. Nothing needs the extra permission. If a program does, that is
   the time.

### 3.5 Three more that choose

- **`omega` and `ring` atoms** (`omega.rs:2370`, `ring.rs:941`): conversion under a fixed
  20,000-step attempt, with `== Ok(true)`. Running out means "different atoms". §4.
- **`rewrite.rs:707` and `lib.rs:4960`**: `is_ok_and` on an unfolded read-back, so a
  failure answers "no unknown in the premise" or "no dependency". Stage 4b makes them exact
  `mentions` questions that propagate.
- **`check.rs:1531` (`refines_to`) and `cases.rs:1157` (`Finder::new`)**: a failed read-back
  answers "not equal" or skips a known equation. They are search internals, so 6b replaces
  them; until then they are on stage 7's list.

### 3.6 Limits that choose only a representation, or a search's next candidate

A few fixed limits change what is *written*, or which candidate a search goes on to, but
never whether a question with one answer gets the right one:

- **`cheaply`** (`unify.rs:2681`, 100,000 work): whether a `let`'s value is folded back into
  a solution (`refold`, `lift.rs:1051`), and whether `Ctx::define` evaluates a `let` now or
  lazily (`check.rs:464`). The meaning is the same either way, and the limits are an attempt
  whose bounds don't depend on the enclosing operation, so the outcome is the same in every
  build.
- **Candidate searches**: `search.rs`'s `ATTEMPT` (200,000 work per candidate; a candidate
  over it "is no match and is counted, as `outOfBudget`") and `closing.rs`'s four attempts.
  Each candidate gets its own fixed limit. A candidate that runs out is skipped, and the
  search goes on to the next.

Failing on these would make every search as fragile as its most expensive candidate. Lean
gives tactics such as `exact?` per-candidate limits in the same way. I recommend D2543 be
read as covering *questions with one answer* (does this mention, are these the same, what
is this read back), and not these two kinds, provided each is deterministic and a search
says when it skipped a candidate for its limit (D2613). **[inferred]**

### 3.7 How to fail clearly without breaking what relies on today's choice

The same steps for every site:

1. **Count first.** 0c logs, per site, how often the limit fires on std, AoC, the roguelike
   and the examples, and in which declarations.
2. **Then make the site exact**, so it answers what the small case answers. Most programs
   that relied on the cap relied on it to avoid a blow-up, not to get a different answer,
   and the exact reader avoids the blow-up in the same cases, because it opens only calls
   that could matter (§3.1).
3. **What still runs out is an error that names the call** and says how to go on:
   `rewrite f` or `f.unfold` to open one definition, `opaque` to close one, or a `let` to
   name a large value.
4. **A program that relied on the choice is rewritten in the lane**, as §8 of the main note
   does for D2542. The lane stops and reports if more than five need it (D2614).

## 4. Omega and ring atoms

### 4.1 What the code does

`Quoter::atom` (`omega.rs:2350`) decides whether a value is an atom it has seen before, in
three steps:

1. **Same normal form.** It reads the value back unfolded (`cx.quote`, propagating
   E-RESOURCE) and compares it syntactically (`matching::same`) with each earlier atom's
   unfolded `term`.
2. **Convertible.** It runs `conv` against each earlier atom, under a fixed attempt (20,000
   work, 10,000 size). `== Ok(true)`: running out counts as "different". This is SW-1435's
   fix, so that a sum as a hypothesis states it and the same sum as `rewrite … at` left it
   are one atom (`examples/accept/omega-atoms-by-conversion.sw`).
3. **Unifiable.** If either side has an unknown and the two unfolded terms have the same
   shape (`same_shape`), it tries to unify them, under 1,000,000 work, undone on failure.

**[checked]**

The certificate uses a separate folded read-back (`written`). The unfolded `term` serves
only identity, `same_shape`, and two message hints (`one_argument_apart`,
`replaced_by_match`, `omega.rs` 2544 and 2555). The other 20 `same` sites compare a part of
one recognised operation with another value: is this division's numerator that atom,
`sub_nat_nat`'s operands, `mul_left`'s factor, `nat_abs_dichotomies`, `linear_once`'s swap
test, `division_facts`' fuel. `ring.rs:932` repeats steps 1 and 2. **[checked]**

### 4.2 Options

| | (a) conversion only | (b) folded key, then conversion | (c) folded key only |
|---|---|---|---|
| Identity | `conv` against every earlier atom | folded `same` first; then `conv` against earlier atoms with the same head once forced | folded `same` |
| Complete? | up to definitional equality, which is more than today's syntactic normal-form equality (eta, proof irrelevance) | same as (a) | **no**: misses `List.sum xs` against its `foldLeft` form (SW-1435) and every other pair that is equal only after unfolding, so `omega` reports a false counterexample where today it proves |
| Sound? | yes: the certificate is kernel-checked | yes | yes |
| Cost | one `conv` per earlier atom, even for identical atoms | identical atoms: one folded read-back, which is already done for `written`, so free. Different heads: a whnf each, then nothing. Same head, different arguments: `conv` compares the arguments first, then unfolds both, at most what today's two unfolded read-backs cost, without building the terms | cheapest |
| Large atoms | no read-back: bounded by `conv`'s limit | the same | no read-back |

**Recommendation: (b)** (D2612). It keeps everything `omega` proves today, since conversion
identifies every pair the normal forms do. It drops the one step that can build ten million
nodes. It costs no more than today on identical atoms, and no more than today's step 2 (which
already runs a `conv` against *every* earlier atom whenever step 1 misses) on different ones.
Bucketing by forced head cuts those `conv`s down to the pairs that could be equal. Step 3
compares the folded terms' shapes. **[inferred]**

**Its limit, under D2543.** Conversion runs under a fixed limit of its own (as now). Running
out is `E-RESOURCE`: "`omega` couldn't tell whether `a` and `b` are the same atom within …
steps", with the two atoms shown folded and the ways on (`let`-name one, or state their
equality as a fact). It no longer means "different". The risk is a proof that checks today
only because a `conv` ran out and the atoms were treated as distinct, where distinct was
enough. That is plausible: `omega` often doesn't need two atoms identified.

So the stage first measures, under a debug switch (`STITCHWORT_OMEGA_BOTH`, as
`STITCHWORT_DECIDE_BOTH`): for every atom, the old answer and the new one, the steps of each
`conv`, and every limit hit. It runs over `std`'s `omega` and `ring` examples and the AoC
namespaces that use `omega` most (§5, stage O). Then it sets the limit above the largest
`conv` that answered "same". If a `conv` that answered "different" still runs out, the lane
stops and reports before turning it into an error. **[0c and O measure]**

**The other 20 `same` sites** become `conv` on the two values, under the same limit. The
two hint sites become folded, with stage 5's `shown` for display. `recomputed`
(`omega.rs:2418`) compares folded: it only asks whether recomputing changed anything, and a
change in the folded form is a change. The lane checks the loop that calls it still ends.

## 5. The stages

Each stage is one lane. The stage names keep revision 3's where the stage survives. New:
**1c** (the remaining output sites), **4a/4b/4c** (stage 4 split in three), **O** (`omega`
and `ring`). Gone: 0a, 0b, 1 and 1b (done), and the D2544 experiment (not adopted).
Estimates follow how recent lanes went: Opus design-heavy lanes in this epic ran at 0.3 to
0.7 of their estimate (SW-1746 21 min, SW-1748 41, SW-1779 20, SW-1782 48), while the
`rewrite`/`match` stages ran at 0.8 to 1.1 (SW-1627 to SW-1630). The estimates are stop
points, not predictions.

### 5.1 Order

| Order | Stage | Model | Est. (min) | Needs | Can run beside |
|---|---|---|---|---|---|
| 1 | **0c** metrics | Sonnet | 45 | D2536 (agreed) | 1c, R |
| 1 | **1c** remaining output sites | Sonnet, Opus review | 60 | — | 0c, R |
| 1 | **R** `rewrite f` (SW-1631) | Opus | 90 | D2610 | 0c, 1c |
| 2 | **4a** the reader; `scanned`, `mentions_unknown` | Opus | 100 | 0c | M |
| 2 | **M** the measured proofs (main note §8) | Sonnet | 45 | R | 4a |
| 3 | **4b** the other mentions sites | Sonnet | 75 | 4a | 4c, 5, O |
| 3 | **4c** zonk | Opus | 75 | 4a | 4b, 5, O |
| 3 | **5** `shown`; messages | Sonnet | 60 | 4a | 4b, 4c, O |
| 3 | **O** `omega` and `ring` atoms | Opus | 90 | 0c, D2612 | 4b, 4c, 5 |
| 4 | **3** the reader's `find` | Opus | 120 | 4a | — |
| 5 | **6a** `rewrite` under D2542 | Opus, Opus review | 100 | 3, M | — |
| 6 | **6b** `match`, `cases`, the transport under D2542 | Opus, Opus review | 110 | 6a | — |
| 7 | **7** no recovered E-RESOURCE decides | Sonnet, Opus review | 45 | 6b | — |

About 1,015 minutes in all: Opus 685 (R, 4a, 4c, O, 3, 6a, 6b), Sonnet 330. Against revision
3's remaining 765 minutes (0c, 4, 5, R, M, 3, 6a, 6b, 7), stage 4's split adds 160, and 1c
and O add 150 that revision 3 didn't plan. Revision 3 didn't know stage 1 would leave
sites, and didn't cover `omega`.

**Why this order.** D2545 put R after stages 4 and 5. R doesn't use the reader, and touches
only `rewrite`'s rule parsing and one new step, so it can start now, and M (which uses it)
is then ready before 6a needs it. That reorders Matt's decision, so it is D2610. The rest
is sequencing (mine):

- 0c before 4a and O, since the limits' values and the at-risk programs come from its
  counts;
- 4a before everything that uses the reader;
- 4b, 4c, 5 and O side by side, in different files. 4c is `unify.rs`'s zonk; 4b is
  `unify.rs`'s callers. Moderate conflict risk at most;
- 3, 6a and 6b in a line, as before;
- 7 last.

If SW-1829 finds that one of §1.2's sites caused the AoC regression, that site's stage goes
first.

**Running out, in every stage.** Each reader question runs under fixed limits of its own
(an attempt, as `cheaply`), and its running out is `E-RESOURCE` naming the largest call
opened, never recovered into another answer (main note §4.4). Each brief says so in these
words, since SW-1743's brief didn't, and its lane built a limit that chooses.

### 5.2 Briefs

Each block can be pasted into a brief. Each brief also carries CLAUDE.md's standing lines:
the worktree, time stops, "no daily or full tier", and `stitchwort fmt`, `cargo fmt` and
clippy.

---

**0c. Metrics: where today's limits choose** (Sonnet, 45 min; D2536 covers its run)

- *Goal:* counts that tell 4a, 4b, O and 7 which programs rely on a limit choosing, and how
  large the questions are. No behaviour change.
- *Sites:* behind `STITCHWORT_READBACK_METRICS`, one line per event, with the site, the
  declaration and node or step counts:
  - `scanned` taking its folded fallback (with the caller);
  - `mentions_unknown` answering "may" on the cap;
  - `on_pending` taking its occurs-check path;
  - `omega.rs:2370` and `ring.rs:941` attempts that run out, and those that answer "same";
  - zonk's whole-solution fallback (`unify.rs:2894`);
  - each of the five recovered sites and each swallowed site of §3.5 recovering;
  - message sides over 10,000 nodes;
  - per site, the largest unfolded read-back.
- *Run:* one background run each of std, AoC, the roguelike and the examples on `main`,
  stopped at 6 minutes. That is D2536's exception, as agreed for 0c, now on `main` only,
  since record eta has merged. If SW-1829 is still open, run after its fix, or AoC won't
  finish.
- *Tests:* `task test:one -- readback_metrics` (a new unit test that the switch is off by
  default and the lines parse).
- *Success:* a table in `docs/reviews/SW-N-stage-0c.md` with one row per site: events,
  declarations and the largest size. It also names every declaration where a cap fired.

---

**1c. The output sites stages 1 and 1b didn't reach** (Sonnet, 60 min; Opus review, since it
generates kernel terms, D2364)

- *Goal:* every term the elaborator writes out is read back folded (D2523), except for the
  deliberate list in the main note's stage 1 text.
- *Sites:* the first row of §1.2. Look at `defaults.rs:1239` and `equations/induct.rs` 975,
  1454 and 1812 one at a time. They read a forced type only to match its head, so they
  need the head of the forced value, not a read-back at all. `defaults.rs:1239` is the one
  that could regress: a head whose type is a `Pi` only after unfolding (SW-1747 item 7).
  `cases.rs` `take_apart` builds `J` terms, so check that its motive still type-checks.
- *Not:* `equations.rs`'s six; `derive_induct.rs` `field_type` and `move_to`; anything that
  feeds a search or a mentions test.
- *Tests:* `task test:lane AREA=elab`; `task snap:hashes` and `hash_stability`; the
  `*_bound_to_the_prelude` tests in `extract.rs`; `task test:one --` the examples whose
  snapshots move.
- *Success:* the grep of §1.1 finds none of these lines. Hash moves are explained (each by a
  call now written as a call). No proof changes.

---

**R. `rewrite f`: one step of `f` by name** (Opus, 90 min; Opus review, since it generates
`J` terms; SW-1631; D1433, D2480)

- *As in the main note, §7, stage R.* A rule naming a definition replaces its visible calls
  by one step of their unfolding, and the next goal is read back folded. A definition with
  arms needs its arguments to select an arm; otherwise an error suggests `match`.
- *Docs:* `docs/syntax.md` ("rewrite"), the language guide's proofs chapter with a checked
  example, and a feature-tour page if it reads well there (CLAUDE.md "Always").
- *Tests:* new accept and reject examples (`rewrite-unfold-one-step.sw`, and a reject for a
  definition whose arguments don't select an arm); `task test:one -- rewrite`.
- *Success:* the examples check. No existing hash moves. SW-1653's day 20 `memEq` is tried
  with it and reported, not required.

---

**4a. The reader, part 1; the two limits that choose in instance search and the unifier**
(Opus, 100 min)

- *Goal:* `crates/core/src/readback.rs` with `mentions(value, vars, metas, consts)` and
  `unfold_where(value, pred)` (main note §4.2), the free-variable rule, a memo per question
  that holds the `Rc`s it keys on (§2, SW-1800), and fixed limits whose running out is
  `E-RESOURCE` naming the largest call opened. Then `scanned` and `mentions_unknown` move to
  it, and their caps go (§3.1, §3.2; D2611).
- *Design points:*
  - a field call (`Elim::Proj` on a call's spine, §2) opens through its base call, memoised
    on the base call's cell;
  - a variable of a record whose fields are all proofs is relevant (SW-1725);
  - `mentions` takes constants, for `equations.rs:5064` and `effects.rs:5118`;
  - SW-1698 first: `identical` and `free_variables` in `core/src/value.rs` take no budget
    steps, so a walk over a huge value ignores the limit. The reader must step, and those
    two should too.
- *Sites:* `interfaces.rs:1399` and its 8 callers (`unknown_notes` reads folded);
  `unify.rs:979`. `on_pending` may stay (§3.3).
- *Tests:* unit tests in core for `mentions` (a variable dropped by `keep a b := a`; one in
  a proof position; one only in an unsolved unknown's arguments; a field call) and for
  `unfold_where`. Then: `task test:one -- lemma-on-large-normal-form` (accept and reject);
  `stitchwort check --no-cache` on `Aoc.Year2024.Day06.Proofs` (the program that brought in
  `SCAN_LIMIT`); `task test:lane AREA=elab`; `the_trip_journal_checks`; 0c's declarations
  where either cap fired.
- *Success:* no `SCAN_LIMIT` and no `KNOWN_CAP` in `mentions_unknown`. Every declaration 0c
  listed still checks, or is rewritten here (D2614). A new reject example shows the reader's
  `E-RESOURCE` naming a call. Day 6 is no slower.

---

**M. The measured proofs rewritten** (Sonnet, 45 min; as in the main note §7 and §8)

- Unchanged, except that it now runs on `main` after R. Rows 1, 2, 4, 6 and 7 of §8, each in
  a form that checks under today's rule and D2542's. Checked one declaration at a time. The
  orchestrator checks that no statement changed (D2436).

---

**4b. The other mentions sites** (Sonnet, 75 min)

- *Goal:* every mentions question of §1.2's 4b row answered by the reader, exactly, with
  errors propagated, not swallowed.
- *Sites:* as listed in §1.2. In particular:
  - `rewrite.rs:707` and `lib.rs:4960` stop answering "no" on failure;
  - `ignorable_arguments` keeps its folded rule but propagates its error (§3.4);
  - `derive_induct.rs:632` (`pred_levels`) and `move_to` (1259) move together, or not at
    all (SW-1784 §1).
- *Tests:* `task test:one --` with SW-323's `ignorable` tests, the `bind.rs` tests and
  `effects`; `task test:lane AREA=elab`; `task test:lane AREA=effects`.
- *Success:* the grep finds none of these lines. No hash moves, since mentions answers don't
  write terms; any that does move is explained.

---

**4c. Zonk** (Opus, 75 min: the unifier, D2506)

- *Goal:* main note §2.3 and §4.3's zonk row: `zonk_changed`'s fallback becomes
  `unfold_where(solution, args mention an unsolved unknown)`. `both_forms` gets the mixed
  form as a third form for `refold`. The zonk-like round trips (`effects.rs:3986`,
  `families.rs:702`, `rows.rs:250`) are checked one by one, since each feeds unification
  (SW-1784 §5). `proof_expected` (`check.rs:4980`) uses `unfold_where` when its folded term
  holds an unknown (SW-1758).
- *Tests:* zonk's unit tests in `unify.rs`; `task test:one -- postponement`;
  `task test:lane AREA=elab`; `hash_stability` and `task snap:hashes`.
- *Success:* hashes move only where 0c saw the fallback fire. A solution term is never
  larger than before. `Rogue.Proofs` is measured, and SW-1762's `resolveOutOfWalls` is
  reported: its motive is 6b's, so only part of it is expected here.

---

**5. `shown`; messages** (Sonnet, 60 min)

- *As in the main note's stage 5.* One read-back per side per error, eliding with `⋯`, and
  shared by every note through a cache on the error being built.
- *Also:* the four sites where a resource error replaces the intended error (§1.2) swallow,
  as the others do; `omega.rs` 2544 and 2555 use `shown`.
- *Tests:* the E-REFL and E-TYPE-MISMATCH snapshots unchanged; a new large-side snapshot;
  `task test:one -- rewrite-value-too-large`.
- *Success:* no message site reads back past `NOTE_BUDGET`. Snapshots move only where a side
  is over 10,000 nodes.

---

**O. `omega` and `ring` atoms by conversion** (Opus, 90 min: a tactic, D2506; D2612)

- *Goal:* §4.2 option (b): folded key, then conversion within the forced head's bucket,
  under a fixed limit whose running out is `E-RESOURCE` naming both atoms. The 20 part-of-
  an-operation `same` sites use `conv` too; `ring.rs:932` the same; `recomputed` compares
  folded. The unfolded `term` field goes.
- *First, measure:* `STITCHWORT_OMEGA_BOTH` (both answers per atom, `conv` steps, limit
  hits). Run it over `task test:one -- omega` and `-- ring` (the examples), then
  `stitchwort check --no-cache` on the AoC namespaces that use `omega` most:
  - `Aoc.Year2024.Day06.Proofs` (`Sightlines.sw`, 48 uses);
  - `Aoc.Year2024.Day12.Proofs` (`Corners.sw`, 33);
  - `Aoc.Common.Proofs` (`Offset.sw` 30, `Plane.sw` 29);
  - `Aoc.Year2025.Day02.Proofs` (`Part2.sw` 27, `Repeated.sw` 26);
  - `Aoc.Year2020.Day18.Proofs` (27);
  - `Aoc.Year2025.Day03.Proofs` (25).

  Set the limit above the largest "same" `conv`. If any "different" `conv` still runs out,
  stop and report before making it an error.
- *Tests:* `omega-atoms-by-conversion.sw`, `omega-computed-forms.sw`,
  `omega-after-rewrite-field-turn.sw`, `ring-after-rewrite-field-turn.sw`,
  `omega-projected-field-atom.sw`; the namespaces above.
- *Success:* the two answers agree, or the new one identifies more, on every atom measured.
  Each namespace above takes no more steps than on `main`. No `cx.quote` is left in
  `omega.rs` or `ring.rs` outside `Quoter`.

---

**3, 6a, 6b.** As in the main note §7, with these additions:

- **3:** the reader's design points from 4a (field calls, the memo) apply to `find`.
- **6a** also absorbs:
  - SW-1723 (E-REFL's note: it is the main note's §4.1 note);
  - SW-1691 (`rewrite … at h` with a large hypothesis);
  - SW-1699 (a stack overflow where `main` says "too large");
  - SW-1654 (motives left unchecked because of unknowns);
  - `rewrite.rs:588` (`discharge`'s round trip, SW-1784 §5);
  - SW-1387: the next goal read back folded should let `CongRangeFrom` go. The lane checks,
    and files the clean-up if so.

  It retires SW-1697 and SW-1709 (their warnings and examples go).
- **6b** also takes:
  - `matching.rs` 512, 521, 657 and 851 (§1.2's correction);
  - `check.rs:1531` and `cases.rs:1157` (§3.5);
  - SW-1687 (`blocker`'s unlabelled `?`).

  It measures SW-1762's `resolveOutOfWalls` before and after (success: back near 4.6k
  nodes, or the reason it isn't).

---

**7. No recovered E-RESOURCE decides** (Sonnet, 45 min; Opus review)

- *Goal:* main note stage 7: "too large to show" stops being recoverable (`undo.rs`). Every
  site 0c listed that 6a and 6b didn't remove fails instead of recovering.
- *Tests:* 0c's declarations, one by one; `task test:one -- as-written` (whatever 6a and 6b
  left of those examples).
- *Success:* a grep for `.ok()`, `is_ok_and` and `if let Ok` on a read-back finds only
  message sites.

## 6. Questions for Matt

- **D2610: start `rewrite f` (R, SW-1631) now, beside 0c and 1c, rather than after stages 4
  and 5.** That amends D2545. [rec: yes. R uses no part of the reader, so waiting gains
  nothing. Starting it now has M ready before 6a, and gives users the documented way to
  look inside a definition sooner. Every failure message in 4a and O can then suggest it.]
- **D2611: the two limits that choose in instance search and the unifier go, and their
  questions are answered exactly by the reader** (`scanned`, §3.1; `mentions_unknown`,
  §3.2). A reader question that runs out is `E-RESOURCE` naming the call. `on_pending`'s
  cap and `normals`' cap stay, because they are exact (§3.3). [rec: yes. It is D2543 applied
  to the last two such sites. The program that brought in `SCAN_LIMIT` (2024 day 6) should
  keep checking, because its large call holds no unknown, so the reader never opens it. 0c's
  counts say whether anything else relies on the caps before 4a starts.]
- **D2612: `omega` and `ring` identify atoms by the folded form first, then by conversion
  within the forced head, not by the unfolded read-back** (§4.2 (b)). Conversion's running
  out becomes an error rather than "different atoms". [rec: yes. It keeps every
  identification today's normal forms make, since conversion is complete for them. It
  removes the one step that builds ten million nodes. It costs no more than today's
  fallback, which already runs a conversion per earlier atom. Folded alone, option (c),
  would undo SW-1435. The lane measures both answers before switching, and stops if a
  conversion that answers "different" runs out.]
- **D2613: D2543 covers questions with one answer, not limits that choose only a
  representation or a search's next candidate** (§3.6: `cheaply`'s refold and lazy `let`s;
  `search.rs`' and `closing.rs`' per-candidate attempts), provided each is deterministic and
  reports a skipped candidate. [rec: yes. Failing a whole search on one candidate's limit
  makes it as fragile as its most expensive candidate. Lean gives such searches
  per-candidate limits too. The meaning of a result never depends on these limits.]
- **D2614: a program that relied on a limit choosing is rewritten in the lane that removes
  the limit**, as §8 of the main note does for D2542. The lane stops and reports if more
  than five need it. [rec: yes. It is the same rule as D2542's migration. 0c names them
  before any lane starts, so none comes as a surprise.]

Decided by me, as sequencing or reading, not questions: the order within §5.1 apart from
R; splitting stage 4 in three; stage 1c, which D2523 already covers; closing SW-1743 and
deleting its branch (§3.4); SW-1725's answer (§2); `normals` and `on_pending` read as exact
(§3.3).

## 7. Tickets this plan settles or absorbs

| Ticket | Outcome |
|---|---|
| SW-1750 | Answered by §3. Its four sites: `scanned` and `mentions_unknown` change in 4a (D2611); `on_pending` and `normals` are exact and stay. Close when 4a is filed. |
| SW-1739 | Answered by §3.2 and §3.3: true of `mentions_unknown` only, which 4a changes. |
| SW-1749 | Answered by §4; stage O. |
| SW-1757 | Done here: §1.2's correction, and the main note's §2.5 table. |
| SW-1743 | Superseded by SW-1779 (§3.4): close, and delete `lane/SW-1743`. |
| SW-1725 | Answered in §2: no eta for proof-only records; the skipping rule's clause goes. |
| SW-1758 | Stage 4c. |
| SW-1759 | Not in a stage: a small chore (cache the environment lookup in a `OnceLock`; say in the doc that the extra run's steps aren't refunded). DeepSeek, 15 min, any time. |
| SW-1762 | Measured in 4c and 6b. |
| SW-1723, SW-1691, SW-1699, SW-1654 | Stage 6a. SW-1697 and SW-1709 are retired by it. |
| SW-1687 | Stage 6b. |
| SW-1698 | Stage 4a, first. |
| SW-1631 | Stage R. |
| SW-1387 | Checked in 6a. |
| SW-556 (D1280's cap), SW-1724 | Stay deferred (main note §9 and §11). |

## 8. What this note did not do

- It ran nothing.
  - The counts §3 relies on ("at risk: none known") are 0c's to measure.
  - The cost comparison in §4.2 is reasoned from the code. Stage O measures it first.
  - The estimates are not measured.
- It read the four sites SW-1750 named, the omega and ring atom code, and the callers named
  here. It didn't re-read every row of SW-1747's table on `main`. §1.2's lines come from a
  fresh grep, and the kinds come from SW-1747.
- It doesn't know SW-1829's cause, which may reorder §5.1.
- It didn't edit `board/tickets.json` (the brief said not to). §7's outcomes are for the
  orchestrator to record.
