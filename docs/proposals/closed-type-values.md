# Closed type values: stop computing a statement's big values when it's declared

**Status:** proposal, 7 November 2026, waiting for Matt's decisions (§7).
Ticket SW-1787 (from SW-1779). It reopens
[glued-closed-types.md](glued-closed-types.md) (SW-1534, parked by D2448
until "a real proof whose closed statement names a big computation"
turned up; this is that proof) and is tied to SW-1782 (§6). Related:
[folded-calls.md](folded-calls.md) (glued calls, D483, "As built (stage
4)"), [opaque-definitions.md](opaque-definitions.md) (the transparency
set), [globals-split.md](globals-split.md) (D2294: admission fixes its
own modes).

## 1. The problem

A theorem's statement with no parameters is computed in full when the
theorem is declared, even when nothing needs the result. 2024 day 22:

```
theorem digitChangesPossible: HoldsDigitChanges (sequencesOf possibleChanges) := …
theorem bestTotalCorrect (count: Nat) (buyers: List Nat): … :=
  bestTotalAmong (sequencesOf possibleChanges) digitChangesPossible count buyers
```

`sequencesOf possibleChanges` is a list of 19^4 = 130,321 records. The
kernel builds it when `digitChangesPossible` is declared, and walks it
twice more: once to compare it with the body's type, and again in
`bestTotalCorrect`, which passes the theorem along. Measured on this
branch's base (release build, `check --no-cache
Aoc.Year2024.Day22.Proofs`):

| declaration | kernel ms | kernel steps | term nodes |
|---|---|---|---|
| `digitChangesPossible` | 3,656 | 80,625,702 | 10 |
| `bestTotalCorrect` | 1,853 | 43,596,922 | 34 |

That's 5.5 s of kernel time for two short proofs (SW-1779 measured 4.4 s
in a whole-aoc run, 29% of aoc's kernel time). Nothing in either proof
looks inside the list.

SW-1779's six-line reduction, extended by one line for the citing case:

```
import Std (List, Nat)
def Holds (xs: List Nat): Prop := (a: Nat) → a ∈ xs → a = a
def many: List Nat := List.range 0 100000
theorem holdsAll (xs: List Nat): Holds xs := a _ => rfl
theorem holdsMany: Holds many := holdsAll many        -- 292 ms, 3.4 M steps
theorem usesMany (n: Nat): Holds many := holdsMany    --  82 ms, 2.0 M steps
```

### Why it happens

The kernel keeps every definition's type as a value, `Def::ty_value`,
made by `push_def` (`check.rs`) when the definition is declared. It's made
with gluing off, because the kernel's entry points run in fixed modes
(`in_kernel_modes`, D2294). Without gluing, a call is unfolded as soon as
it's made, so a type with no parameters (`Holds many`) is evaluated all
the way down: the whole list. A type with parameters doesn't have the
problem, because its value is a function type whose result part is
evaluated later, while a body is checked with gluing on.

Then the two checks that use it:

- **The theorem's own body.** `admit_group` checks the body with gluing
  on, against `def_type`, which is `ty_value`. The body's inferred type is
  the glued `Holds many`; comparing it with the unfolded list forces the
  glued side and walks both lists.
- **A proof that cites it.** `infer` of `Term::Def` also returns
  `def_type`, the unfolded list, which `conv` compares with the citing
  proof's glued expectation, walking both again.

With both sides glued, `conv` would see two calls of the same definition
with the same arguments and answer "equal" at once (D483's rule). The
unglued `ty_value` is what stops that.

### Why it is kept unglued

folded-calls.md, "As built (stage 4)": a type's value "is still made
unglued, so nothing glued outlives the check". A glued call
(`Value::Call`) carries a cell for its unfolding, filled the first time
anything looks inside and shared by every copy. A glued value kept in a
`Def` would live for the whole session, and its cells would be filled by
whoever forces them first, in whatever mode they're in:

- **Transparency.** Forced while some body is checked with an opaque
  definition visible (`unfolding X`), a cell can hold an unfolding that
  used `X`'s body. Read later where `X` is hidden, it hands that back. Not
  a logical unsoundness (`X` is still a definition), but what is accepted
  would depend on what was checked before: against D2294 and opacity's
  promise that a proof outside doesn't depend on the body.
- **Erasure.** Forced while a program runs (rt's `telescope` reads
  `ty_value`), a cell can hold an unfolding computed with proofs erased,
  then reused by the checker.
- **Gluing itself.** Forced with gluing off (`decide`), a cell holds the
  full unfolding with no calls left in it. A later folded read-back that
  takes the cached unfolding writes out that whole value where a glued
  unfolding would have stayed small. That's SW-1782.
- **Steps.** Even with every mode matched, whether a cell is already full
  depends on history (what was checked earlier this session, or whether a
  module came from the cache). Results can't change, but step counts can,
  and with them, at the margin, whether a declaration fits its budget.

Today the kernel is safe from all four by construction: its kept values
have no glued calls, and the glued values made while checking a body are
dropped when the check ends. The kernel reads its cells only at epoch 0
(`Unfolding::get`), so it never sees a cell the elaborator filled, but the
elaborator does read cells the kernel filled ("epoch 0 holds in any").

## 2. Who reads `ty_value`

About 45 sites read it directly; the kernel's checking reads it through
`def_type`.

- **Kernel checking:** `def_type` (`check.rs`), for the type of a
  referenced definition (`infer` of `Term::Def`), of the definition whose
  body is being checked (`admit_group`), in `define_group`'s other path
  and in `inert.rs`. When the transparency set isn't empty, `def_type`
  already evaluates `def.ty` again instead.
- **Kernel shape checks, not conversion of proofs:** binding natives
  (`native.rs`, `float.rs`, `nat_add.rs`: `conv` of the expected shape
  with `ty_value`), `add_validator`'s `telescope`, `partial.rs`. All look
  at function types with small domains.
- **The elaborator:** its own `def_ty` goes through the kernel's
  `def_type`; most other uses read `ty_value()` directly to walk a
  telescope or find a head: instance search (`interfaces.rs`), `auto`,
  `omega`, `ring`, numbers, `unify.rs` (a definition's type when solving
  under a spine), `library.rs`, `decreasing.rs`, the counterexample search
  (`quote` of the statement).
- **Programs and tools:** erasure and extraction (`erase.rs`, `js`), rt's
  `telescope`, `audit.rs`, `run.rs` (printing a type).

Nothing needs the unglued value as such: every reader either forces what
it looks at (and a glued value forces to the same thing) or reads it back
with `quote`, which unfolds glued calls and gives the same term.

## 3. The options

Probes (code only for measurement, not committed) on this branch's base,
release build. Kernel ms and steps for the two day 22 theorems and the
whole `Aoc.Year2024.Day22.Proofs` check; wall time is noisy (load average
7 to 11), steps aren't. All four builds checked the namespace without
errors and wrote the same number of term nodes (654,128 in 3,771
declarations).

| build | `digitChangesPossible` | `bestTotalCorrect` | namespace kernel ms | wall s | repro `holdsMany` / `usesMany` |
|---|---|---|---|---|---|
| base | 3,656 ms, 80.6 M | 1,853 ms, 43.6 M | 6,371 | 11.1 | 292 / 82 ms |
| A: `ty_value` glued | 0.0, 963 | 0.0, 828 | 589 | 4.0 | 0 / 0 |
| C: fresh glued type per use, `ty_value` unglued | 1,107 ms, 37.0 M | 0.0, 954 | 1,699 | 5.1 | 62 / 0 |
| C + `ty_value` glued (the proposal) | 0.0, 1,054 | 0.0, 954 | 581 | 4.3 | 0 / 0 |

### Option 1: compute `ty_value` lazily

`ty_value` becomes a cell, filled (unglued) on first use.

- **Day 22:** no gain on its own. The theorem's body check reads it at
  once through `def_type`, and so does every proof that cites it, so the
  list is built anyway. It helps only combined with a glued value for the
  body check (glued-closed-types.md's option B), and even then a citing
  proof pays in full, and so does any elaborator site that reads the
  type. C's row is an upper bound on what lazy plus a glued body check
  could save: the 37 M steps left are the eager unglued evaluation.
- **Soundness and determinism:** nothing changes; the invariant holds.
- **Memory:** the same as now once it's forced (the whole list, kept for
  the session).
- **Cost:** about 45 read sites become fallible (the evaluation can run
  out of budget), a wide mechanical change for little.

**Not recommended.**

### Option 2: keep a glued value for closed types, with a rule that makes it safe

`push_def` evaluates the type with gluing on (glued-closed-types.md's
option A; the patch is `dev/patches/sw-1534-glued-closed-types.patch`).
The rule: a cell records the modes it was filled in, and is reused only
in matching modes (option 4 below).

- **Day 22:** everything (row A): 5.5 s of kernel time to nothing.
- **Soundness:** with the mode rule, a cell is only reused in the modes
  it was computed in, so no opaque body or erased proof leaks. Without
  the rule, both leaks of §1 are possible.
- **Determinism:** the rule fixes results but not steps. The kernel would
  read cells that an earlier kernel check filled (epoch 0), so a
  declaration's step count would depend on what was checked before it in
  the session, and on whether its dependencies came from the cache. This
  is the one thing A gives up that the proposal keeps.
- **Memory:** better than now. A kept type is a call until something
  outside the kernel forces it; today it's the whole list from the start.
- **Visible changes:** anything that reads a kept type back folded
  (`quote_folded`, the elaborator's `show`) prints `Holds many` where it
  printed the list. That's better for messages. Read-back with `quote`
  (unfolded) is unchanged, so kernel-quoted terms are the same.

### Option 3: keep the type as a term, and evaluate it on demand

`def_type` evaluates `def.ty` afresh in the current mode instead of
handing out `ty_value`. While checking (gluing on) that's cheap: calls
stay calls, so the cost is the size of the statement as written, and for
a function type only its first domain. Optionally remembered for the rest
of one check, and dropped with it (Lean's kernel caches are scoped like
this, from memory, not checked against its source; the argument here
doesn't rest on it).

- **Day 22:** fixes the citing proof and the body comparison, but not the
  declaration's own eager evaluation while `ty_value` stays unglued (row
  C: 37 M steps left). With `ty_value` glued as well, everything (last
  row).
- **Soundness and determinism:** the kernel only ever sees glued values it
  made itself in this check, so "nothing glued outlives the check" holds
  for the kernel by construction, and its step counts don't depend on
  history.
- **Cost:** a glued evaluation of the statement per reference per check.
  Not measurable on day 22 (`bestTotalCorrect` 828 steps with A, 954 with
  C). The probe didn't remember values within a check, and didn't need
  to: two fresh `Holds many` compare equal at once by their arguments.
  The `check-list-rfl` +11% that sank this idea in folded-calls.md stage 4
  came from evaluating every closed type twice (unglued for `ty_value`,
  then glued for the body); with `ty_value` glued, neither evaluation
  unfolds anything.
- **Memory:** values live for one check.

### Option 4: record the modes in cached unfoldings

`Unfolding` keeps, beside its epoch, the modes it was filled in: whether
gluing was on, the transparency set, and whether a program was running
(erasure). `Unfolding::get` reuses it only when the reader's modes match,
with one relaxation: a cell filled with gluing on can be read with gluing
off (an unglued reader forces the calls inside as it goes, and gets the
same value), but not the other way round, since a cell filled unglued has
no calls left and reads back in full. A mismatched reader computes the
unfolding again and stores its own, so each cell holds one value and
memory stays bounded.

- **Day 22:** nothing on its own; the kernel still makes `ty_value`
  unglued.
- **What it fixes:** the class of SW-1782 (§6), in the elaborator, where
  glued values already outlive single forcings within a declaration. And
  it is what makes any session-long glued value safe for its non-kernel
  readers, whichever of options 2 and 3 is chosen.
- **Soundness:** trusted code (`value.rs`), about 15 to 20 lines. It can
  only refuse a cached value, never invent one, so it can't make anything
  accepted that wasn't. A mode the key misses would be the risk, hence the
  test in §5.
- **Cost:** some recomputation where today a cell is reused across modes,
  mainly a glued force after an unglued one (`decide` then a goal
  display). Not measured.
- **Determinism:** results then depend only on the modes, not on which
  mode filled a cell first. Steps still depend on history wherever cells
  are kept; that's why option 3 keeps the kernel off them.

## 4. Recommendation: options 3 and 4 together, with `ty_value` glued

**The change.**

1. Cached unfoldings record their modes (option 4), as SW-1782's fix.
2. The kernel's checking never reads `Def::ty_value`: `def_type` always
   evaluates the statement afresh, glued, in the check it's called from
   (`admit_group` already turns gluing on for bodies; SW-1779 turns it on
   for `declare_def`'s signature check; the shape checks in `native.rs`,
   `float.rs`, `nat_add.rs`, `add_validator` and `partial.rs` go through
   `def_type` too, in the same mode they run in now).
3. `push_def` and `retype_def` make `Def::ty_value` with gluing on, so
   it's a call, not a computed value, for the elaborator, programs and
   tools. Their reads are safe by step 1.
4. The proving guide's workaround (§6, "A statement with no parameters is
   computed when it is declared") goes, and glued-closed-types.md is
   marked superseded by this note.

**What it should do.**

- Day 22's two theorems go from 5.5 s of kernel time to nothing (measured
  in the probe, last row of §3), and `Aoc.Year2024.Day22.Proofs` from
  6.4 s of kernel time to 0.6 s. The reduction goes from 374 ms to
  nothing. SW-1534's `countdown 0 100000000 = countdown 0 100000000`
  should check at once.
- The kernel's invariant becomes simpler to state and holds by
  construction: *the kernel evaluates only terms, and every value it
  makes is dropped when its check ends*. Its results and its step counts
  depend only on the declaration and what it refers to.
- Session-long glued values exist only outside the kernel, and their
  cells are reused only in the modes they were made in.
- Kernel-quoted terms are unchanged (`quote` unfolds as before). Folded
  read-backs of a kept type, and so messages and possibly some elaborated
  terms, show the call instead of its value. Hashes may move once.

**Why not A alone.** It gives the same speed (row A) with less code, but
lets the kernel read cells filled by earlier checks: its step counts
would depend on session history and on the cache. Option 3's extra cost is
a glued evaluation of each statement where it's used, which didn't show
up in the measurements.

**Order.** Step 1 is SW-1782's lane (it has its own check: rerun
SW-1748's instrumentation and see the twelve Rogue hashes stay). Steps 2
and 3 come after it, and after SW-1779 is merged, since SW-1779 changes
`declare_def`'s gluing on the same lines. Both are kernel work, on Opus,
and the change that turns `ty_value` glued is reviewed on Opus (D2364).

## 5. Evidence still to collect, in the implementation lanes

- A kernel test that forces a glued kept type's call under one
  transparency set, then reads it under the empty one, and must not see
  the opaque body; the same for erasure (a program forcing it, then the
  checker).
- A test that the kernel's steps for a declaration are the same whether
  or not the elaborator, or an earlier declaration, forced its
  dependencies' kept types first.
- The bench baseline (`crates/bench`, `check-list-rfl` and the others:
  steps should fall or stay), the hash snapshots (`snap:hashes`,
  `hash_stability`), the `conv_shortcut` sweep, the core and elab lanes,
  and the natives' `bound_to_the_prelude` tests (native binding reads the
  type).
- Whole-aoc kernel time and steps against SW-1779's figures (needs
  Matt's OK, as a whole-AoC run).
- The cost of option 4's recomputation where a cell is now reused across
  modes, in elaborator steps on rogue and a few AoC days.

## 6. How this relates to SW-1782

SW-1782: whether a call's unfolding is already cached changes what a
later folded read-back writes (an extra unfolded read-back moved twelve
Rogue hashes). SW-1784's likely cause: a call caches its unfolding
without recording whether gluing was on; forced unglued (`decide`,
instrumentation), a later folded read-back takes that full unfolding.

**One mechanism, two changes.** Option 4 is SW-1782's fix, extended from
the gluing bit to transparency and erasure. This ticket needs it, because
a glued `ty_value` is the first glued value that lives for a whole
session and can be forced in every mode. SW-1782 doesn't need this
ticket. So: SW-1782 first, with option 4 in full (all three modes, not
only gluing), then this ticket's steps 2 and 3. They could be one lane,
but SW-1782 has its own confirmation (the Rogue hashes) and is useful
without this, so two lanes in order are easier to review.

## 7. Decisions for Matt

- **D2568: reopen D2448?** It parked glued-closed-types.md (option C,
  document the cost) until a real proof hit the problem. 2024 day 22 does:
  5.5 s of kernel time in two theorems, 29% of aoc's kernel time in
  SW-1779's run. *Rec: yes.*
- **D2569: the direction.** The kernel evaluates a definition's statement
  afresh, glued, in each check and never reads a kept value; the kept
  `Def::ty_value` becomes glued, for the elaborator, programs and tools
  (§4). The alternatives: A (the kernel also reads the kept glued value;
  less code, but its step counts depend on history), or lazy unglued
  values (doesn't fix day 22). *Rec: §4, options 3 and 4.*
- **D2570: cached unfoldings record their modes** (gluing, transparency
  set, erasure; a glued-made unfolding readable unglued, not the reverse),
  built as SW-1782's fix and required before `ty_value` turns glued.
  *Rec: yes, SW-1782 first, then this ticket's implementation.*

Decided here, as implementation details: no memo of evaluated types within
a check (the probe didn't need one; add it only if the bench says so), and
a mismatched-mode reader overwrites the cell rather than keeping several.
