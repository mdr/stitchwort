# Keeping calls folded in a theorem's closed statement

**Status:** parked, 6 November 2026 (D2448, Matt: option C for now;
"definitely record any research we've done so far so we can pick it up
again"). Ticket SW-1534 (from SW-1525); revisit ticket SW-1596. The
documented workaround is in the proving guide, §6. Read
[§6](#6-why-parked-and-what-to-do-on-revisiting) before picking it up.
Related: [folded-calls.md](folded-calls.md) (glued calls, D483; "As built
(stage 4)" is where the rule this note revisits was set),
[opaque-definitions.md](opaque-definitions.md) (the transparency set).

## 1. The problem

```
def countdown (acc: Nat): Nat → Nat
  | 0 => acc
  | Succ k => countdown (acc + 1) k

theorem t: countdown 0 100000000 = countdown 0 100000000 := rfl
```

`stitchwort check` on this runs for minutes (it is killed by a 60 s timeout
here). Both sides are the same term, so `rfl` needs no computation at all,
and nothing in the proof looks at the value. With `N` = 1,000,000 the check
takes 1.2 s against 0.16 s for `N` = 1,000; the time is linear in `N`.

It isn't a hang in the strict sense: the check's step budget
(`Limits::work`, 10,000,000,000) would end it with E-RESOURCE eventually.
But a statement that only *mentions* a big computation shouldn't cost
that computation.

## 2. Where the time goes

All of it is in the kernel, in `check.rs` `push_def`, called from
`declare_def` (the theorem's signature, before its body):

```rust
let ty_value = eval(&g.ev(), &[], &ty)?;
```

The kernel runs with gluing off (`in_kernel_modes`), so evaluating the
statement unfolds `countdown 0 100000000` as soon as it is built: the
whole loop runs, in `value::run` and the natives' big-number additions
(`sample` on a release build: 2,145 of 2,145 samples under `push_def` →
`eval`). The elaborator isn't involved: it glues, so its copy of the
statement keeps the calls folded.

This is deliberate. folded-calls.md, "As built (stage 4)", says a type's
value, which is kept (`Def::ty_value`), "is still made unglued, so nothing
glued outlives the check", and that a closed type (`theorem t: f 5 = f 5`)
therefore "gains nothing" from the kernel's call-by-arguments rule.
Evaluating it a second time, glued, for the body was tried and dropped
because it cost a second evaluation of every closed type (`check-list-rfl`
+11% steps).

A statement with parameters (`theorem t (m: Nat): countdown 0 N = ...`)
doesn't have the problem: its value is a function type whose codomain is a
closure, evaluated only while the body is checked, glued. Nor does
SW-1525's `Big (countdown 0 N)` with `Big` a definition: the call is an
argument of a call that stays a neutral `Big ...` until forced.

## 3. Options

**A. Make `Def::ty_value` glued** (`push_def` and `retype_def` evaluate
with gluing on). The statement's calls stay calls; anything that looks
inside one forces it, as everywhere else. `rfl` then compares two calls of
`countdown` with the same arguments and answers "equal" at once (the rule
D483 added to `conv`). No second evaluation, so no `check-list-rfl` cost.

What it gives up is the invariant "nothing glued outlives the check". A
glued call's unfolding is computed once and shared by every copy
(`Unfolding`), and today that cache is only reused across metavariable
epochs with a check (`Unfolding::get`). A call kept in `ty_value` would be
forced from many places over a session, in different modes:

- *Transparency.* Forced while some definition's body is checked with an
  opaque definition visible (`unfolding X`), the cached unfolding may have
  seen `X`'s body; forced later with `X` hidden, the cache would hand back
  that unfolding. That isn't a logical unsoundness (an opaque definition is
  still a definition), but it breaks D2294: what the kernel accepts would
  depend on what was checked before.
- *Erasure.* Forced while a program runs (rt's `telescope` reads
  `ty_value`), the unfolding could be computed with proofs erased and then
  reused by the kernel.

So A needs `Unfolding` to record the modes it was computed in (the
transparency set, by `Rc` identity or contents, and whether erasure was
active) beside the epoch, and to reuse a cached unfolding only in the same
modes. That is about 15 lines in `value.rs`, trusted code.

There will also be visible changes beyond speed: anything that reads back
`ty_value` folded (`quote_folded`, `show`) would now print `countdown 0 N`
where it printed the value, and kernel-quoted statements may hash
differently (snapshots and cache keys move once).

Measured, as an uncommitted experiment (gluing on in `push_def`, and the
closed type evaluated glued again in `admit_group`; no `Unfolding` change):
the repro checks in 0.17 s at `N` = 100,000,000 (from over 60 s), 1,000,000
in 0.17 s (from 1.2 s); `task test:lane AREA=core` (175 tests) and `AREA=elab`
(156) pass. With A, the second change isn't needed: `def_type` hands the
body check the glued `ty_value`.

**B. Evaluate `ty_value` lazily, and a closed type glued for its body.**
`Def::ty_value` becomes a `OnceCell`, filled on first use, still unglued;
`admit_group` evaluates a closed type glued for the body check, and that
value is dropped afterwards, as a parameterised type's codomain already is.
The invariant is kept and there is no second evaluation (the unglued one
happens only if something uses `ty_value`). But anything that refers to the
theorem (`theorem u: ... := t`) forces the unglued value and pays the whole
computation again, so the problem moves rather than goes away. And
`ty_value()` is read in about 25 files across the crates, so making it
fallible is a wide, mechanical change.

**C. Leave the kernel as it is**, and document that a statement's closed
calls are computed when it is declared: write the theorem with a parameter,
or name the big value with a definition. Nothing changes in trusted code.

The brief's other suggestion, an identical-terms short-circuit in `conv`,
doesn't help: the time is spent before any comparison, in evaluating the
statement.

**Recommendation: A**, with the `Unfolding` modes check. It removes the
cost everywhere the statement goes (its body, every proof that cites it),
it reuses the comparison rule the kernel already has, and the mode check
makes the cache's reuse as strict as its epoch check is now. B is the
conservative fallback.

## 4. Evidence still to collect

Before building A: the bench baseline (`check-list-rfl` and the others,
steps should fall or stay), the `conv_shortcut` sweep (gluing more in the
kernel means the shortcuts are exercised more), the hash snapshots, and a
kernel test that forces a glued `ty_value` call under one transparency set
and then under the empty one, which must not see the opaque body.

## 5. Decisions

- **Q1.** Make the kernel's kept type values glued, with the unfolding
  cache keyed by the modes it was computed in (option A)? [rec: yes]
- **Q2.** If not A, which: B (lazy, closed types glued for the body only)
  or C (document the cost)? [rec: B]

## 6. Why parked, and what to do on revisiting

**Decided (D2448, Matt, 6 Nov 2026):** C for now: the kernel is unchanged
and the cost is documented (proving guide §6, "A statement with no
parameters is computed when it is declared"). A stays the preferred fix
when this is picked up.

**Why it's low priority.** No real proof has hit it. The incident behind
SW-1525 (2020 day 15, theorems naming turn 30,000,000) was the audit's
counterexample search reading the statement back, not the kernel: those
theorems had a parameter (the starting numbers), so they checked at once.
SW-1525 capped that read-back at 5M steps. The kernel case needs a
statement with no parameters at all that spells out a computation of
millions of steps; it was found only by the constructed repro in §1.
AoC theorems are stated for any input, so they have parameters.

**What exists.**
- The experiment for A: `dev/patches/sw-1534-glued-closed-types.patch`
  (gluing on in `push_def`, closed types glued again in `admit_group`; no
  `Unfolding` mode check yet). Measured in §3: N = 100,000,000 from over
  60 s to 0.17 s; core (175) and elab (156) lanes passed.
- The evidence list in §4, still to collect.

**Gap: prior art not checked for this question.** folded-calls.md §3
compares Lean 4, Agda, Rocq, Idris 2 and smalltt on gluing in general, but
not on what this decision turns on: how each kernel records a closed
statement, and whether a cache of unfoldings ever crosses settings
(transparency, erasure). Unverified beliefs, from memory, to check against
sources before deciding:
- Lean 4's kernel keeps statements as terms; declaring a theorem only
  infers that its type is a sort (to weak head), so `countdown 0 N` isn't
  run, and `rfl` on identical terms is settled by comparing them. Its
  kernel caches (whnf, defeq) live in one type-checker run and are dropped
  after the declaration.
- Agda and Rocq likewise work on terms and unfold on demand.
- Idris 2 glues (`Glued`: a term with its lazily computed normal form);
  how long its normal forms live hasn't been looked at.

If the Lean point holds, it suggests a variant between A and B: glue the
statement, but scope remembered unfoldings to one check (as Lean's caches
are), which keeps folded-calls.md's invariant "nothing glued outlives the
check" without B's cost of every citing theorem recomputing. First step on
revisiting: an Opus lane adds a verified prior-art section here (sources
for each claim) and says whether it changes the recommendation.
