# Using unfinished proofs: checking what relies on an open goal

**Status:** proposed, 11 November 2026 (SW-2797). Decisions D-a to D-d
are open, [at the end](#decisions-for-matt). Direction from Matt, D3502:
"it would be good to allow unchecked stuff to be used in a larger proof
... it's okay to have holes or, you know, sorrys mixed in, as long as it's
clear that those issues exist when we're reporting to the user."

Builds on [lsp-goal-holes.md](lsp-goal-holes.md) (D636: a declaration
with a `?` is unfinished, and so is anything that uses it) and on
`check: open-goals: warn` (SW-2762, D3489, D3494) and `test` under it
(SW-2793, D3500).

Labels: **[checked]** read in the source at `9d5f9b001`; **[run]** run
with the main checkout's release CLI on a scratch project; **[cited]** a
web source, linked; **[recalled]** from memory of the system, not
re-checked today; **[inferred]** follows from what I read.

## 1. The short version

- **The problem.** In the Software Foundations port, the worked proof
  `plusRearrange` uses the reader's exercise `addComm := ?`. Today the
  kernel never checks `plusRearrange`, and nothing says so: `check`
  reports only the `?` itself. So the book's own proofs aren't checked
  until the reader has done the exercises they cite, and nobody is told.
- **The change.** Each `?` becomes an **assumption** the kernel knows: a
  named constant with the goal's type and no body, one per `?`. The
  declaration with the `?`, and everything that uses it, is then checked
  by the kernel as usual, *assuming the goal holds*. Every tool reads the
  assumptions off the checked terms, the way `stitchwort axioms` finds
  `Quot.sound`, and says what relies on which open goal: `check`'s summary,
  `audit` (still fails them, now naming the goals), `axioms`, a listing
  command, and the editor.
- **What it should do.** In `sf/`, `plusRearrange` and every other worked
  proof that cites an exercise becomes kernel-checked today, with a line
  saying it relies on `addComm`'s goal; a mistake in it is an error now
  rather than when the exercise is done. Nothing changes for a project with
  no `?`, and nothing that relies on a goal ever counts as finished:
  `audit` fails it, `run` and `build` refuse it, `check` under the default
  `fail` still exits 1.

## 2. Where things stand today

Measured on a scratch project with `check: open-goals: warn` [run]:

```
theorem addComm (n m: Nat): n + m = m + n := ?

theorem rearrange (n m p q: Nat): (n + m) + (p + q) = (m + n) + (p + q) :=
  rewrite addComm n m in rfl

def half (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ k => ?

theorem halfZero: half 0 = 0 := rfl
```

- `check` prints the two goals and `2 goals open, allowed by
  `check: open-goals: warn`: the declarations with them, and what uses
  them, aren't checked, and `stitchwort audit` fails them`, exit 0.
  `rearrange` and `halfZero` aren't mentioned.
- **The elaborator does check users.** A wrong proof that cites `addComm`
  (`n + m = m + n + 1`, same proof) gets `E-REFL` with a counterexample
  [run]. What's skipped is the kernel's re-check: a component whose only
  errors are `E-UNFINISHED` is `Status::Unfinished` and never admitted
  (`crates/elab/src/module.rs:446-462`), its names go into
  `Globals::unfinished`, and the kernel's `E-FAILED-DEPENDENCY` on a user
  becomes `E-UNFINISHED`, silently (`crates/elab/src/goals.rs:475`)
  [checked].
- `audit` fails all three theorems with the same message, `unfinished:
  it, or something it uses, has an open goal (`?`), so it isn't checked`
  (`crates/driver/src/audit.rs:205-221`) [run, checked]: it doesn't say
  which goal.
- `halfZero` is true whatever `half`'s `Succ` branch becomes, and `rfl`
  proves it, but it is "unfinished" too.
- `axioms Demo.rearrange` refuses: "isn't finished" [run].
- A namespace with a goal, or with a declaration using an unfinished one,
  is never written to the check cache (`crates/elab/src/cache/mod.rs:697-704`)
  [checked].

So the gaps are: (1) users of an open goal aren't checked by the kernel,
which is what "checked" means in Stitchwort; (2) nothing says which
declarations are affected; (3) `audit` doesn't say which goal.

## 3. How others do it

| System | What the hole becomes | What you can check | How you're told |
|---|---|---|---|
| Lean 4 `sorry` | the axiom `sorryAx`, at the hole | everything: the declaration and its users go through the kernel | warning "declaration uses 'sorry'" on each declaration *containing* one; `#print axioms` lists `sorryAx` for anything that relies on one |
| Rocq `Admitted`, `admit` | the whole statement becomes an axiom (`Admitted`); `admit` gives a goal up, and `Qed` then refuses | users of the statement; the admitted proof's own finished part isn't kept | `Print Assumptions` lists the admitted lemma |
| Agda holes, `postulate` | an unsolved meta; `postulate` is a declared axiom | a module with holes checks; importing it is an error ("unsolved metas in an imported module"); `--safe` refuses `postulate` | the holes in the editor; the import error |
| Isabelle `sorry` | the oracle `skip_proof`, only allowed in `quick_and_dirty` mode | everything | each theorem records the oracles it depends on |
| Idris 2 `?name` | a global name with the hole's type | everything, and the program runs | `:metavars` lists holes; running into one is a runtime error |

Details:

- **Lean.** `sorry` elaborates to `sorryAx`, an axiom of any type. Since
  4.16 (#5757) elaborator `sorry`s are *unique* and *labelled*: each is
  `sorryAx` applied to its own tag carrying its source position, so two
  `sorry`s aren't definitionally equal (`(sorry : Nat) = sorry := rfl`
  fails), and go to definition on a `sorry` in the infoview jumps to where
  it was written [cited: [v4.16.0 release notes](https://lean-lang.org/doc/reference/stable/releases/v4.16.0/),
  [Lean.Meta.Sorry](https://lean-lang.org/doc/api/Lean/Meta/Sorry.html)].
  The warning is on the declaration that *contains* the `sorry`; a user of
  a sorried lemma gets no warning, and is found only by `#print axioms`
  [recalled]. That is the weak point this note tries not to copy.
- **Rocq.** `Admitted` ends a proof by turning the statement into an
  axiom; `admit`/`give_up` leaves a goal given up, and `Qed` then fails
  with "No more goals, but there are some goals you gave up" if it
  appears in the proof term [cited: [proof mode](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/proof-mode.html)].
  `Print Assumptions` lists the axioms, admitted lemmas included, that a
  constant depends on [recalled]. Granularity is the declaration, not the
  hole.
- **Agda.** Holes check, but a module with unsolved metas can't be
  imported ("There were unsolved metas in an imported module")
  [cited: [Agda test output](https://www.cse.chalmers.se/~ulfn/darcs/Agda2/test/fail/errors/UnsolvedMetasInImport.err)].
  `--safe` refuses `postulate` and unsolved metas, transitively
  [cited: [Safe Agda](https://agda.readthedocs.io/en/stable/language/safe-agda.html)].
  So top-down work across modules needs `postulate`, by hand.
- **Isabelle.** `sorry` closes a goal through the `skip_proof` oracle,
  allowed only with `quick_and_dirty`; the theorem's derivation records
  the oracle, which tools can query [cited: [skip_proof.ML](https://isabelle.in.tum.de/repos/isabelle/file/9fb7661651ad/src/Pure/skip_proof.ML),
  [Zulip](https://isabelle-prover.github.io/zulip-archive/stream/202961-General/topic/.E2.9C.94.20.60quick_and_dirty.60.20mode.20skips.20regular.20proofs.html)].
- **Idris 2.** A hole `?name` is a name with a type; the program type
  checks and runs, and evaluating the hole fails at run time
  [cited: [Idris 2 tutorial](https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html); the message's exact text unverified].

**The pattern.** The systems that let you build on a gap all make the gap
a constant the kernel knows (an axiom, an oracle), and find what relies on
it by looking at the terms. None tells you clearly, by default, which
*users* rely on a gap; that's the part Matt asked for.

## 4. Options

End state only (D2303). Each is judged on: what the kernel sees; soundness
(nothing finished may silently depend on an open goal); the commands; the
caches; the editor; the setting.

### A. Each `?` is an assumption (recommended)

**What the kernel sees.** Before a component with goals is admitted, each
`?` becomes a new kernel **assumption**: a constant with a type and no
body, final at once, that never unfolds. Its type is the goal closed over
the hole's context: for `?` in `addComm` with `n m: Nat` in scope, the
assumption `addComm.?1: (n m: Nat) -> n + m = m + n`, and the `?` itself
becomes `addComm.?1 n m`. Then `addComm` is an ordinary declaration, checked
by the kernel, with that term as its body. `rearrange` is checked against
`addComm` as usual. `half` computes on `Zero`, so `halfZero` is checked by
`rfl` and relies on `half.?1` only because it mentions `half`.

**Soundness.** An assumption may be false (the reader stated the exercise
wrongly, or it's `Void`). What makes this safe is not that the assumptions
are true, but that nothing relying on one is ever called finished:

1. The dependency is *in the checked term*. "Relies on an open goal" is
   reachability, over checked types and bodies, of an assumption, found by
   the same walk as `stitchwort axioms` (`crates/driver/src/axioms.rs:213`),
   not by the elaborator's bookkeeping, which today is the only thing
   marking users.
2. An assumption's hash covers its type and its identity (the owner's name
   and the hole's number in it). So every user's hash covers it too: when
   the `?` is filled, every user's hash changes, and no cache entry, test
   result or `audit` verdict made under the assumption is reused.
3. Every command that answers "is this finished?" answers from (1):
   `audit` fails it, `run`/`build`/`eval` refuse it, `test` skips it.

A kernel-checked proof that relies on an assumption is still a real
result: it holds for *every* way of filling the hole with a term of the
goal's type. The kernel treats the assumption as an opaque constant, so a
proof can't depend on what it unfolds to.

**Where a `?` can't become an assumption.** Its type must mention only
final declarations (`crates/core` refuses a pending reference in a
signature, docs/core.md "Groups of definitions"). So:

- a `?` whose goal mentions a member of its own group (rare: a proof
  inside a recursive function about that function), and
- a `?` in a signature (`def f: ? := 3`), whose type isn't known,

fall back to today's behaviour: the component isn't admitted. Its users
are then **not checked**, and are reported as such (§5), never silently.

**Blocked users.** Under A, a user that needs to *compute through* a hole
fails: with `nandb := ?` still open, a reader who writes `rfl` for `testNandb1: nandb True False = True` gets
`E-REFL`, since `nandb.?1 True False` is stuck. That isn't an error the
reader made; it's "can't be checked until `nandb` is written". The
elaborator already has the hook: today it turns a fallout of a stuck
unfinished definition into `E-UNFINISHED` (`blame_failed_dependency`,
lsp-goal-holes.md §8.1). Under A the same rule fires when the failing
comparison is stuck on an assumption's head. The declaration is then
**unfinished, not checked**: reported by name, with the goal it waits on.
A real mistake that happens to be stuck on a hole is reported as blocked
until the hole is filled, then as the error; that delays a message, it
never passes anything.

**Commands.** `check`, `audit`, `axioms` change as in §5. `run`, `build`,
`eval` and the REPL refuse anything that relies on an assumption, as they
refuse unfinished definitions today (D-d). `test` skips tests that rely
on one (D3500's rule, unchanged; SW-2793). If a run ever reaches an
assumption anyway, the evaluator stops with an internal error naming the
goal; it should be unreachable.

**Caches.** The check cache: stage 1 keeps today's rule (a namespace with
goals, or relying on one, isn't cached), so goals are always fresh; a
later stage can cache them (the terms are complete now) by storing the
goal diagnostics in the entry. The test cache is keyed by hash, so (2)
covers it.

**Editor.** The `?` diagnostics are unchanged. New: a mark on each
declaration that relies on a goal, and on each that is blocked (§5.5).

**Cost.** A kernel change (one new declaration form), elaborator work at
zonking (the hole's term context, which in a lifted `match` helper is the
helper's parameters, not the printed context), and the reporting. It's
the most work of the four.

### B. The unfinished declaration's statement is the assumption

The declaration with a `?` is admitted as an assumption as a whole (its
body thrown away after elaborating), Rocq's `Admitted`. Users are checked
against its statement.

- Kernel: the same new declaration form as A, used once per declaration.
- Weaker than A: a `def` with one `?` branch computes on none of them
  (`halfZero` is blocked), and the finished part of an unfinished proof
  is never kernel-checked. A `?` in a group still can't be handled
  (a group installs all or nothing).
- Simpler elaborator: no hole contexts.
- Reporting identical to A, per declaration instead of per hole.

B costs nearly the same kernel work as A and gives less, so it's only
worth it as a first step if A's elaborator part proved hard.

### C. Check users relative to the goals, with no new kernel form

Check `rearrange` as a function of the goals it relies on: the kernel
checks `(addComm: (n m: Nat) -> n + m = m + n) => body` against
`(addComm: …) -> statement`. Nothing new is trusted, and the kernel never
holds an assumption.

- But every user of a user must be abstracted too, over the union of its
  dependencies' goals, so nothing that relies on a goal is a final
  constant; definitions with a `?` can't compute at all; the terms checked
  differ from the ones that will be checked once the goal is filled; and
  the elaborator has to thread the abstraction through namespaces.
- What it buys over A is that no false assumption ever enters the
  environment. A gets the same guarantee from (1)-(3), the way `Quot.sound`
  is handled already. Not recommended.

### D. Status quo, with reporting only

Keep D636 (users not checked by the kernel), and only report them: count
and list the users in `check`, name the goals in `audit`.

- No kernel or elaborator change; the reporting is the same work as A's.
- But "relies on `addComm`" would mean "checked by the elaborator only",
  a weaker claim than anywhere else in Stitchwort, and the user can't
  tell the difference from the report. Matt's direction is to *use*
  unfinished work in larger proofs; D makes the larger proof
  second-class. Not recommended, though it's a cheap first stage of the
  reporting if A slips.

## 5. Reporting (A)

The rule: every surface that says something is checked says, in the same
breath, whether it relies on an open goal. Words: **"relies on an open
goal"** for checked-assuming, **"can't be checked until … is filled"** for
blocked. One goal is named by its declaration and place: "`addComm`'s goal
(src/Sf/Lf/Induction/Induction.sw:118:52)"; a declaration with several
says "2 goals in `half`".

Samples use the §2 project, plus `halfOne: half 1 = 0 := rfl`, which is
blocked.

### 5.1 `check`

Goals are printed as today. The summary gains one line for what relies on
them, and lists the blocked ones (they aren't checked at all, so they're
named):

```
2 goals open, allowed by `check: open-goals: warn`; `stitchwort audit` fails what relies on them
3 declarations rely on open goals, checked assuming they hold (`stitchwort goal` lists them)
1 declaration can't be checked until a goal is filled:
  Demo.halfOne  needs `half`'s goal (src/Demo/Demo.sw:11:17)
checked 1 namespace of sw2797
```

Under `fail` the same lines, with `2 goals open` and exit 1. With no
users, the second line is left out. Counts are of declarations written in
source, generated ones folded into their owner.

### 5.2 `stitchwort goal` (no `--at`): every open goal and what relies on it

```
$ stitchwort goal
2 goals open

`Demo.addComm`  src/Demo/Demo.sw:3:46
  ⊢ n + m = m + n
  relied on by: Demo.rearrange

`Demo.half`  src/Demo/Demo.sw:11:17
  ⊢ Nat
  relied on by: Demo.halfZero
  blocking: Demo.halfOne
```

`--json` gives `goals`, each with `declaration`, `file`, `line`,
`column`, `goal`, `reliedOnBy` and `blocking`, transitively closed, for
agents. This is the "uses unfinished" listing; `goal --at` stays the
single-point command (D-b).

### 5.3 `audit`

Still fails each, now naming the goals (first three, then "and N more"):

```
✗ Demo.addComm
    fail: has an open goal (src/Demo/Demo.sw:3:46)
✗ Demo.rearrange
    fail: relies on an open goal: `addComm`'s (src/Demo/Demo.sw:3:46); checked assuming it holds
✗ Demo.halfZero
    fail: relies on an open goal: `half`'s (src/Demo/Demo.sw:11:17); checked assuming it holds
✗ Demo.halfOne
    fail: can't be checked until `half`'s goal (src/Demo/Demo.sw:11:17) is filled
audited 4 theorems: 4 failed, 0 with warnings, 0 passed (3 rely on open goals, 1 not checked)
```

JSON (`version` 2): `status` is `checked`, `assuming` (kernel-checked,
relies on goals), `unfinished` (not checked: blocked, or a fallback) or
`failed`; each theorem gets `openGoals: [{declaration, file, line,
column}]`; the finding `check` stays `unfinished`. A theorem that relies
on an open goal never passes, whatever `--allowed-axioms` says: an open
goal isn't an axiom you can allow.

### 5.4 `axioms`

No longer refuses; lists open goals beside axioms:

```
$ stitchwort axioms Demo.rearrange
open goal in `Demo.addComm` (src/Demo/Demo.sw:3:46): (n m: Nat) -> n + m = m + n
```

### 5.5 The editor and playground

- The `?` keeps its Information diagnostic (its goal).
- A declaration that relies on a goal gets a **Hint** diagnostic on its
  name: "relies on an open goal: `addComm`'s (Induction.sw:118)". Hints
  show as faint dots and stay out of the Problems panel, so 77 exercises
  don't flood it; hover on the name shows the same line.
- A blocked declaration gets an **Information** diagnostic on its name:
  "can't be checked until `nandb`'s goal (Basics.sw:228) is filled". It is
  in the Problems panel, because nothing about it was checked.
- The Goals panel, in a declaration that relies on goals, starts with
  "relies on 1 open goal: `addComm`'s (Induction.sw:118)", with the place a
  link.
- The playground shows the §5.1 lines in its output.

### 5.6 `test`, `run`, `build`

- `test` (D3500, SW-2793): a skipped test names the goal it relies on:
  `skipped  "nandb tests"  relies on `nandb`'s goal (Basics.sw:228)`.
- `run`: "`main` relies on an open goal: `half`'s (src/Demo/Demo.sw:11:17),
  so it isn't run". `build`: as today, nothing is built while a goal is open.

## 6. The setting

`check: open-goals` should decide **only how open goals are reported and
the exit status**, not what is checked. Under `fail` (the default, D3494)
users are checked against the assumptions too, so a mistake in
`rearrange` is found before `addComm` is proved; the goals are errors-level
and `check` exits 1, so CI never passes a project with holes. Under `warn`
they're warnings and `check` exits 0. Reasons: more information in both;
the editor behaves the same in every project; and there's nothing to
protect by refusing to check (checking admits nothing as finished). `audit`
ignores the setting, as now. Default stays `fail` (D-c).

## 7. What changes in `docs/core.md` (stage 1, same lane, D3210)

A new section, **Assumptions (open goals)**, after "Opaque definitions":

- The form: `check::assume(name, ty, label)` declares a constant whose type
  is checked to be a type referring only to final declarations; it's
  final at once, with no body and arity 0.
- Conversion and evaluation: a neutral head, rigid (the "Rigid" list
  already says "an axiom"), compared by identity and arguments; never
  unfolds; in index unification a call of one against a constructor is
  stuck, not a conflict, as for opaque definitions.
- Hashing: tag `assume`, the label (owner's path and hole number, the one
  place a name is hashed, so two holes of the same type stay distinct, as
  Lean's unique `sorry`s), and the type.
- Running: reaching one is an internal error naming its label; extraction
  refuses a definition that reaches one.
- Trust: an assumption adds a premise, not a rule. The kernel's claim for
  a term that mentions one is "well typed given these constants", the same
  claim it makes for a term mentioning `Quot.sound`. Which declarations
  rely on assumptions is computed outside the kernel by the axioms walk;
  `stitchwort axioms` lists them.
- The check cache (when stage 5 caches them) stores and replays them like
  definitions.
- Error codes: the internal one for running into an assumption.

## 8. Stages

| Stage | Work | Model | Estimate |
|---|---|---|---|
| 1 | Kernel: assumptions (`check::assume`), hashing, conversion/eval/erase/extraction, `docs/core.md` §7; core unit tests | Opus | 90 min |
| 2 | Elaborator: each `?` becomes an assumption applied to its term context at zonk; owner and users admitted; fallbacks (group member in the goal, `?` in a signature) keep today's path; `Status` gains "checked, relies on goals"; blocked classification; `examples/goals/` snapshots re-recorded | Opus | 2 h |
| 3 | Reporting: reliance in the axioms walk; `check` summary; `stitchwort goal` listing and `--json`; `audit` statuses and JSON v2; `axioms` lists goals; `run`/`test` messages; `docs/syntax.md` Goals and audit sections, the guide, `sf/README.md` | Sonnet | 90 min |
| 4 | Editor: Hint on relying declarations, Information on blocked ones, hover, Goals panel line, playground summary | Sonnet | 60 min |
| 5 | (later) cache namespaces with goals: goal diagnostics in the entry | Sonnet | 60 min |

Order: 1, 2, then 3 and 4 in parallel. Stage 2 is the risky one: hole
contexts in lifted `match` helpers and `let`s, and the blocked rule.
Targeted tests: stage 1 `task test:one` on core's new tests; stage 2
`examples/goals/` and `examples/projects/goals/` through `examples.rs`,
the rewind differential test on goals examples, and `stitchwort check` on
`sf/` (77 goals, small); stage 3 the audit and CLI snapshot tests; stage 4
the LSP goals tests.

SW-2793 (`test` under warn) is unaffected and should land first; stage 3
only changes its message to name the goal.

## 9. Decisions for Matt

- **D-a: The end state.** A declaration with a `?`, and everything that
  uses it, is checked by the kernel *assuming* each open goal holds, one
  assumption per `?`, and is always reported as relying on that goal,
  never as finished. [rec: yes (option A). It does what D3502 asks with
  the kernel's full check, like Lean's `sorry`, plus reporting Lean
  lacks.]
- **D-b: What's reported, and the words.** `check` adds one line counting
  what relies on open goals and names what can't be checked yet;
  `stitchwort goal` with no `--at` lists every goal and what relies on it;
  `audit` names the goals; the editor puts a faint hint on each relying
  declaration. Words: "relies on an open goal", "can't be checked until
  … is filled". [rec: yes, as in §5.]
- **D-c: The setting.** `open-goals: fail` and `warn` check exactly the
  same things; the setting only decides warning or error and the exit
  status. Default stays `fail`. [rec: yes: checking admits nothing as
  finished, so there's nothing to protect by refusing.]
- **D-d: Running.** `run`, `build` and `test` still don't run anything that
  relies on an open goal, even one whose goals are only proofs. [rec: yes:
  proofs are erased when running, and a false one (a wrong equation) can
  make the erased program take a branch it "can't" or treat a value as
  the wrong type; revisit if a real program needs it.]

## 10. Calls made (implementation, not Matt's)

- One assumption per `?`, not one polymorphic `sorry` axiom: no universe
  polymorphism needed, each goal named in reports, and two holes never
  equal (Lean moved to unique sorries for this reason).
- The assumption's type closes over the hole's whole term context, with
  `let` values substituted, so its type matches the goal shown.
- Hash label = owner's path and the hole's number in source order, not its
  line: editing above a hole doesn't change hashes.
- Reliance is computed outside the kernel, in the axioms walk
  (`crates/driver/src/axioms.rs`), recomputed on load; the kernel only
  needs the new form.
- Blocked = the failing comparison is stuck on an assumption's head, as
  `blame_failed_dependency` does today for unfinished definitions.
- Stage 1-4 keep today's check-cache rule (no entry for a namespace with
  or relying on goals); stage 5 lifts it.
- `audit --json` goes to version 2 (new status value, new field).
- `stitchwort search` offers lemmas that rely on goals, marked "relies on
  an open goal", since stating a lemma and using it before proving it is
  the workflow this enables; today it leaves them out.
- No user-level `axiom` keyword: the kernel form could carry one, but
  that's a separate question.

## 11. Risks and not known yet

- **Hole contexts.** A `?` inside a lifted helper (`f.%match1`) or a
  `decreasing` obligation has a term context unlike the printed one; the
  assumption must use the term's. Stage 2's main risk [inferred].
- **How many `sf/` and `aoc/` goals fall back** (goal mentioning a group
  member): not measured; expected rare. Stage 2 should count them on `sf/`.
- **Blocked classification** may be too broad or narrow at first; a miss
  either way is a wrong *message*, never a pass.
- **Kernel time**: checking what was skipped costs time in projects with
  goals; for `sf/` the whole project checks in seconds today [recalled],
  so expected negligible.

## 12. Tickets to file

Proposed, not filed:

1. Stage 1 — kernel assumptions + `docs/core.md` (Opus, 90 min).
2. Stage 2 — `?` as assumptions in the elaborator; users kernel-checked;
   blocked rule (Opus, 2 h). After 1.
3. Stage 3 — reporting: `check`, `goal`, `audit` v2, `axioms`, messages,
   docs, `sf/README.md` (Sonnet, 90 min). After 2.
4. Stage 4 — editor marks and Goals panel (Sonnet, 60 min). After 2.
5. Stage 5 — check cache for namespaces with goals (Sonnet, 60 min).
   Later, backlog.
