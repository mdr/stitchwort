# Checking and running tests when a project has errors or open goals

**Status:** proposed, 11 November 2026 (SW-2938), for Matt's decisions,
listed [at the end](#10-decisions-for-matt). D-a (D3524), D-b (D3527) and D-c (D3525) accepted; stage 1
built (SW-2940), stage 2 built (SW-2943: reporting; instance search's part of §4.2's implicit uses is SW-2970's), stage 3 built (SW-2952, SW-2980 for bodies that don't parse): importers are checked, against stand-ins,
and `E-USES-FAILED` replaces `E-NAMESPACE-FAILED` everywhere, the editor's
live project included (SW-2997, §6). It answers D3524 (what
happens to a namespace that imports a broken one) and puts today's
one-at-a-time decisions under one model: SW-2805/2806 (each `?` is an
assumption), SW-2855 (what waits on a goal), SW-2909 (a test that reaches
a `?` fails) and SW-2932 (D3523: tests run despite errors elsewhere).

Builds on [using-unfinished-proofs.md](using-unfinished-proofs.md) and
`docs/core.md` "Assumptions (open goals)". End state only: migration cost
isn't counted (D2303).

Labels: **[run]** run today with a release binary on a scratch project
(main's at `49dbcb4e5`, or the SW-2932 lane's where it says so);
**[checked]** read in the source or docs; **[cited]** a web source,
linked; **[recalled]** from memory, not re-checked; **[inferred]** follows
from what I read.

## 1. The short version

- **The problem.** Slip a bug into `beats` in the book's chapter 1 and two
  theorems go red. On `main`, no test runs at all. With SW-2932, chapter
  1's tests run, but chapter 2 is skipped whole
  (`E-NAMESPACE-FAILED`): its five exercise goals disappear from the
  output and its declarations aren't checked, though it imports only
  `Move`, `beats`, `Outcome`, `play` and `otherSide`, none of which has an
  error [run]. And the rules disagree with each other: a test that cites a
  theorem whose proof is `?` runs (SW-2909), one that cites a theorem
  whose proof has an error fails without running (SW-2932); a namespace
  with open goals doesn't stop its importers, one with an error stops all
  of them [run].
- **The change.** One model. Status belongs to a **declaration**, never to
  a namespace: a namespace is only where declarations live. There are two
  kinds of **gap**, an open goal (`?`) and an error, and a declaration
  either *has* a gap, *relies on* one (checked by the kernel assuming it),
  or *waits for* one (can't be checked until it's fixed). An importer is
  checked like any other code: each name it imports comes with its status.
  A declaration with an error whose statement checked is stood in for by
  an assumption of that statement, exactly as a `?` is, so what uses it is
  still checked. A test runs unless the code it runs needs a gap.
- **What it should do.** In the book, with the slip: the two false
  theorems are red, chapter 1's seven tests run (two fail, on their
  merits), and chapter 2 is checked in full, with its goals shown
  [estimated from the imports]. Nothing with a gap, or relying on one, is
  ever reported as finished: `check` exits 1 whenever any declaration has
  an error, `audit` fails everything that has, relies on or waits for a
  gap, and the check cache stores none of it.

## 2. Today's behaviour

Scratch project: `A` has `double` (fine), `broken (n: Nat): Nat := True`
(a type error), `twice` (calls `broken`), `later := ?`, a false theorem
`doubleTwo: double 2 = 5 := rfl`, and tests; `B` imports only `A.double`
and has a definition, a true theorem and a test; `C` imports nothing.

| | `main` [run] | SW-2932 lane [run] |
|---|---|---|
| `check` | the two errors and two goals in `A`; `E-NAMESPACE-FAILED` for `B`; exit 1 | same |
| `test`, `A`'s tests | none run: only the diagnostics, exit 1 | "double works" passes; "uses broken" fails ``it uses `broken`, which has an error (src/a.sw:5:29)``; "uses twice" fails ``it uses `twice`, which depends on `broken`, which has an error (…)``; "reaches later" fails ``` `later` isn't written yet: its body is `?` (…)``` |
| a test passing `doubleTwo` as a proof argument | not run | fails: ``it uses `doubleTwo`, which has an error (…)`` |
| `B`'s test (uses only `double`) | not run | not run: `B` is skipped |
| `C`'s test | not run | passes |
| `audit` | prints the diagnostics, no verdicts, exit 1 | same [inferred] |

The same project with the errors removed and only the two `?`s left, under
`check: open-goals: warn` [run, main]: `B` **is** checked, its test runs
and `audit` passes `B.quadOne`; a test that passes `doubleComm` (proof
`?`) as a proof argument runs and passes; the test that calls `later`
fails. So today an open goal is per declaration across namespaces, and an
error is per namespace.

The book, with `Paper, Rock => True` changed to `Paper, Scissors => True`
[run]: on `main`, two `E-REFL` errors, `E-NAMESPACE-FAILED` for
`Book.Cases`, no test results. On the SW-2932 lane: the same three
errors, then 8 tests, 6 passed and 2 failed ("paper wraps rock", "rock
against paper loses"); the goal count falls from 11 to 6, because chapter
2's exercises are no longer reported.

How it works today [checked]:

- A namespace is checked whole, after those it uses.
  `check_project_namespace` (`crates/driver/src/project.rs:358`) returns
  one `E-NAMESPACE-FAILED` and `Skipped` if any namespace it uses is
  `Failed` or `Skipped`. `Failed` means "some diagnostic is an error".
- Inside a namespace the unit is already the declaration: a failed one is
  `Global::Failed`; a reference to it is `E-FAILED-DEPENDENCY`, which
  isn't reported when the original error is (`module.rs:635-642`); the
  kernel refuses anything that refers to a failed declaration (`docs/core.md`,
  "Admission": "nothing built on it is ever accepted"). The reference
  itself is the elaboration error (`check.rs:2400`), so the user is never
  checked as a whole and its own mistakes can stay hidden until the
  dependency is fixed [inferred].
- An open goal is an assumption (`check::assume`), its users are
  kernel-checked, and `assumption::relied_on` reads reliance off the
  checked terms.
- `test_run.rs`: a test relying on goals fails unless every goal it relies
  on erases (a proof or a type), in which case it runs.
- A namespace with errors, with goals, or relying on goals is never in
  the check cache.

## 3. The model

### 3.1 Statuses

A declaration has a **statement** (its signature; for a type, its header)
and a **body**. Its status is one of six, from two kinds of gap and three
relations to one:

| Status | Meaning | In the kernel | Words |
|---|---|---|---|
| **checked** | accepted; reaches no gap | final | (nothing) |
| **has an open goal** | its body has a `?` | final; each `?` an assumption | "has an open goal" |
| **has an error** | its statement or body was refused | failed; if the statement checked, a **stand-in**: an assumption of the statement (§3.3) | "has an error" |
| **relies on** a gap | checked assuming a goal, or a stand-in's statement | final; reaches an assumption | "relies on `addComm`'s goal" / "relies on `beats`, which has an error" |
| **waits for** a gap | can't be checked until it's fixed: it must compute through the gap, or the gap has no stand-in | not admitted | "can't be checked until `half`'s goal is filled" / "… until `beats` is fixed" |

(Five rows; "relies on" and "waits for" each come in a goal and an error
flavour, which only changes the words.) "Depends on a failed declaration"
isn't a separate status: such a declaration either relies on the stand-in
or waits.

A declaration can have several at once (an error of its own and a
reliance); it's reported by the worst: has an error, waits, has a goal,
relies on.

### 3.2 How status travels

- **Any reference carries it, for checking.** If `g` refers to `f`
  anywhere (signature, body, a proof argument, an `unfolding` list), `g`
  relies on or waits for whatever `f` has, relies on or waits for. This is
  reachability over checked terms, the walk `stitchwort axioms` does; the
  elaborator's bookkeeping only supplies "waits", for what never reached
  the kernel.
- **Statement or body.** A gap in a *body* leaves the statement usable, so
  users are checked against it (they rely). A gap in a *statement* (a `?`
  or an error in a signature; any error in a `type`, `interface` or
  `ability`) leaves nothing to check against, so users wait.
- **Needing the body.** A user that has to compute through a gap (`rfl` on
  `half 1` while that arm is `?`; `rfl` on `beats Rock Paper` while
  `beats` has an error) waits. This is SW-2855's rule, unchanged, applied
  to both kinds.
- **Imports carry nothing extra.** `import A (double)` brings `double` with
  its status. That `A.broken` has an error matters to `B` only if `B`
  refers to something that relies on or waits for `broken`. A namespace
  "has errors" only as a count in a summary.
- **Running is narrower than checking.** A run (a test, `run`) is stopped
  only by a gap its *code* needs: one whose type is data. A gap that is a
  proof or a type is erased when the program runs, so it doesn't stop the
  run; the result says the run assumed it (§4.2).

### 3.3 The stand-in: an error is an assumption too

When a `def` or `theorem` fails with its statement checked, the elaborator
declares an assumption with that statement, as it does for a `?`: for
`theorem doubleTwo: double 2 = 5 := rfl`, an assumption `double 2 = 5`
labelled "`doubleTwo`, error". The name `doubleTwo` resolves to it. This
is option B of using-unfinished-proofs.md (Rocq's `Admitted`), used where
option A (one assumption per `?`) has nothing finer to offer, because a
body with an error has no well-typed remainder.

- **What the kernel needs:** nothing new in kind. `check::assume` exists
  [checked]; its label gains a kind (goal number or "error"), hashed, so a
  stand-in and a goal of the same type differ and every user's hash
  changes when the error is fixed. `docs/core.md` gets a paragraph (D3210).
- **Why it's sound:** the argument in `docs/core.md`, "Why it's sound",
  word for word. A stand-in adds a premise, not a rule; it never unfolds;
  a term that mentions it is well typed in the environment extended by a
  constant of that type; and nothing that reaches one is reported as
  finished, because that is read off the checked terms by `relied_on`,
  not off the elaborator's records. A stand-in is *more* likely to be
  false than a goal (the checker may have just shown the statement false),
  which is why §5's rule is "never finished, never exit 0", not "probably
  fine".
- **What doesn't get one:** a declaration whose statement didn't check; a
  `type`, `interface`, `ability` or instance with an error (later work
  could give an instance with a checked head one); a member of a failed
  group whose signature mentions another member, nor a member of a failed
  group with no error of its own (the group fails together, so its body
  isn't trusted alone; its users wait for the member with the error, which
  is the one named). Their users wait. A stand-in for a theorem is a
  theorem to the kernel, so nothing takes a proof for something that
  computes.
- **Syntax errors.** A declaration whose body didn't parse but whose
  signature did (parse-recovery.md) gets a stand-in the same way. So
  typing inside `beats`' body no longer takes down everything that calls
  `beats`: callers stay checked against its signature. Parse recovery
  keeps a `def` or `theorem` whose header parsed and whose body (anything
  after its `:=` or first `|`) didn't, as its signature with the place of
  the syntax error and no equations; the elaborator checks the statement
  and fails the declaration there without a second message, so it stands
  in, or its users wait, by the rules above (SW-2980). A declaration whose
  header didn't parse, and an instance, are left out as before: their
  names are known only as failed, and their users wait, counted as
  waiting, not as errors.

This is what makes the two rules of §1 one rule: a broken theorem and an
unfinished theorem are the same thing to their users, an assumption of the
statement.

## 4. What each command does

### 4.1 What is checked

Every declaration of every namespace is checked, in dependency order,
whatever happened before it. `E-NAMESPACE-FAILED` goes away; a namespace
is skipped only where it can't be placed in the order at all
(`E-NAMESPACE-CYCLE`).

| Declaration | Elaborated | Kernel | Its users |
|---|---|---|---|
| checked | yes | accepted | checked |
| has an open goal | yes | accepted, with assumptions | checked: rely, or wait if they compute through it |
| has an error, statement checked | yes; the error is reported once, there | stand-in accepted | checked: rely, or wait |
| has an error, statement failed | yes; reported once | failed | wait |
| relies on a gap | yes: its own mistakes are errors now | accepted | checked: rely |
| waits for a gap | as far as the gap | not admitted | wait |

### 4.2 Not cascading

An error is reported once, where it is. For what uses it:

- **Relies on:** no diagnostic in `check`'s output; counted in the
  summary; a faint Hint on the name in the editor (as using-unfinished-proofs.md
  §5.5 does for goals).
- **Waits:** never a fresh error (no `E-REFL` saying `beats Rock Paper`
  is stuck, no "unknown name"). In the same file as the gap: nothing more,
  as today. In another file: **one** diagnostic per broken name per file,
  on its import (or its first qualified use), listing what waits:

  ```
  [E-USES-FAILED] Error: `broken` has an error, so 2 declarations here can't be checked
     ╭─[ src/b.sw:3:11 ]
   3 │ import A (double, broken)
     │                   ───┬──
     │                      ╰── `broken` has an error (src/a.sw:5:29)
     │ Note: waiting for it: `quadBroken`, test "quad of broken"
  ```

- **Implicit uses.** Instance search, `auto`'s decision procedures and
  dot-method lookup can fail *because* a candidate has an error. When the
  search fails and a failed candidate was in scope, the declaration waits
  for that candidate instead of reporting "no instance" (the elaborator
  already does this in places for `Global::Failed`: `effects.rs:1865`,
  `dot.rs:939`, `reify.rs:276` [checked]). Where that can't be told, the
  error stands, with a note: "`A`, used here, has errors; this may be a
  result of them".

  *As built (SW-2970):* instance search. An instance whose signature
  checked keeps its row in the instance table when its body fails, marked
  not valid, in its own namespace and in those that import it. A search
  that reaches that row (directly, as a prerequisite of another instance,
  or for an operator such as `<` on the instance's type) fails with
  `E-FAILED-DEPENDENCY` and notes the instance as used, so its user waits
  for it as for a named declaration with an error: nothing more in the
  same namespace, one `E-USES-FAILED` per file in another, labelled at the
  first waiting declaration (nothing imports an instance by name). A
  search that another instance answers is unaffected. An instance whose
  signature failed was never registered, so "no instance" stands there,
  without the note; `auto`'s decision procedures and dot-method lookup
  are as before.
- **A namespace with syntax errors** may be missing declarations, so an
  imported name not found in it is "`A` has a syntax error (place), so
  `beats` can't be found", once, on the import, and its users wait: not
  `E-UNKNOWN-NAME` at every use.

### 4.3 `check`

Diagnostics as above, then a summary (the goal lines exist today; the
error lines are new):

```
2 errors: in `A.broken` and `A.doubleTwo`
1 declaration relies on a declaration with an error, checked assuming its statement
2 declarations can't be checked until an error is fixed:
  A.twice              needs `broken` (src/a.sw:5:29)
  A.test "uses twice"  needs `broken` (src/a.sw:5:29)
2 goals open
1 declaration relies on open goals, checked assuming they hold (`stitchwort goal` lists them)
checked 3 namespaces of p1
```

**Exit 1 whenever any declaration has an error**, under every setting.
There is no `errors: warn`: an open goal is a gap the author declared, an
error isn't. Exit 0 needs no errors, and no goals unless `open-goals:
warn`.

### 4.4 `test`

Diagnostics and summary as `check`, then every test of every namespace
gets a result:

| The test | Result | Line |
|---|---|---|
| everything its code runs is checked | runs: passes or fails on its merits | `✓ … ran` |
| …and it relies on gaps that are proofs or types | runs, never from an old result (its hash covers the gaps) | `✓ … ran  (assuming `doubleTwo`, which has an error (…))` |
| its code needs a `?` | fails, not run (SW-2909) | ``(`later` isn't written yet: its body is `?` (…))`` |
| its code needs a declaration with an error | fails, not run (SW-2932) | ``(it uses `twice`, which depends on `broken`, which has an error (…))`` |
| it waits for a proof or statement gap | fails, not run | ``(it can't be checked until `doubleTwo` is fixed (…))`` |
| its own body has an error | fails, not run: a result, so the count of tests doesn't change as errors come and go | `(it has an error (src/a.sw:16:23))` |

"Needs" is decided before running, from what the test refers to, by the
gap's type (data stops a run, a proof or a type doesn't), as
`unfinished_message` does today for goals [checked]. So a test never
starts and then stops at a gap.

Exit 1 if any test failed or ran out of resources, if nothing matched, or
if anything checked for the run has an error. `--json`: `ok` as the exit
status, a new `errors` count beside `tests`, and per test an `assuming`
list, so an editor can tell "all passed, but the project has errors" from
"all passed".

### 4.5 `audit`

Prints its verdicts even when there are errors (today it prints only the
diagnostics [run]):

```
✓ B.quadOne
✗ A.doubleTwo
    fail: has an error (src/a.sw:11:36)
✗ A.usesTwo
    fail: relies on `doubleTwo`, which has an error (src/a.sw:11:36); checked assuming its statement
✗ A.twiceOne
    fail: can't be checked until `broken` is fixed (src/a.sw:5:29)
audited 4 theorems: 3 failed, 1 passed (2 errors in the project)
```

A theorem passes only if it is checked and reaches no assumption of either
kind, whatever `--allowed-axioms` says: a gap isn't an axiom you can
allow. `B.quadOne` passing while `A` has errors is right: the kernel
checked it against final declarations only, and `A`'s failures contribute
nothing to the environment. Exit 1 if any theorem failed **or the project
has any error**; JSON `ok: false`, statuses `checked`, `assuming`,
`waiting`, `failed`, each with its gaps and their kind.

### 4.6 `run`, `eval`, `build`

`run` and `eval` follow `test`'s rule: the diagnostics, then the program
runs if the code `main` runs needs no gap, with the warning line D3507
gave goals ("`main` relies on …"); otherwise "`main` uses `broken`, which
has an error (…), so it isn't run". `build` refuses while what it builds
has, relies on or waits for an error: an executable outlives the session
that knew about the gap.

### 4.7 The editor and the playground

- Errors where they are, as now. `E-USES-FAILED` (§4.2) replaces
  `E-NAMESPACE-FAILED` in importing files: one per broken name, pointing
  at the name, instead of one per file pointing at the namespace.
- A Hint on the name of each declaration that relies on a gap; an
  Information diagnostic on each that waits (the goals design's marks,
  for both kinds).
- Run icons and the Testing panel: every test has a result, with §4.4's
  messages. Goals, hovers and go-to-definition keep working in importers
  of a namespace with an error, which today lose them [inferred from the
  skip].
- The playground's Check tab shows §4.3's summary; its Tests tab is §4.4.

### 4.8 Exit codes

| | no gaps | goals only, `fail` | goals only, `warn` | any error |
|---|---|---|---|---|
| `check` | 0 | 1 | 0 | 1 |
| `test` | by the tests | 1 | by the tests | 1 |
| `audit` | by the theorems | 1 | 1 if any theorem has, relies on or waits for a goal | 1 |
| `run` | the program's | runs (D3507); 1 if it needs a gap | same | runs if it needs no gap, then exits 1; else 1 |
| `build` | 0 | as D3507 | as D3507 | 1, nothing built |

## 5. Namespaces that import a broken one (D3524)

| | A. Skip (today) | B. Check; failed names stay failed | C. Check; failed declarations with a checked statement are stand-ins (recommended) |
|---|---|---|---|
| What's checked in the importer | nothing | everything that doesn't refer to a failed name | also what refers to one but doesn't need its body |
| Could a chapter-2 theorem be accepted relying on a broken chapter-1 declaration? | no | no: the kernel refuses any reference to a failed declaration, as it does inside a namespace today | checked *assuming its statement*; never finished: `relied_on` finds the stand-in, `audit` fails it |
| New trust | none | none: per-declaration checking past a failure is what one namespace already does | none in kind: the open-goal argument (§3.3); one more use of `check::assume` |
| `check` / `audit` success | never, with an error | never | never |
| Cascade | one line per importing namespace; hides everything else in it | one line per broken name per file; own errors of waiting declarations hidden until the fix | same line only for what needs the body; own errors of relying declarations found now |
| Cost with an error in a widely used namespace | none: dependents skipped | dependents checked again each run, uncached (§6) | same as B |
| The book reader, after the slip | chapter 2 vanishes: no goals, no hovers, no tests | chapter 2 fully checked (it imports no failed name) | same as B here; differs when a later chapter cites a red theorem: B makes that proof wait, C checks it |

**Why not A.** It makes the size of a namespace decide what an error
costs: split a file in two and a slip in the first half hides the second.
It's also the one place where an error and an open goal behave
differently for no reason the user could give (§2).

**Why C over B.** B is C's first stage and is right as far as it goes. C
adds three things: users of a broken declaration get their own mistakes
reported now, not after the fix (Lean's behaviour inside a file); a
syntax slip in a body doesn't blank its callers (§3.3); and the test
rules unify (§4.4, §7). C's cost is the elaborator work to keep a failed
declaration's statement and declare the stand-in.

**The one risk that's new in C** is at run time, not in the logic: a test
or program that only *cites* a broken theorem runs with that proof
erased, and a broken theorem may be false. That is D3507's risk for a
false `?`, with the same defences (SW-2809: reaching an impossible
branch or a data gap stops the run and names the gap; its review left
false type-equality casts as the known silent case, named in the warning
line [checked in docs/reviews/SW-2809-running-with-goals-review.md; what
shipped not re-checked]). The result line always says what was assumed,
and the run exits 1 because the project has an error. See D-c.

## 6. Caching and the live project

- **Test results** are keyed by the test's content hash. A hash covers
  every assumption reached, label and type, so a result made while
  relying on a gap is never reused once the gap is fixed [checked,
  `docs/core.md` "Hashing"]. A test that fails without running (needs a
  gap, waits, has an error) has no hash and is never cached, as now.
- **Check cache, first stage.** Keep today's structural rule, extended by
  one word: a namespace is stored only if every declaration in it is
  checked and reaches no assumption of either kind. A namespace whose own
  declarations are all checked is stored even when a namespace it imports
  has errors (`B` above), provided replay doesn't assume its dependencies
  were replayed too; if it does, don't store it and file that.
- **Cost.** While a widely imported namespace has an error, each importer
  with a waiting declaration is checked from source on every run; today
  it's skipped for free. For the book that's nothing. For `aoc/` with an
  error in `Aoc.Common` it could be most of a cold project check per run
  [estimate; not measured: a whole-`aoc/` run is the verifier's or
  Overmind's]. Declarations that wait fail at the first reference, so the
  cost is in the ones that still check.
- **Check cache, later stage.** Store such namespaces too. An entry is
  already a function of its key (the namespace's sources, those of what
  it uses, the configuration, the compiler); it would hold the checked
  declarations as now, plus the names that waited and their diagnostics.
  Only checked definitions are replayed as trusted; a waiting name is
  replayed as failed (the replay already has that entry kind,
  `cache/mod.rs:938` [checked]). Do it if the measurement says so.
- **The editor's live project.** Today importers of a failed namespace
  keep the answers they had when last checked (parse-recovery.md §7).
  New: they are rechecked when the namespace they use changes, error or
  not, by the scheduling a clean edit already uses, so an edit that
  breaks `A` costs what an edit that keeps `A` clean costs. With
  stand-ins, a half-typed body leaves `A`'s statements, and so its
  importers' answers, unchanged; without them (stage 1) the importers'
  waiting marks would flicker while typing, so stage 1 kept "last
  answers" for an importer while the namespace it uses had a *syntax*
  error. Stage 3 removed that (SW-2997): an importer is always rechecked,
  against the stand-ins, and only a syntax error in a header (whose
  declaration has no statement) makes its users wait while it lasts, as
  in its own file. The logs of failed declarations and broken tests
  (`check`'s summary, `audit`) are cut back with each rewind, so they
  describe each namespace's latest check.

## 7. Consistency: SW-2909's rule and SW-2932's

| A test that… | SW-2909 (`?`) | SW-2932 (error) | This note |
|---|---|---|---|
| calls a function with the gap | fails | fails | fails (both) |
| only cites a theorem with the gap | runs | fails | runs, and says what it assumed (both) |
| is in a namespace that imports one with the gap | runs | not run | runs or fails by its own dependencies (both) |

SW-2932's "fails" in the second row isn't a choice it made: the test
can't be elaborated against a `Global::Failed` name, so there's nothing to
run [checked]. The stand-in removes the reason. The other consistent
choice is the strict one, D-c's alternative: a test that cites any gap,
`?` or error, doesn't run. It gives up running a day's tests while one of
its bound lemmas is being re-proved, which is the moment a developer most
wants them.

## 8. How others do it

| System | Unit that fails | What a broken thing is to its users | Running with errors |
|---|---|---|---|
| Lean 4 | the declaration inside a file; the file across files | elaboration errors become a synthetic `sorry` and the declaration is usually still added with its stated type, so later ones check and get no second error [recalled; one thread shows a case where it wasn't added: [Zulip](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/apply.3F.20might.20suppress.20other.20warnings.2Ferrors.html)]. A file with an error produces no `.olean`, so importers don't build [recalled] | `#eval` refuses a term that depends on `sorry`; `#eval!` forces it [recalled] |
| Agda | the module | a module with an error, or with unsolved metas, can't be imported ([test output](https://www.cse.chalmers.se/~ulfn/darcs/Agda2/test/fail/errors/UnsolvedMetasInImport.err) [cited]) | no |
| Idris 2 | the definition, for holes | a hole is a name with a type; users check | runs; reaching a hole is a run-time error [cited in using-unfinished-proofs.md] |
| Haskell, `-fdefer-type-errors` | the expression | "type errors will still be emitted as warnings, but will not prevent compilation"; "you can run any type-correct parts of your code just fine" ([GHC user's guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/defer_type_errors.html) [cited]) | yes; the error is raised when the expression is evaluated |
| Eclipse JDT | the method | a method that doesn't compile gets a body that throws `java.lang.Error: Unresolved compilation problem`; its signature stays, so callers compile [recalled] | yes, after "Errors exist in required project(s). Proceed with launch?"; JUnit runs, and tests reaching the method error [recalled] |
| Roc | the expression | "you can run a program that has compile-time errors … If the program reaches the error at runtime, it will crash", partly built ([roc-lang.org/friendly](https://roc-lang.org/friendly) [cited]) | yes |
| Rust, Kotlin, Scala, OCaml, Elm | the crate or module | nothing | no; only units that don't depend on the broken one build [recalled] |
| Unison | the definition | the codebase holds only definitions that checked; a broken edit stays in the scratch file while the old versions keep running; test results are cached by hash [recalled] | old code runs; new code doesn't until it checks |

**The pattern.** Every system that keeps going past an error does it the
same way: the broken thing keeps its *declared type* and loses its body
(Lean's `sorry`, JDT's throwing method, GHC's deferred expression). None
of the provers extends that across files, and none tells the users of a
broken declaration that they rely on it. Stitchwort can do both, because
reliance is read off kernel terms and a test's dependencies are known
before it runs: so a run never starts and then crashes at a gap, which is
what JDT, GHC, Roc and Idris do. Matt's observation (D3523) that most
languages run nothing after a compile error is true of the last two rows
but one, and those systems have no per-declaration check to lean on.

## 9. Recommendation and stages

Adopt the model of §3 and option C of §5. Merge SW-2932 as it stands: it
is stage 0 (per-declaration within a namespace, for tests), and its two
limits are what stages 1 and 3 remove.

| Stage | Work | Model | Estimate |
|---|---|---|---|
| 1 (built) | **Importers are checked (D3524, option B).** Drop the skip in `check_project_namespace`; a failed name crosses an import as a failed name; `E-USES-FAILED` once per broken name per file, and the syntax-error case of §4.2; importers' tests run under SW-2932's rule; goals, hovers and tests in importers; live project per §6; cache rule per §6; `docs/projects.md`, `docs/syntax.md`, guide 09, the book's text; `examples/projects/reject/failed` re-recorded | Opus (elaborator and project loading; a wrong guess spreads) | 2.5 h |
| 2 (built) | **Reporting.** `check`'s error summary lines; a test with its own error is a failed result; `test --json` `errors`; `audit` prints verdicts with errors and its JSON statuses; the implicit-use note of §4.2 | Sonnet | 90 min |
| 3 (built) | **Stand-ins (option C).** A `def` or `theorem` with a checked statement and a failed body (type or syntax error) becomes an assumption of its statement; label kind in `check::assume` and its hash; users elaborated and kernel-checked; the waiting rule for both kinds; `relied_on` reports the kind; `test` runs what only cites a broken theorem, with the "assuming" note for both kinds; `docs/core.md` (D3210); then an Opus review, since it generates kernel terms (D2364) | Opus | 3 h + review |
| 4 | **Editor and playground.** Hints and Information marks for both kinds; Testing panel and Tests tab messages; Check tab summary | Sonnet | 60 min |
| 5 | **`run` and `eval` with errors** (if D-e is yes) | Sonnet | 45 min |
| 6 | **Measure, then maybe cache.** Check `aoc/` with an error put into `Aoc.Common` (verifier or Overmind, not a lane); if it's slow, store namespaces with waiting declarations (§6) | Sonnet, after an Opus look at the cache's trust path | 90 min |

Order: 1, then 2 and 3 in parallel, then 4; 5 and 6 any time after 1.
Stage 1 alone fixes the book. Targeted tests: stage 1 the project tests
by name (`project.rs` failed-namespace cases, `test_json.rs`), the LSP
dependent-diagnostics test (`lsp.rs:1122`) and `stitchwort test` on the
book with the slip; stage 3 core's assumption tests and
`examples/goals/` by name.

## 10. Decisions for Matt

- **D-a (D3524): importers of a namespace with errors are checked,
  declaration by declaration.** Status belongs to declarations; a
  namespace is never skipped because another has an error; what uses a
  broken name is reported once per name per file. [rec: yes. It's what an
  open goal already does across namespaces, it adds no trust (the kernel
  still refuses anything built on a failed declaration), and it's the
  whole fix for the book.]
- **D-b (D3527, accepted 12 Nov 2026): an error is an assumption too.** A declaration with a checked
  statement and a broken body is stood in for by an assumption of its
  statement, so what uses it is checked, and reported as relying on it,
  never as finished. [rec: yes, as stage 3, after D-a's stage. Same
  soundness argument as `?`, already reviewed; it also stops a half-typed
  body from blanking its callers in the editor.]
- **D-c (D3525, accepted 12 Nov 2026): one rule for tests.** A test runs unless the *code* it runs
  needs a gap; a gap it only cites as a proof, whether `?` or an error,
  doesn't stop it, and the result line says what it assumed. [rec: yes.
  The alternative that's also consistent is strict: citing any gap fails
  the test, reversing SW-2909 for theorems. Running tells you more, the
  line says what was assumed, and the run exits 1 anyway while an error
  stands. The cost is D3507's: a false proof can make a run misbehave.]
- **D-d: exit status and `audit`.** Any error means exit 1 from `check`,
  `test` and `audit`, with no setting to relax it; `audit` still prints a
  verdict per theorem, so you can see which ones are unaffected. [rec:
  yes.]
- **D-e: `run` with errors.** `stitchwort run` runs `main` when the code
  it runs needs no gap, after printing the errors, and exits 1; `build`
  still refuses. [rec: yes for `run`, as for tests; low priority.]
- **D-f: the words.** "has an error", "relies on `x`, which has an
  error", "can't be checked until `x` is fixed", beside the goal words
  already chosen; `E-USES-FAILED` replaces `E-NAMESPACE-FAILED`. [rec:
  yes.]

## 11. Calls made (implementation, not Matt's)

- "Needs a gap" is decided by the gap's type (data, or proof/type), not by
  where the reference sits, as `unfinished_message` does now.
- One stand-in per broken declaration, not per erroneous expression: an
  ill-typed body has no trustworthy remainder to keep.
- A body with a syntax error fails its declaration with an internal error
  that is never shown (`E-UNPARSED-BODY`), at the syntax error's place, so
  the stand-in, the reporting and the summary are stage 3's, unchanged
  (SW-2980). A `decreasing` one isn't checked at all, as it gets no
  stand-in.
- No stand-in for types, interfaces, abilities or instances at first.
- A test with its own error is a result, not only a diagnostic.
- Stage 1 kept last answers in the live project for importers of a
  namespace with a syntax error; stage 3 made that unnecessary, and it is
  gone (SW-2997).
- `E-NAMESPACE-FAILED` is retired (SW-2997): no case was found, other
  than a cycle, which has its own code, where a namespace truly can't be
  checked.

## 12. Not known yet

- Whether cache replay of an importer assumes its dependencies were
  replayed (§6): read in stage 1.
- The cost in `aoc/` (§6): stage 6 measures it.
- How often an implicit use (`auto`, dot methods) of a failed
  declaration turns into a fresh error across namespaces: instance search
  waits (SW-2970), the rest wasn't tested.
- What exactly shipped from the SW-2809 review's must-fixes for false
  proofs at run time; D-c leans on them.
- Lean's and JDT's rows in §8 are recalled, not re-verified today.
