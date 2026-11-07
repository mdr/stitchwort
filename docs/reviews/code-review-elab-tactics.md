# Code review: `crates/elab`, part 2, the tactics (SW-1899)

Reviewed 7 Nov 2026 by reading `crates/elab/src` at `c2d5d5aec`. I read only:
nothing was built or run. In scope: `rewrite.rs` and `rewrite/`, `omega.rs`,
`omega_search.rs`, `ring.rs`, `search.rs`, `closing.rs`, `cases.rs`, `calc.rs`,
`chain.rs`, `congruence.rs`, `saturate.rs`, `counterexample/`, `induct_match.rs`,
`decreasing.rs`, `auto.rs`, `membership.rs`, `logic.rs` and `goals.rs`, about
26.7k lines. I read in full the kernel paths (`omega.rs`'s entry points and
`emit`, `ring.rs`'s `emit`, `saturate.rs`, `counterexample/mod.rs`,
`rewrite/as_written.rs`, `rewrite.rs`'s `discharge` and `check_motive`,
`auto.rs`'s `prove`/`decide`/order, `cases.rs`'s closers) and skimmed the rest.

I built on these and did not redo them:
`docs/proposals/bounded-readback-remaining.md` (`omega`/`ring` atoms are
stage O; the `rewrite`/`match` unconfirmed and recovered paths are stages 6a
and 6b), `docs/reviews/SW-1321-stale-stuck-calls.md` (`tactic_or_wait`, F5),
`docs/proposals/stuck-blockers.md`, and `docs/reviews/SW-1808-kept-search-session.md`
(tickets SW-1818 to SW-1821).

## Summary

**Overall.** The tactics have a sound trust boundary, and I found no way for
a tactic to make a false theorem check. Every term a tactic builds is part of
a body that goes to the kernel through `define_group`
(`kernel.rs:78`). The only unchecked admissions are the cache's
`admit_trusted_*`. The term rewrites that run before the kernel
(`saturate`, `settle_tagged`) feed the kernel, and their output is checked
like any other term. `omega` and `ring` emit a certificate that the kernel
checks by running the library's own checker (`rfl`). `auto` and `cases`
run decision procedures only to choose a proof, and the kernel runs them
again. Search suggestions are only text, which is elaborated again and
checked. Search limits are counts (rows, steps, cases, plans), apart from
two wall clocks: `search --at`'s deadline (advisory and documented) and the
counterexample search's 200 ms. The second one decides what a failing
theorem's diagnostic says, and it behaves differently in the browser
(F5). The fixed hasher is used throughout, and no hash map in scope is
iterated. The weak points are robustness and upkeep, not soundness:
- `omega`'s own "this is a bug" errors are swallowed when it runs inside
  another tactic.
- The arithmetic readers recurse with no stack guard.
- A `catch_unwind` in the search contradicts an assumption of the
  kept-session review.
- The counterexample search reruns on every failing or `:= ?` theorem at
  every check.
- The abstract-and-transport machinery exists four times.

**Top five recommendations:**

1. **Let `E-OMEGA-INTERNAL` through** when `omega` runs inside `rewrite`,
   `cases` or `auto` (F1). Today those callers turn an `omega` bug into
   "not proved", which hides it from the user and from `fuzz_elab`'s "no
   internal error" oracle. S.
2. **Stack guards in `omega`'s and `ring`'s readers** (F2): `Quoter::quote`,
   `quote_int`, `Reader::read_nat` and `read_int` recurse on the value with
   no `budget.nesting` check. A deep stuck sum aborts the process (in the
   editor, the server) instead of giving `E-RESOURCE`. S.
3. **Decide what a panic in the search's comparison does** (F3).
   `search.rs:1402` catches it, counts it and goes on in the same session.
   In the kept editor session that session lives on, so SW-1821's "if a
   panic is ever caught" is already true. Fold this into SW-1820 and
   SW-1821. S to M.
4. **The counterexample search in the editor** (F4, F5, F6, D2700, D2701):
   - it runs at every check for every failing or `:= ?` theorem, up to 200 ms
     each, since those namespaces are never cached;
   - its note depends on the clock and the build;
   - its timer starts earlier than its comment says.

   Remember results per statement for the session, bound the failure-time
   search by inputs, as `ON_AUDIT` is, and fix the timer. M.
5. **One module for "abstract the occurrences, build the motive, check it,
   transport"** (F7). It exists in `rewrite.rs`, `matching.rs`, `check.rs`
   (`transport_along`) and `induct_match.rs`, with two `as_written`
   variants and two different motive checks. Start with a design note
   after stages 6a and 6b, which delete much of it. L.

**Count:** 0 high, 7 medium, 10 low.

## Findings

| # | Sev. | Conf. | Where | What | Fix (size, model) |
|---|---|---|---|---|---|
| F1 | medium | high | `omega.rs:293-301`, `318-330`; callers `rewrite.rs:596`, `cases.rs:372,379`, `auto.rs:406` | `omega` as a sub-tactic swallows every non-`E-RESOURCE` error, including `E-OMEGA-INTERNAL` | Let internal errors through, or record them where tests and the fuzzer see them (S, Sonnet) |
| F2 | medium | medium | `omega.rs:1959` (`Quoter::quote`), `2072` (`quote_int`); `ring.rs:794`, `845` | Recursion on the value with no `budget.nesting`: a deep stuck sum overflows the stack (abort) | `g.machine.budget.nesting(PASS)?` at each entry (S, Sonnet) |
| F3 | medium | medium | `search.rs:1402` | `catch_unwind` around each comparison: a panic is counted and the session goes on, in the kept editor session too | Drop the catch, or mark the session poisoned so the driver discards it (S-M, Sonnet; with SW-1820/1821) |
| F4 | medium | high | `module.rs:610-680` → `counterexample/mod.rs:271`; `cache/mod.rs:666` | Every failing or wholly-`?` theorem runs a search (≤200 ms + up to 5M steps of building) at every check; such namespaces aren't cached, so the editor pays it per edit | Remember per statement content hash for the session; or skip it in probe sessions (M, Sonnet) |
| F5 | medium | high | `counterexample/mod.rs:54-57`, `594`, `652`, `1053-1081` | The failure-time note depends on wall time (whether one is found, how far it's shrunk) and on the build (no clock in wasm) | D2700: end it by inputs, with time as a backstop, as `ON_AUDIT` does (S, Sonnet) |
| F6 | low | high | `counterexample/mod.rs:322`, `357-358` | "The time limit counts from here", but `started` was taken before `build_checker`, so building eats the 200 ms | Take `clock::now()` at line 358, or fix the comment (S, DeepSeek) |
| F7 | medium | high | `rewrite.rs:1586,1665`; `rewrite/as_written.rs`; `matching.rs:610-940,1680-1845`; `matching/as_written.rs`; `check.rs:1423,1551`; `induct_match.rs:113` | Four implementations of occurrence abstraction, motive construction and motive check; two `as_written` (478 + 793 lines); two motive checks that differ (`kernel::check_type` vs the lifted helper's type) | Design note after 6a/6b: one `abstract`/`transport` module (L, Opus) |
| F8 | medium | high | `undo.rs:115-132`; `auto.rs:903`; `rewrite.rs:124`; `saturate.rs:67`; `goals.rs:478` | Control flow by diagnostic code strings, and "recoverable" by message suffix (`ends_with("too large to show")`); the 1 Nov finding, still open | A typed error kind on `Diagnostic` for the codes control flow reads (M-L, Opus design first) |
| F9 | low | medium | `omega.rs:3993-4045`, `ring.rs:1186-1240` vs `rewrite.rs:1615` | `omega`/`ring` check their term in the elaborator's modes (glued `unify`); `rewrite` checks its motive the kernel's way (`without_glue`, `kernel::check_type`). A disagreement surfaces as a kernel refusal naming `Std.Omega` terms, not as `E-OMEGA-INTERNAL` | When no unknowns remain, check the emitted term with `kernel::check` under `without_glue` (M, Sonnet) |
| F10 | medium | medium | `core/src/pretty.rs:1207`; J built in `rewrite.rs`, `calc.rs:398,406`, `check.rs:1423`, `cases.rs` | The printer shows every `J` as `J (m) (b) (p)`, including the compiler's own; SW-1680 is one case | Show a compiler-made `J` by what it transports; a snapshot test that no reject output has `J (` unless the source wrote `J` (M, Sonnet; with SW-1680) |
| F11 | low | low | `counterexample/inputs.rs:228-233` | Input plans are keyed by the printed type; two types that print alike (a cut `…`, the same short name) share a plan, giving ill-typed inputs and a possible bogus "statement is false" | Key by the quoted `Term` (S, Sonnet) |
| F12 | low | medium | `driver/src/counterexample.rs:258`; `counterexample/mod.rs:617,661` | The fast runner lowers the checker again for every batch: each random chunk and each of up to 200 shrink rounds | Lower once per search; pass the inputs separately (M, Sonnet) |
| F13 | low | high | `auto.rs:797`, `rewrite.rs:402`, `rewrite/as_written.rs:257`, `search.rs:1676` | Debug switches read with `env::var_os` on hot paths (`decide` runs for every `auto` argument) | Read once (`LazyLock`) or put them in `Options` (S, DeepSeek) |
| F14 | low | high | `apps`: `decreasing.rs:115`, `derive_induct.rs:230`, `partial.rs:85`, `omega.rs:4066`; `spine`: `decreasing.rs:290`, `saturate.rs:337`, `logic.rs:757`; `telescope` with `usize::MAX - 2`: `induct_match.rs:47,78,217,229`, `check.rs:6292`, `patlet.rs:152` | Small helpers copied; the fake level is a latent panic if anything under it is ever read back | One `term_util` (or `Term` methods); a named `Value::dummy_var` (S, DeepSeek) |
| F15 | low | high | `cases.rs:64` vs `113` | The docs say the split equation is `%splitN`; the code binds `%caseN` | Fix the comment (S, DeepSeek) |
| F16 | low | medium | `omega_search.rs:905-907`, `914` | `replay` adds and multiplies `i128` unchecked: it panics in debug and wraps in release, while the search beside it uses checked arithmetic | `checked_mul`/`checked_add`, `false` on overflow (S, DeepSeek) |
| F17 | low | high | `omega.rs` (4,097 lines), `decreasing.rs` (3,136), `rewrite.rs` (2,316) | Too large to read whole: `omega.rs` holds reading, quoting, splitting, failure messages and emitting | Split `omega.rs` into `omega/{read,quote,split,explain,emit}.rs` when next touched (M, Sonnet) |

## Details

### F1. `omega` inside other tactics hides its own bugs

`prove_premise_within` (`omega.rs:263`) and `prove_case` (`omega.rs:315`)
restore the snapshot and return `Ok(None)` for every error that isn't
`undo::fatal`, which means every error except `E-RESOURCE`. That includes
`E-OMEGA-INTERNAL` (`omega.rs:801`): the pre-check's "`Std.Omega.check`
refuses the certificate" or "the quoted goal means … not the goal …". So a
bug in `omega`'s quoting shows up as a `rewrite` premise "not proved", a
`cases` case left open, or an `auto` argument `E-AUTO-STUCK`. The user gets
a wrong account of their program. `crates/driver/tests/fuzz_elab.rs`
oracle 2 ("no `E-…-INTERNAL` diagnostic") can't see it either, because no
diagnostic is ever made. `omega` runs inside `auto` on every arithmetic
obligation where `omega`'s library is loaded, and inside `cases` on every
case. That makes these the most-run paths of `omega`, and the least
watched.

**Fix:** treat a diagnostic whose code ends in `-INTERNAL` like `fatal` in
both functions, or keep returning `None` but push the error onto a session
list that `fuzz_elab` and a debug assertion check. The same applies to
`ring` if it is ever called as a sub-tactic. Add a unit test that forces
the pre-check to fail (a test-only switch that corrupts the certificate)
and asserts the error comes out of `cases`.

### F2. Unguarded recursion in the arithmetic readers

Every other recursive pass in the elaborator calls
`g.machine.budget.nesting(…)` at each level (`lift.rs:351`,
`saturate.rs:126`, `Term::rewrite_up`, `decreasing.rs`). That check turns
a stack that is too deep into `E-RESOURCE`. `omega.rs` and `ring.rs` have
none. `Quoter::quote` (`omega.rs:1959`) recurses once per `k + base`,
`a + b` and `k * x` layer, and `quote_int` (`2072`, through `sub!`), `ring`'s
`Reader::read_nat`/`read_int` (`ring.rs:794`, `845`) and the
`NTerm`/`ITerm` helpers (`atoms`, `render`) do the same.

Each frame carries a `Result<Result<NTerm, Unknown>>`, and a `Diagnostic`
is large, so a stuck sum a few thousand deep is enough on a 2 MiB thread
(the default `Limits` and the test threads), or tens of thousands on the
CLI's 64 MiB. Such a sum is easy to make:
`(List.range 5000).foldRight (_ acc => acc + x) 0 <= …` computes to
`x + (x + … )`, stuck on `x`. A Rust stack overflow aborts the process. In
the editor that kills the server, where the user should get an error.

**Fix:** one line at each recursive entry. The budget's stack floor
already makes it cheap.

### F3. A caught panic in the search

`Elaborator::search` (`search.rs:1402`) wraps each `search_one` in
`catch_unwind(AssertUnwindSafe(..))`, counts a panic as
`stats.internal_errors`, and moves on to the next candidate. This has been
there since SW-915 (`3b8e08f7c`, 31 Oct). The `Restore` guard
(`search.rs:916-932`) and the budget's `Operation` put back the metas,
the trail, the frozen metas, glue and the budget as they unwind. Nothing
puts back other state a panicking comparison may leave half-changed: the
unifier's caches, the kernel's `apart_sets`, a `RefCell` that a frame
outside the guard had borrowed.

SW-1808's finding 4 (now SW-1821) rated `Machine::reset` leaving glue and
erasure harmless "because no catch of a panic is reachable from these
paths". This catch is reachable: the kept session runs `search` for
completion and code actions. SW-1820 proposes adding a catch in the
worker.

**Recommendation:** take one policy for both tickets. Either a panic in
the search ends the request and the kept session is dropped and rebuilt
(remove this catch; SW-1820's worker-level catch answers "no result"), or
this catch stays and sets a "poisoned" flag that makes the driver drop the
warm session afterwards. I recommend the first: a panic is a bug, and a
comparison that panics once will panic for every query that reaches it,
so going on hides it.

### F4. The counterexample search at every check

`note_counterexample` (`module.rs:610`) runs `counterexample_note` for every
theorem that failed, and for every theorem whose proof is wholly `?`.
Namespaces with an error or a goal are never written to the check cache
(`cache/mod.rs:666-670`), so they are elaborated again at every check, and
the search runs again each time. Each search spends:
- up to `STATEMENT_STEPS` (5M evaluation steps, about 0.75 s at the
  documented 0.15 s per million) building the checker;
- then up to `TIME_LIMIT_MS` (200 ms) searching (but see F6).

A user who writes ten statements as `:= ?` and then proves them one at a
time pays up to 2 s of extra latency on every keystroke's check. The kept
session also grows the log each time (SW-1818). The log exists only to hand
the found bindings from `counterexample_note` to `module.rs:663`, which
reads `.last()`.

**Fix (M):**
1. `counterexample_note` returns the `SearchLog` (or just the `Counterexample`
   data) instead of pushing it, which ends SW-1818's leak for free.
2. Keep a per-session memo from the statement's content hash (its type's
   `def_hash` with dependency hashes) to the note. A statement that hasn't
   changed gets the same note without searching. With F5's input-bounded
   search the memo is exact.

Alternatively, or as well, turn it off in probe sessions (SW-1818's option
(a)).

### F5. A note that depends on the clock and the build

The failure-time search (`ON_FAILURE`: 2,000 inputs, 200 ms) is normally
ended by time on any statement that is slow to run. Phase 2 draws random
chunks "until four fifths of the time" (`mod.rs:594`). Shrinking runs "in
the time left" (`652`). So on a loaded machine:
- the same failing theorem can get a note on one run and none on the next;
- the note can show a less-shrunk counterexample.

In WebAssembly there is no clock (`mod.rs:1053-1081`), so the browser
playground's note can differ from the CLI's for the same file. Tests avoid
all this through `STITCHWORT_UNTIMED_COUNTEREXAMPLES`
(`mod.rs:1083-1093`). `ON_AUDIT` already chose inputs over time "so that
the vacuity warnings don't vary from run to run" (`mod.rs:66-73`). D2543
("limits fail, never choose") was written for the read-back path, but the
same rule fits here: a limit here chooses what a diagnostic says. → D2700.

### F6. The timer starts before the build

`search_counterexample` takes `started` at line 322, before `build_checker`.
At line 357 it says "The time limit counts from here", and then uses that
same `started` (`let timed = started.filter(…)`). A statement whose
checker takes 200 ms to build (as much as 5M steps is allowed) leaves the
search one input at most: the first `each` call sees the time already
passed. Either the comment or the code is wrong. I think the code is,
since the build has its own step limit.

### F7. Four copies of the transport machinery

Each of these finds occurrences of a term in a goal, abstracts them into a
motive, checks the motive, and builds a `J` or an eliminator application:
- `rewrite`: `replace_occurrences`, `check_motive` (`rewrite.rs:1586`,
  `kernel::check_type` under `without_glue`), `round_trip` (`1665`), and
  the folded variant in `rewrite/as_written.rs`.
- generalised `match` and `cases`' split: `matching::generalised*`
  (`matching.rs:610-940`), `check_motive` (`1680`, which checks the
  type of a lifted helper draft), and `matching/as_written.rs`.
- the match-equation transport: `Ctx::transport_along` (`check.rs:1423`),
  with `abstract_needle` (`check.rs:1551`) matching syntactically
  (`same_shifted`).
- `match induct`: `induct_match::Abstract` (`induct_match.rs:113`), with its
  own `telescope` walking under a fake level.

The two motive checks can disagree on a motive (one checks the motive's
body as a type, the other the helper's full type). D2542's "search what you
see" has to be built into each copy separately, and bugs in this area
(SW-1680's `J` in a message, the hidden-copy rules) are fixed one copy at
a time. Stages 6a and 6b delete the `as_written` unconfirmed paths and the
recovered sites. After that, the remaining overlap is the core of a single
module: occurrence search by key, abstraction, one motive check, the round
trip and the `J`. This is what the architecture review's `ProofCx` crate
candidate would need first.

### F8. Control flow on code strings

This is the 1 Nov finding (`undo::fatal`, `e.code == "E-RESOURCE"`), still
open, and the tactics lean on it more than anything else:
- `undo::fatal` appears in nearly every `Err(e) if fatal(&e)` arm in scope;
- `auto::give_up_on` (`auto.rs:903`) repeats it;
- `rewrite::resource_in_rewrite` (`rewrite.rs:124`) checks the same code;
- `saturate::explain` keys on `"E-TERMINATION"`;
- `goals::unfinished_dependency` keys on `"E-FAILED-DEPENDENCY"`;
- `undo::recoverable` keys on the message's last words
  (`ends_with("too large to show")`), so rewording that message changes
  elaboration.

Stage 7 of the bounded read-back plan removes the recoverable case. The
rest needs a typed kind on `Diagnostic` (an enum the kernel and budget
set, with the string code derived from it).

### F9. Two ways to predict the kernel

`omega`'s `emit` (`omega.rs:3993-4045`) and `ring`'s (`ring.rs:1186-1240`)
check their term by evaluating the checker with `cx.eval` and comparing
types with `cx.unify`, in the elaborator's modes (glue on). `rewrite`'s
`check_motive` and `has_carrier` call the kernel itself under
`kernel::without_glue`. Both approaches are sound, because the kernel
checks the term again. But only the second predicts the kernel exactly.
If the first passes and the kernel refuses, the user gets a kernel type
mismatch at the definition, showing `Std.Omega.prove (MkEnv …)` terms
(F10's problem again), not `E-OMEGA-INTERNAL` at the `omega`. Once the
unknowns are solved, `kernel::check` on the emitted term under
`without_glue` would give the "checks the way the kernel will" that the
module docs promise. Fuzz oracle 3 would catch a disagreement. I have not
seen one.

### F10. Compiler-made `J` in messages

`pretty.rs:1207` prints `J` generically. That is right for a source `J`
(`examples/soundness/proof-irrelevance-15-after-j.sw` shows one), but
`rewrite`, `calc` (`calc.rs:398`, `406`), the transport and `cases`'
contradictions also build `J`s that the user never wrote. When one of them
ends up in a type that a message shows (SW-1680), the message names syntax
the user can't connect to anything they wrote. The elaborator could wrap
its `J`s in a marker (a `Loc` with the tactic's span, or a flag), and the
message printer could show a marked one as its base with a note
"(transported along …)". A snapshot sweep would hold the line: no
`examples/reject` output contains `J (` unless its source does.

### F11 to F17

These are in the table. F11 matters only if two input types print alike.
`pretty::term` cuts a deep term to `…` once the stack budget is used up,
which makes that possible for large types. A shared plan would then make
ill-typed inputs, and the reference evaluator "confirms" whatever it
computes. F16 can only fire if a certificate's rows differ from the ones
the checked search made, so it is defence in depth.

## Checked and sound

- **The trust boundary.**
  - Every tactic's term reaches the kernel inside its definition's body
    (`lift.rs:811` → `kernel::define_group`).
  - `admit_trusted_*` is called only from the cache (`cache/mod.rs:2774`,
    `2787`).
  - `saturate` (eta-expanding partial recursive calls, `saturate.rs`) and
    `settle_tagged` (`logic.rs:716`) run before the kernel, and the kernel
    checks what they make. `settle_tagged`'s "trusts that `tag` and the
    decision agree" is about the program's run-time choice only, not its
    logic.
  - Goals never reach the kernel (`goals.rs:14-18`, `UNFINISHED`).
  - `decreasing` installs the run body only after `f.unfold` is proved
    (`decreasing.rs:1077-1097`), and `set_run_body` checks its type.
- **`omega_search`.** Untrusted, deterministic (no map iterated, the budget
  counts rows), with checked `i128` arithmetic and `Rat` normalisation in
  the search itself. `Failure::Budget` is reported as such
  (`omega.rs:3668`), not as "false".
- **Determinism.** `stitchwort_core::collections::HashMap` uses a fixed
  hasher (`collections.rs:19-31`). In scope, `cases` `splittable`, `inputs`
  `keys`/`tiers`, `decreasing` `respects`/`congs`, `induct_match` `map` and
  `omega_search` `by`/`numbers` are only looked up. `auto`'s decision order
  goes by `DefId` in file mode and by path in a project
  (`auto.rs:1007-1040`), and `DecisionOrder`'s key covers what the order
  depends on. The counterexample random seed comes from the statement's
  text (`mod.rs:582-591`).
- **`rewrite`'s budget.** Running out is `E-REWRITE-BUDGET`, never "no
  match". Each candidate is a transaction. An `as_written` attempt costs
  the usual search nothing when it fails (`as_written.rs:229-253`).
- **`calc`.** The combination table (`calc.rs:385-429`) is correct for all
  nine pairs, and orders are restricted to `Nat` (`E-CALC-RELATION`).
- **The `cases` decision closer** only chooses (`cases.rs:441-470`); `No`
  doesn't fail a case. `CASES` (64) bounds the tree, and running past it is
  `E-CASES-BUDGET`.
- **Counterexamples.**
  - A fast-runtime result is confirmed on the reference evaluator, and a
    disagreement is shown as an internal error.
  - Building the checker is checked to declare nothing.
  - Cancellation on the reference path gives no answer.
  - Failing namespaces aren't cached, so no timed note is ever replayed.
  - Text size is covered by `code-review-rt.md` F4.
- **`congruence::candidates`** is keyed by the definition count and
  cleared on rewind (`state/caches.rs:134`).
- **The search.** Each attempt runs under `ATTEMPT` and a `Restore` guard,
  and plans are text that the driver checks (`closing.rs:19-21`).

## The 1 Nov review's findings in this scope

| Finding (docs/research/rust-codebase-review.md) | Status |
|---|---|
| Control flow on string codes (`undo::fatal`, §3) | **Open**, and used more widely in the tactics (F8) |
| Search JSON snapshot depends on the wall clock (§2) | **Mitigated**: `--time 120s` (`AT_TIME`, SW-1168), `checks` normalised. The deadline itself stays by design. |
| Background proof actions unbounded, unversioned (§1.4) | Outside this scope (`lsp`). SW-1798's single search worker bounds concurrency; versioning not re-checked here. F3 bears on its panic handling. |
| Architecture review: proof automation as a crate behind `ProofCx` | **Open**, unchanged; F7 is a prerequisite |

## Tickets to file

1. **`omega`/`ring` hardening** (F1, F2, F16). Sonnet, 45 min. Let
   internal errors through `prove_premise_within`/`prove_case`; add
   `nesting` to the four readers; checked arithmetic in `replay`. Tests:
   `task test:one` on the `omega` examples, plus a new reject example with
   a 5,000-deep stuck sum expecting `E-RESOURCE`.
2. **The caught panic in the search** (F3). Fold into SW-1820/SW-1821, by
   D2701. Sonnet, 30 min on top of those.
3. **The counterexample search in the editor** (F4, F6, with SW-1818).
   Sonnet, 60-90 min, after D2700. Return the log instead of pushing it,
   remember per statement hash, fix the timer start.
4. **Counterexample inputs and lowering** (F11, F12). Sonnet, 45 min.
5. **Mechanical tidy-up** (F13, F14, F15). DeepSeek, 30-45 min.
6. **Compiler-made `J` in messages** (F10, with SW-1680). Sonnet, 60 min,
   or Opus if the printer marker touches core.
7. **Design note: one abstraction and transport module** (F7), after 6a and
   6b. Opus, 90 min.
8. **Design note: typed diagnostic kinds** (F8). Opus, 60 min, with the
   bounded read-back's stage 7.
9. **The kernel's way in `omega`/`ring`'s pre-check** (F9). Sonnet, 45 min,
   low priority. Split `omega.rs` when it is next touched (F17).

## Questions for Matt

- **D2700: should the counterexample search on a failing theorem be ended
  by its count of inputs rather than by time, so its note is the same on
  every run and in the browser?** Time would stay as a backstop for slow
  statements, as `stitchwort audit`'s search already works. The cost is
  that a slow statement's search may take longer than 200 ms before the
  backstop. [rec: yes, with F4's memo so the editor pays once per
  statement]
- **D2701: when a search comparison panics, should the request fail and
  the editor's kept session be rebuilt, rather than the search going on
  in the same session?** [rec: yes: remove the per-comparison
  `catch_unwind`, and let SW-1820's worker-level catch answer "no result"
  and drop the warm session]
