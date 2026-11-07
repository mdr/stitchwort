# Proposal: internal error kinds

**Status:** draft 1, 7 November 2026. Ticket SW-1908, from D2653. Decisions D2770 to D2773
([§8](#8-decisions-for-matt)). Builds on the 1 November review's §3.5
([rust-codebase-review.md](../research/rust-codebase-review.md)), and on the 7 November
reviews: [code-review-elab-checking.md](../reviews/code-review-elab-checking.md) F5 and F13,
[code-review-elab-rest.md](../reviews/code-review-elab-rest.md) F5 and F21,
[code-review-elab-tactics.md](../reviews/code-review-elab-tactics.md) F8. Related:
[bounded-readback.md](bounded-readback.md) §4.4 (D2540, D2543) and its stages 6a and 7
(SW-1839, SW-1841).

Code references are at commit `e35f954ad`. **[read]** means I read the code at the `file:line`
given; **[inferred]** means I reasoned from what I read and did not run anything (this was a
read-only lane: no builds, no tests).

## The short answer

The compiler decides some of what it does next by reading the text of its own error
messages: "was that error code `E-RESOURCE`?", "does the message end in *too large to
show*?". So a harmless-looking edit to an error's wording can change which proofs check.

The change: give `Diagnostic` a small internal field, `kind`, that says *why* something
failed in the few ways the compiler acts on (ran out of resources, and how; can't infer yet;
performs an ability; partial; and a handful more). The code that makes the error sets it; the
code that chooses a path reads it. The codes users see stay exactly as they are, and nothing
new is shown. Then a docs lane can reword any message, and a lane can rename a code, without
changing what the elaborator does.

What it should do, and how we'd know: after the sweep, no production code in `crates/elab`,
`crates/core` or `crates/driver` reads `message` text to decide anything, and every path
choice made on "ran out of resources" reads `kind`. A small source-scan test keeps it that
way. Every existing test passes unchanged, because the sweep changes no behaviour.

## 1. The problem

### 1.1 In plain words

Three edits a docs or cleanup lane could make today, each of which looks like it only touches
wording:

1. **Rewording "a value was too large to show"** to "a value was too big to print"
   (`crates/core/src/budget.rs:66`). `undo::recoverable` recognises that error by its last
   words (`crates/elab/src/undo.rs:128-131`) **[read]**. After the edit it would recognise
   nothing, so `rewrite` and `match` would stop going on past a read-back that is too large
   (`rewrite.rs:743`, `matching.rs:782`, `matching.rs:942`), and proofs that check today would
   fail with `E-RESOURCE`. The module report would also stop adding its "too large" notes
   (`module.rs:466`).
2. **Rewording "it took more evaluation steps than allowed"** (`budget.rs:61`). The module
   report decides whether to add "ran out while running `f`" by checking that the message
   ends with that sentence (`module.rs:214-218`, used at `:472`) **[read]**. The note would
   silently disappear.
3. **Rewording the non-exhaustive message's "no arm matches"** (wherever `E-NONEXHAUSTIVE`
   is made). `matching.rs:239` only rewrites the message for `match` if it contains those
   words, and `matching.rs:278` cuts the message at them **[read]**. The `match`-specific
   wording would silently stop.

None of these is a bug today: the reviews found no misclassification. The problem is that
nothing would catch one. The type is already there: the budget has a typed
`ResourceError { Work, Depth, Nesting, Size, Deadline, Cancelled }` (`budget.rs:37-55`), and
it is flattened into text at `budget.rs:73-78`; `module.rs:214` then parses the text back
into the type it came from.

Renaming a code is the louder version of the same problem. Codes are compared as strings
(`code: &'static str`, `crates/syntax/src/diagnostic.rs:28`), so renaming `E-CANNOT-INFER`
at its makers but missing one comparison would, for example, stop the kernel trying the right
side of an equation first when the left can't be inferred (`crates/core/src/check.rs:372`),
with no compile error.

### 1.2 Why it matters more now

The 1 November review counted one site. Today there are 144 lines comparing `.code` across
the crates, 115 of them in production code (outside JavaScript strings and tests), plus 95
calls of `undo::fatal`, each a string comparison by proxy, in 26 files **[read: grep at
`e35f954ad`]**. Most of them are harmless (§2.2); about 40 choose a path.

The larger risk sits under the string comparisons. `Result<T, Diagnostic>` is the error type
of the whole elaborator (`check.rs:19`, `lib.rs:153`, and seven more aliases), so every
`Err(_) => …` arm (55 in `crates/elab/src/*.rs`) and `.ok()` (105) that drops an error drops a
resource error too, unless someone remembered `fatal`. The 95 guards exist because the default
swallows. When a swallowed resource error changes which path is taken, the result depends on
where a shared budget ran out, which D2543 ("limits fail, never choose") rules out. §5.3 deals
with that part.

## 2. The map

### 2.1 Sites that choose a path

Grouped by what is read. "Kind" is the name the site's test gets in §3.

**Ran out of resources: `E-RESOURCE`** (kind `Resource`).

| Site | What it decides |
|---|---|
| `undo.rs:116` `fatal` (95 callers, 26 files) | propagate, rather than treat as "this way didn't work" |
| `undo.rs:126-132` `recoverable` | go on past a too-large read-back; reads **message text** `ends_with("too large to show")` |
| callers of `recoverable`: `matching/as_written.rs:186,219,305`; `rewrite.rs:743,839,956`; `matching.rs:782,942,1145`; `rewrite/as_written.rs:191` | recover and take another branch (D2540's concern; SW-1841 removes these) |
| `derive.rs:277`, `derive_ord.rs:165`, `derive_show.rs:98`, `derive_finite.rs:133`, `derive_decide.rs:91,127`, `derive_ext.rs:81`, `update_lemmas.rs:93`, `families.rs:59`, `derive_induct.rs:298` | re-raise, else drop or reword the generated declaration's failure (elab-rest F5) |
| `records.rs:178`, `partial.rs:818`, `decreasing.rs:1423` | re-raise, else wrap in the site's own error (`E-EXPORT`, the unpackable note, `E-DECREASING`) |
| `lib.rs:4460` `branch_failed` | stop, rather than collect the branch's error and go on |
| `auto.rs:904` `give_up_on`, `effects.rs:5219` | stop, rather than "this candidate doesn't fit" |
| `equations.rs:2501` | with `budget.exhausted().is_none()`: the attempt's own limit ran out, so skip the equation |
| `module.rs:415` | sets `Item::ran_out`, which shapes dependants' reports (`module.rs:602`) |
| `library.rs:1365` | a library file that ran out is passed on, not reported as `E-INTERNAL` "doesn't check" |
| `crates/driver/src/run.rs:219` (with `E-UNFINISHED`) | stop trying the other call shapes for `run` |
| `rewrite.rs:126`, `matching.rs:1507` | add the tactic's label when the error has none (shaping, listed here because it is the same test) |

**Ran out, and how** (kind `Resource(limit)`): `undo.rs:130` (size, by message);
`module.rs:466` (size, by message); `module.rs:214-218`, `:472` (steps or depth, by message).
These are the message-text sites the brief counts as two; there are three.

**Can't infer yet: `E-CANNOT-INFER`** (kind `CannotInfer`).

| Site | What it decides |
|---|---|
| `crates/core/src/check.rs:372` | the kernel infers an equation's right side first when the left can't be inferred |
| `check.rs:2979-2982` | which of two errors `retrying` keeps |
| `numbers.rs:1568` | restore, and queue the literal's leaf as uninferred (postponement) |

**Performs an ability, or is partial: `E-ABILITY`, `E-PARTIAL`** (kinds `Ability`, `Partial`).

| Site | What it decides |
|---|---|
| `check.rs:1815` | `pure_first` doesn't try running the expression (SW-437, SW-439) |
| `check.rs:1840` | which of the plain and the run error is reported |
| `lib.rs:1397` | check a test again as a partial computation (elab-checking F7) |
| `effects.rs:4837` | check a handler's body again as partial |

**The rest.**

| Site | Read | What it decides | Kind |
|---|---|---|---|
| `records.rs:567` | `E-NOT-A-CONSTRUCTOR` | braces are a record argument, not fields | `NotAConstructor` |
| `logic.rs:343-344` | `E-AUTO-NONE`, and the other error's `E-AUTO-NONE`/`E-INSTANCE-NONE` | give up on the decision reading (`Ok(None)`) | `NoInstance` |
| `rewrite/under.rs:658` | `E-REWRITE-PREMISE` | collect the missing premise and go on | `RewritePremise` |
| `rewrite.rs:840`, `rewrite/as_written.rs:191` | `E-REWRITE-BUDGET` | fall back to the unconfirmed path (SW-1839, stage 6a, removes it) | `RewriteBudget` |
| `crates/driver/src/search.rs:802` | `E-UNKNOWN-NAME` | retry the search pattern with the name as a new hole | `UnknownName` |
| `module.rs:434` | `goals::UNFINISHED` (a constant) | `Status::Unfinished` rather than `Failed` | none needed |
| `library.rs:1354-1357` | four warning codes (two as constants) | a library file with these warnings doesn't load (D306) | none needed |
| `crates/lsp/src/lib.rs:327` | `E-PARSE` | keep the last answers that parsed | none needed |

The three "none needed" sites read a finished diagnostic's public code as part of a public
convention (D306, D636, the editor's "last good parse"), so the code is the right key. They
should use named constants, as two already do (§4, stage 4).

### 2.2 Sites that only shape a message or a report

About 70 sites choose a note, a rewording or a filter by code, and change nothing else. In
elab: `ErrorFrame::map` impls (`check.rs:3247`, `:4253`, `:5410`; `defaults.rs:647`;
`decreasing.rs:814`; `numbers.rs:1638`); notes on `E-TYPE-MISMATCH` (`check.rs:4572`, `:4794`;
`numbers.rs:918`; `records.rs:1487`; `named.rs:635`; `autobind.rs:67`; `rewrite.rs:229`;
`defaults.rs:940`; `calc.rs:229`); on `E-ABILITY` (`effects.rs:904`, `:2920`, `:3659`;
`lib.rs:4664`; `defaults.rs:376`); on termination (`saturate.rs:67`, `lift.rs:1577`, `:1681`);
`goals.rs:478`, `quot.rs:416`, `induct_match.rs:525`, `derive.rs:648` and its two twins,
`check.rs:2618`, `:3296`, `:5072`, `:5741`, `logic.rs:348`, `:637`, `numbers.rs:1658`, `:1873`,
`rewrite.rs:330`, `rewrite/as_written.rs:159`, `:179`; and the reporting filters and de-dups
in `module.rs:546-595`, `:818`, `redundant.rs:71`, `matching.rs:1160-1254`, `rewrite.rs:971`,
`check.rs:4747`, `no_effect.rs:197`, `cache/mod.rs:455,629,673`, and the driver's
`driver.rs:558,912`, `project.rs:788` **[read]**.

These key on the public code, which is a stable contract (tests match on it,
`diagnostic.rs:26-27`), so a reworded message can't move them. Keying a note on the code is
what the code is for. They stay as they are (D2772), with one exception: the ones that read
**message text**:

| Site | Text read | Fix |
|---|---|---|
| `matching.rs:239`, `:278` | "no arm matches" | the maker records which form it made (a `MissingCases` field, or a flag) |
| `module.rs:549` | `message == format!("unknown name `{n}`")` | compare the name: `E-UNKNOWN-NAME` makers record it in `detail` |
| `defaults.rs:393` | `message.contains("`x`")` for an unknown name | the same recorded name |
| `numbers.rs:586` | a note contains "because of the literal" (don't add it twice) | a flag, or check `defaulted` before adding |
| `lift.rs:1609-1611` | message, labels and notes contain a helper's name (to rename it in the text) | leave: it rewrites text, and reads text to do so |

## 3. Designs

### A. A kind beside the code (recommended)

```rust
// crates/syntax/src/diagnostic.rs
pub struct Diagnostic {
    pub severity: Severity,
    pub kind: Kind,             // new: internal, never shown
    pub code: &'static str,
    …
}

/// Why something failed, in the ways the compiler acts on. Not shown, not
/// cached; the code is what users and tests see.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Kind {
    #[default]
    Other,
    /// Ran out of a resource: there is no answer within the limits, so this
    /// is never a "no" (D2543).
    Resource(Limit),
    /// Blocked on an unknown: might work once more is known.
    CannotInfer,
    Ability,
    Partial,
    NotAConstructor,
    NoInstance,
    UnknownName,
    RewritePremise,
    /// Until SW-1839 removes the unconfirmed path.
    RewriteBudget,
}

/// `ResourceError` without its payload (a `Nesting`'s pass name stays in the message).
pub enum Limit { Work, Depth, Nesting, Size, Deadline, Cancelled }
```

- **Where it is set.** `From<ResourceError> for Diagnostic` (`budget.rs:73`) sets
  `Resource(e.limit())`. The other kinds are set by the code that makes the error, through
  constructors that set code and kind together (`Diagnostic::cannot_infer(message)`), so a
  site can't make the code without the kind. The makers are few: about 19 for
  `E-CANNOT-INFER`, 19 for `E-ABILITY`, 3 for `E-PARTIAL`, 23 for `E-UNKNOWN-NAME`, 2 or 3 for
  the rest **[read: grep counts; some makers go through helpers that take the code as an
  argument, `check.rs:949`, `lib.rs:612`, so the real count is a little higher]**.
- **Where it is read.** `undo::fatal` becomes `matches!(e.kind, Kind::Resource(_))`;
  `recoverable` becomes `e.kind == Kind::Resource(Limit::Size) && budget.exhausted().is_none()`,
  which is exactly what the message test was approximating (its comment at `undo.rs:127-128`
  says it excludes `Nesting` on purpose; the typed form does so by construction). The other
  sites of §2.1 match `e.kind`.
- **Rewording and re-coding.** `kind` is the cause, not the presentation: changing `message`,
  `notes` or `labels` keeps it. A construct that turns an error into its own (`E-CALC-STEP`,
  `calc.rs:242`) builds a new `Diagnostic`, which starts at `Other`, exactly as today a new
  code stops matching the old comparison. So stage 1 changes no behaviour. Where a construct
  wants to keep the cause while changing the code, it says so (`e.recoded("E-X")`).
- **Finer than codes, where useful.** A kind needn't match a code one to one. `Resource`
  splits by limit, which no code does; later, `CannotInfer` could split into "blocked on an
  unknown the queue may still solve" and "can't ever be inferred" without changing what users
  see.
- **Size.** `Diagnostic` is kept small on purpose (`diagnostic.rs:33-36`, SW-1056). A
  two-level fieldless enum fits in one byte, which fits in the padding after `severity`, so the
  struct stays the same size **[inferred from layout rules; stage 1 adds a
  `const _: () = assert!(size_of::<Diagnostic>() == N)` to hold it]**. That is why `Limit` drops
  `Nesting`'s `&'static str`: carrying it would add 16 bytes to every `Result` in every frame.

**Cost.** One field, one enum, about 70 maker sites and about 40 reader sites, all
mechanical after stage 1. Nothing outside the compiler sees it.
**Rules out.** Nothing; B can still come later.

### B. A `Code` enum in place of the string

Replace `code: &'static str` with `code: Code`, an enum of the 172 codes, each with
`as_str()` giving today's text. The tactics review's F8 leans this way ("the string code
derived from it"). GHC did this in 9.6: each diagnostic constructor has a type-level code,
and the `GHC-12345` number users see is derived from it (from memory; not checked).

- **For:** every comparison, including the 70 shaping sites, becomes compiler-checked; a typo
  in a code is a compile error; renaming a code's text is one line.
- **Against:** 356 maker sites and the test suite's hundreds of `assert_eq!(e.code, "E-…")`
  change (or need `PartialEq<&str>`); the cache decodes a string back into a `Code`
  (`static_code`, `cache/mod.rs:1296`) and must handle unknown ones. And it does not fix the
  message-text sites: `Resource`'s limit still isn't in the code, so B needs A's `Limit`
  anyway. It also keeps the one-to-one tie between "how it's reported" and "why it happened"
  that A deliberately loosens.

### C. A typed error per layer

Make the elaborator's error type an enum rather than a `Diagnostic`:
`enum Error { Exhausted(ResourceError), Blocked(Box<Diagnostic>), Failed(Box<Diagnostic>) }`,
with `From<Diagnostic>` so `?` keeps working. This is what Lean and rustc do, roughly. Lean's
`Exception` has `error` and `internal` cases; postponement is an internal exception with its
own id, and `try … catch` skips runtime-limit errors unless written `tryCatchRuntimeEx`
(bounded-readback §4.4 cites it). rustc's trait solver returns typed `NoSolution` and
ambiguity rather than diagnostics, and errors already reported carry an `ErrorGuaranteed`
token (both from memory).

- **For:** "ran out" can't be mistaken for a failure in a `match` on the error; a boxed
  payload would make `Result` smaller still.
- **Against:** the elaborator mentions `Result` about 1,300 times (`crates/elab/src`), and
  every site that builds, inspects or decorates a `Diagnostic` in an `Err` changes. And it
  still doesn't stop the real hole: `.ok()` and `Err(_) =>` discard an `Exhausted` exactly as
  they discard a `Diagnostic`. Lean's guarantee comes from `catch` itself skipping runtime
  errors, not from the type. Stitchwort gets the equivalent more cheaply in the budget (§5.3).

### Recommendation

**A** (D2770). It fixes everything the reviews found, for about 110 mechanical edits, with
no change users can see and no change to the cache. B is a reasonable later tidy-up for the
shaping sites, but costs four times as much and needs A's `Limit` anyway. C is the most
principled, but costs a rewrite of the elaborator's signatures and still leaves `.ok()`
swallowing; §5.3's check closes that gap from the other side.

## 4. How it interacts with the rest

### 4.1 Postponement and retry

- **Queued checks and their frames.** An error raised when a postponed check resumes goes
  through the `ErrorFrame`s of the constructs it was made inside (`queue.rs:640-644`,
  `through_frames`, `queue.rs:719-730`). Frames already skip fatal errors (`queue.rs:693`,
  `:723`); those tests become `kind` tests. Frames that reword keep the kind; frames that
  build a new error reset it, as their new code does today (§3 A).
- **Blocked versus failed.** The queue's own decision, "fails only at pairs stuck on unknowns
  the queue still has to settle", is already typed (`compare_waiting` returns `bool`,
  `queue.rs:1034`; `Failure` is an enum, `queue.rs:1008`). The `E-CANNOT-INFER` sites of §2.1
  feed it from outside; `Kind::CannotInfer` gives them the same footing.
- **Retries.** `lib.rs:1397` (test as partial), `effects.rs:4837` (handler as partial),
  `check.rs:1815` (`pure_first`), `records.rs:567` (braces) and `search.rs:802` (pattern holes)
  each retry on one kind. Unchanged in behaviour; they read `kind`.

### 4.2 The budget errors (D2543)

- `E-RESOURCE` is the code for every `ResourceError`; the kind carries which limit. The
  message-text tests (`undo.rs:130`, `module.rs:214-218`, `:466`) become `Limit` tests.
- `recoverable` exists only until bounded-readback stage 7 (SW-1841), which makes a
  too-large read-back fail the declaration. Either order works: if SW-1841 lands first, stage 2
  here has fewer sites; if this lands first, SW-1841 deletes a typed test rather than a string
  one. I'd run this first, since it makes SW-1841's sites easy to find (decided myself:
  sequencing).
- `E-REWRITE-BUDGET` is a limit that chooses today (`rewrite.rs:840`): running out sends
  `rewrite` to the unconfirmed path. Stage 6a (SW-1839) removes that path; `Kind::RewriteBudget`
  goes with it.
- `equations.rs:2501`: an equation whose proof runs past the generator's fixed attempt limit
  is skipped, not failed. The limit is fixed and independent of the enclosing budget, so the
  result is deterministic, but it is a limit that chooses whether a lemma exists. Out of this
  note's scope; filed below.

### 4.3 The check cache

The cache stores only **warnings**, and only for namespaces with no errors or goals
(`cache/mod.rs:666-670`; `encode` refuses an error, `:1514-1516`). Each is stored as code,
message, labels and notes (`:1517-1527`) and read back with `Diagnostic::warning`
(`:3005-3006`) **[read]**. No warning has a kind other than `Other`, so a decoded warning
gets `Other` from the constructor, the same as a fresh one: equal under the derived
`PartialEq`, no format change, `FORMAT` (`cache/mod.rs:77`, 29) stays. If a warning ever needs
a kind, the end state is to store it as one byte and bump `FORMAT`; that costs nothing worth
counting, but isn't needed now.

The editor's indexes (`IndexDiagnostic`, `crates/driver/src/nav.rs:139-141`;
`LiveDiagnostic`, `live.rs:105`) copy the code, not the whole diagnostic, so the kind stays
inside the compiler.

### 4.4 The codes users see

No code changes, no message changes, nothing new is printed. `kind` is not shown by the
renderer and isn't in the JSON output. Tests that match codes keep working. The one visible
risk is `Debug` output, which the derive extends: I found no snapshot of a `Diagnostic`'s
`Debug` form, but stage 1 checks (`crates/driver/src/render.rs` and the `insta` users).

## 5. What it should do, and how we'd know

### 5.1 After the sweep

- `rg '\.message\.(ends_with|starts_with|contains)|message ==' crates/{elab,core,driver}/src`
  finds only `lift.rs:1609-1611` (which rewrites text) and tests.
- `rg '"E-RESOURCE"'` finds only `budget.rs` and the two other makers (`driver/src/run.rs:343`,
  `cli/src/main.rs:3123`, `syntax/src/parser.rs:719`; each makes one, and gets the kind from
  `From<ResourceError>` or a `Diagnostic::resource` constructor).
- Each §2.1 site reads `kind`.

### 5.2 A check that keeps it so

A unit test in `crates/elab` that scans its own sources for the two patterns above, with an
allowlist (decided myself: an implementation detail; a source scan is crude, but clippy can't
see a field comparison, and the patterns are narrow).

### 5.3 The backstop for swallowed limits

A kind makes the 95 `fatal` guards correct, but not complete: nothing makes the next
`Err(_) =>` remember one. Running out of steps, stack, deadline or frames is already sticky
for the operation: once out, every later check fails too (`budget.rs:7-8`, `exhausted`,
`:598`). Running out of **size** or **nesting** is not (`undo.rs:126-128`), and those are the
ones a swallowing site can turn into a different answer.

The end state I'd propose (D2771): once SW-1841 has made the size limit fail rather than
recover, the budget records every resource error it raises, and a declaration that finishes
`Ok` after one was raised is a compiler bug: `debug_assert!` in tests and the elaborator
fuzzer (`crates/driver/tests/fuzz_elab.rs`), `E-INTERNAL` in release. Attempts with limits of
their own (`Budget::attempt`, `budget.rs:311`; the generator's at `equations.rs:2485-2500`)
are excluded where their "ran out" is a documented answer, and listed. That is the Lean
property (`catch` doesn't see runtime limits) reached from the budget's side.

## 6. The sweep, in mechanical stages

Each stage leaves `main` building and every test passing, with no change in behaviour.

1. **Kind and Limit** (Sonnet, 45 min). Add `Kind`, `Limit` and `Diagnostic::kind` in
   `crates/syntax`; `ResourceError::limit()` and `From<ResourceError>` setting
   `Resource(limit)` in `crates/core`; `fatal`, `recoverable`, `module.rs:214-218` and `:466`
   read the kind; the size assertion. Other kinds aren't set yet. Tests: `task test:one --`
   for the resource tests (`crates/driver/tests/resources.rs`), the too-large-value tests
   (SW-1554's), and `crates/elab`'s `undo` and `module` unit tests.
2. **Every resource test through `fatal`** (DeepSeek, 40 min). The ~23 direct
   `== "E-RESOURCE"` sites of §2.1, including the derive group, `library.rs:1365` and the
   driver's `run.rs:219`. Absorbs elab-checking F13. Coordinate with elab-rest F5's
   "one helper for admitting a generated group" (after D2721): if that lane is queued, it
   takes the ten derive sites and this stage skips them. Tests: the derive tests touched,
   `resources.rs`.
3. **The other kinds** (Sonnet, 60 min). Kind-setting constructors for `CannotInfer`,
   `Ability`, `Partial`, `NotAConstructor`, `NoInstance`, `UnknownName`, `RewritePremise`,
   `RewriteBudget`; each maker uses one; each §2.1 reader matches `kind`. Includes the
   kernel's `crates/core/src/check.rs:372` (a one-line read; the kernel's behaviour is
   unchanged, but it is the kernel, so the orchestrator checks that diff line by line). Tests:
   the elaboration tests for each retry (partial tests, `pure_first`, braces, `search`
   patterns), `test:lane AREA=elab` if it fits the budget.
4. **Message-text shaping and named codes** (DeepSeek, 40 min). §2.2's text sites
   (`matching.rs:239,278`, `module.rs:549`, `defaults.rs:393`, `numbers.rs:586`) record what
   they need at the maker; the three "none needed" sites and the reporting filters use named
   constants. Tests: the non-exhaustive `match` messages, unknown-name-after-failed-import.
5. **The scan test** (DeepSeek, 20 min). §5.2. Tests: the new test itself.
6. **The backstop** (Opus, 60 min, after SW-1841 and D2771). §5.3. Tests: the fuzzer's
   short run, `resources.rs`.

Order: 1, then 2 and 4 side by side, then 3, then 5; 6 waits for SW-1841. Stages 1 and 3
touch `crates/syntax/src/diagnostic.rs` and so run one after the other.

## 7. What this note doesn't do

- It doesn't turn the 70 shaping sites into typed kinds; D2772 asks to confirm that.
- It doesn't redesign `E-REWRITE-BUDGET` or the read-back's recovery: SW-1839 and SW-1841 do.
- It doesn't count every `Err(_)`/`.ok()` that swallows a resource error; §5.3's check finds
  the ones that matter by running, which is more reliable than a review.
- The JavaScript `e.code` lines the grep finds (`crates/js/src/run.rs:451,532,536,1037`) are
  Node error codes in generated code, unrelated.

## 8. Decisions for Matt

- **D2770: adopt design A**, an internal `kind` on `Diagnostic` beside the public code, set
  where an error is made and read where a path is chosen, with codes and messages unchanged?
  [rec: yes, because it removes every string- and text-based decision for about 110
  mechanical edits, and leaves B possible later.]
- **D2771: end state for swallowed limits:** once SW-1841 lands, a declaration that succeeds
  after one of its resource limits was hit (outside listed, documented attempt limits) is a
  compiler bug, asserted in tests and the fuzzer, `E-INTERNAL` in release? [rec: yes, because
  it is D2543 made checkable: a kind makes the guards right, only this makes them complete.]
- **D2772: notes and rewordings keep keying on the public code** (no kind for the ~70 shaping
  sites), with only the message-text ones fixed? [rec: yes, because the code is already a
  stable contract that tests hold, and a kind per code would be design B at A's price.]
- **D2773: `CannotInfer` may later split finer than its code** ("blocked, may resolve" versus
  "can't be inferred") without a new user-visible code? [rec: yes, because kinds describe
  causes for the compiler, and users don't need the distinction in the code.]

## 9. Tickets to file

| # | Stage | Model | Est. | Tests | Order | Replaces |
|---|---|---|---|---|---|---|
| 1 | Kind and Limit on `Diagnostic`; `fatal`/`recoverable`/module report read them | Sonnet | 45 min | `resources.rs`, too-large tests, `undo`/`module` unit tests | first | elab-tactics F8's recoverable case; the 1 Nov §3.5 |
| 2 | Every `E-RESOURCE` test through `fatal` | DeepSeek | 40 min | derive tests touched, `resources.rs` | after 1 | elab-checking F13; elab-rest F5's sites if its lane hasn't taken them |
| 3 | The other kinds: makers set, readers match | Sonnet | 60 min | each retry's tests; `test:lane AREA=elab` within budget | after 1 (2 may run alongside) | elab-checking F5, elab-rest F21, elab-tactics F8 |
| 4 | Message-text shaping sites; named constants for public-code checks | DeepSeek | 40 min | non-exhaustive messages, failed-import unknown names | after 1, beside 2 | elab-rest F21's text sites |
| 5 | Source-scan test | DeepSeek | 20 min | the test | after 3 and 4 | — |
| 6 | Backstop: a hit limit can't end in `Ok` | Opus | 60 min | fuzzer short run, `resources.rs` | after SW-1841 and D2771 | part of D2540 |

**Findings to file separately:**

- `equations.rs:2485-2510`: the equation generator's fixed attempt limit skips an equation
  rather than failing; deterministic, but a limit that chooses whether a lemma exists. Ask
  whether it is a documented exception to D2543 (it would go on §5.3's list) or should report.
  Sonnet, 30 min to write up with a repro.
- `module.rs:214-218` decides "steps or depth" by matching each `ResourceError`'s `Display`
  against the message's end, so a future `Display` that ends with another's text would match
  both. Fixed by stage 1; no separate ticket unless stage 1 is deferred.
