# How work gets done

Stitchwort is built by Matt with AI models doing most of the writing. This
note records who does what, so the split stays consistent between sessions
and any model working on the repo can read it. The kanban board in `board/` is the task list (see [board/README.md](../board/README.md)).

## Who does what

| Model | Used for |
|---|---|
| **Claude Opus** | Design notes, analysis, anything touching the kernel or soundness, proofs, tricky bugs, writing specs for other models, and reviewing every diff before it's merged. Also orchestrates: hands out tasks, merges, runs the test tiers. |
| **Claude Sonnet** | Implementation that needs judgement: changes across several files, the checker and elaborator, anywhere a misreading would spread. |
| **DeepSeek V4.1 Flash** (via OpenCode Go) | Mechanical coding from a precise spec: renames, sweeps, boilerplate, new tests, small features with a clear shape. |
| **GLM-5.3-Flash** (via OpenCode Go) | Fallback when DeepSeek is unavailable. |
| Local model (Ollama) | Offline fallback only; about 20 times slower. |

The aim is to spend Opus on the hard reasoning and hand everything else to
cheaper models. Specs for DeepSeek are written by Opus: a spec says which
files to read, what to change, what tests to add, and which checks to run.

## Significant designs

A design that changes the language goes in a note under `docs/proposals/`,
researched against how other languages do it. Matt decides the open
questions, an independent reviewer reads the note, and only then does
implementation start, usually in stages.

## Handing a task to DeepSeek

1. Make a scratch clone with no git remote, so the model can't push.
2. Run OpenCode there in the background with the spec. The spec says: no
   sub-agents, no commits; run `cargo fmt`, clippy and the relevant tests;
   leave new snapshots (`.snap.new`) and benchmark changes for the reviewer.
3. Opus reviews the diff line by line. DeepSeek has introduced real bugs
   before, so its own "tests pass" isn't enough.
4. Commit in the clone with the trailer "Done by OpenCode with DeepSeek V4.1
   Flash (OpenCode Go) from a spec by Claude; reviewed by Claude", check the
   commit author, then fetch and merge into `main`.
5. Regenerate snapshots and the benchmark baseline, stage them, and run the
   merge tier (below). For playground changes also run `task test:browser`.
6. Update the ticket: move it to done and record the commits (`board/board commit N HASH`, `board/board move N done`).

Claude's own lanes work the same way, in git worktrees instead of scratch
clones.

## The test tiers

Tests run in tiers with time budgets ([testing.md](testing.md#tiers)), so
that most of the time the tests being run are fast ones:

- **lane**, under 10 s: a lane runs `task test:lane AREA=…` for the area it
  changed, and `task test:one -- NAME` for the tests it touched, while it
  works.
- **merge**, under 60 s: `task test:merge` on `main` after every merge.
- **daily**, under 5 minutes: `task test:daily`, or `nix flake check`
  (`task test:gate`), at a daily checkpoint: formatting, clippy, every test
  with the corpus sweeps on a sample, the examples and their snapshots, hash
  stability and the benchmark baseline, and `debug-builtins` (the
  `stitchwort-driver` `builtins` test binary, which loads the prelude, built
  and run in the debug profile so overflow checks and `debug_assert!`s are
  exercised; every other check is release).
- **full**: `task test:full`, every test over the whole corpus, only when
  Matt asks.

New files must be `git add`ed first, since the flake only sees tracked
files. Long runs (the daily tier, browser tests, builds) go in the
background.

Before committing, run `stitchwort fmt` on the `.sw` files you touched. The
test `crates/cli/tests/fmt_repo.rs` fails, naming the files, if any tracked
`.sw` file is not formatted. It skips `examples/reject`, `examples/soundness`,
`examples/projects/reject`, `crates/fmt/tests/golden` and
`examples/accept/list-literal-layout.sw`, so leave those as written.

Pushing to GitHub happens only when Matt asks.

## Lanes and the task list

Work runs in lanes (up to three at once), each in its own git worktree and
branch, merged into `main` one at a time (with `nix flake check` after each).
The main session orchestrates: it chooses lanes, hands each to a background
agent, then reviews, merges and keeps the board up to date. Agents move their
own tickets as described in [board/README.md](../board/README.md).

- Lanes that change performance run the benchmarks before merging
  (`nix develop -c cargo run --release -p stitchwort-bench`) and record an
  intended change with `-- --update`, saying why in the commit. The
  deterministic counts are checked by `nix flake check` (+10% fails).
- Significant design decisions (soundness, the kernel, language semantics)
  get a design note in `docs/proposals/` first, researched against the
  literature, and wait for the user (and possibly an external reviewer)
  before implementation.
- Questions for Matt in a session get a D number (D1454, D1455, …),
  counting up from the highest in use so each is unique. D numbers are
  handles for the session's open questions, not a permanent record: the
  answer goes on the SW- ticket it concerns. After each turn the
  orchestrator lists the session's unanswered D questions, each followed by
  its recommendation in square brackets (`D1454: start these lanes? [rec:
  yes]`).
- New findings become tickets in `backlog` (label `bug` for known issues),
  not straight into `next`, unless they block what's in progress.
- Design detail lives in `DESIGN.md` and `docs/proposals/`; tickets only
  track what is to do and why. Finished work is in git log;
  [history.md](history.md) keeps what the old `TODO.md` recorded as done.

### How a proof lane finishes

A lane that adds or changes theorems (AoC proofs, the roguelike's, std's)
runs `stitchwort audit` on the namespaces it touched before it reports
(SW-912, D2040), from the project folder: `stitchwort audit
Aoc.Year2024.Day06`, `stitchwort audit Rogue.Proofs`, or `stitchwort audit
Std.List` for std ([syntax.md](syntax.md#auditing-theorems-stitchwort-audit)).

- A failure (`✗`: an axiom beyond the allowed ones, an unfinished theorem,
  or a counterexample) is fixed before reporting, or listed under "Not
  proved".
- A warning (`!`: hypotheses no input satisfied) is read. If the
  hypotheses really contradict each other, the theorem proves nothing:
  fix its statement, or say so in the report. If they are only narrow (a
  monster at exactly the given cell), say so in a line.
- The report quotes the summary line (`audited N theorems: …`).

`audit` isn't in `task test:merge` yet.
