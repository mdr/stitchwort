# How work gets done

Stitchwort is built by Matt with AI models doing most of the writing. This
note records who does what, so the split stays consistent between sessions
and any model working on the repo can read it. `TODO.md` is the task list.

## Who does what

| Model | Used for |
|---|---|
| **Claude Opus** | Design notes, analysis, anything touching the kernel or soundness, proofs, tricky bugs, writing specs for other models, and reviewing every diff before it's merged. Also orchestrates: hands out tasks, merges, runs the gate. |
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
   gate (below). For playground changes also run `web/build.sh` and
   `web/test.sh`.
6. Update `TODO.md`.

Claude's own lanes work the same way, in git worktrees instead of scratch
clones.

## The gate

Nothing is committed to `main` unless `nix flake check` passes: formatting,
clippy, all tests, the examples and their snapshots, hash stability and the
benchmark baseline. New files must be `git add`ed first, since the flake only
sees tracked files. Long runs (the gate, browser tests, builds) go in the
background.

Pushing to GitHub happens only when Matt asks.
