# Agent-feedback review, 17-25 Nov 2026 (SW-3779)

First review of `docs/agent-feedback/2026-11.md` (D3673): about 540 entries
and items from roughly 370 lane reports. Counts below are entries that
mention the theme (grep, then read; rough). Minutes are only those the
entries state, so they are floors: most entries give none.

## Summary: the top quick wins

1. **Say how to wait** (one line in the three lane agent definitions, fix one
   wrong line in `docs/testing.md`): the most frequent friction, about 100
   entries, every Claude model, still daily on 25 Nov.
2. **`task worktree:new` builds the release binary and clones `tools/fmt`'s
   check cache** (tool, ~20 min): ends "no binary in a fresh worktree",
   "which binary", "package is stitchwort-cli" and the 1.5-6 min cold
   formatter checks (about 70 entries together).
3. **One "where things are" line in the lane agent definitions**: std is
   `crates/elab/src/std`, the CLI package is `stitchwort-cli`, `check` takes
   namespaces from the project folder, a copied binary needs `--std-dir`
   (about 60 entries; most of it is documented, but where lanes don't read).
4. **Brief-writing rules for the orchestrator** (section 4): wrong names,
   untested premises and guessed times are the largest cost by far (about
   180 entries, 280+ stated minutes).
5. **Board: make README item 6 agree with `CLAUDE.md`, commit the board
   before `worktree:new`, add `board note`** (about 45 entries).

## 1. Themes, ranked by cost

| # | Theme | Entries | Models / lanes | Stated min. | Examples |
|---|---|---|---|---|---|
| 1 | **Brief or ticket wrong**: a name, path, flag or test that doesn't exist (~27), a guessed cause (~37), a statement assumed true that was false (~16), a wrong time (~40), a pointer to a removed worktree or unsaved report (~15), a repro already fixed (~7) | ~180 | all; proof and bug lanes most | 280+ | "One reproducer was already fixed when the brief was written … about 20 min proving that" (17 Nov, SW-3770); "brief named `check --timings`, which doesn't exist" (17 Nov, SW-3872); "brief assumed end-of-print facts were exposed (20 min to find they aren't)" (18 Nov, SW-4053) |
| 2 | **Waiting on long commands**: `sleep` refused, calls moved to the background, `&` and stacked Monitors, `pgrep` loops matching other lanes, exit 144 with no output | ~100 | Opus 46, Sonnet 51, Fable 3; build lanes | 86+ (many "polling took three tries") | "The lane started a subagent just to wait for background tasks" (17 Nov, SW-3753); "waiting on builds with Monitor cost ~40 tool calls" (20 Nov, SW-4341); "stacked monitors repeated the same notification about 15 times" (25 Nov, SW-4783) |
| 3 | **Fresh worktree: no binary, cold builds and caches**: no `target/release/stitchwort`, `stitchwort` not on the `nix develop` PATH, first test build 2-6 min, cold `tools/fmt` checks 1.5-6 min | ~70 | Sonnet 30+, Opus | 80+ | "a fresh worktree's first nextest build took 4 min 53 s" (18 Nov, SW-3953); "first check of a new worktree takes ~6 min cold" (19 Nov, SW-4194); "stitchwort is not on the nix develop PATH in a fresh worktree" (24 Nov, SW-4733) |
| 4 | **Choosing tests**: which package and binary a test is in, `EXAMPLES=` vs test names, filters that build all 44 binaries, snapshot recording | ~70 (+~45 snapshots) | Opus, Sonnet | 100+ | "`hash_stability` with `-p stitchwort-driver` builds every driver test target … about 10 min" (17 Nov, SW-3732); "a test:one by name built everything and ran nothing" (22 Nov, SW-4609) |
| 5 | **Shell**: GNU `sed -i ''` (~44), zsh word splitting and unquoted globs (~50) | ~90 | Opus and Fable most | 35+ | "GNU `sed` again … it has come up in four lanes today" (17 Nov, SW-3820); "zsh word splitting broke a namespace-list baseline (10 min)" (21 Nov, SW-4530) |
| 6 | **Where things live**: std path, `check` takes a namespace (not a file) from the project folder, a copied binary can't find std | ~45 | Opus, Sonnet | 25+ | "std lives in crates/elab/src/std, not std/" (20 Nov, SW-4371; again 22 Nov, SW-4593); "A binary copied to scratch cannot find std: briefs must say STITCHWORT_STD_DIR" (24 Nov, SW-4736) |
| 7 | **Board**: which `tickets.json` to write, no append command, tickets filed after the worktree was cut | ~45 | all | 25+ | "the brief told it to use the worktree's board, against board/README item 6" (18 Nov, SW-3969); "tickets filed after the worktree was made weren't on the lane's board" (25 Nov, SW-4770) |
| 8 | **Scripted edits** (python/perl/sed/heredoc) that matched twice, half-applied or did nothing | ~30 | Opus, Sonnet | 40+ | "A Python `str.replace` … matched the same anchor in two existing proofs" (17 Nov, SW-3830); "String-replace edit scripts silently did nothing after cargo fmt reflowed code; use Edit" (24 Nov, SW-4739) |
| 9 | **Syntax slips in probes and reviews** (no crib): `[a: Type]`, `True`/`False`, `n => …`, record eta, `main(): {IO} ()` | ~15 | Fable reviews, Opus | 25+ | "Crib should say record eta needs a brace type … lambdas are `n => …` not `fun`" (23 Nov, SW-4690 review) |
| 10 | **Killing by name** (`pkill -f`, `pgrep -f`) | ~16 | Sonnet 10, Opus 6 | 10+, and one lane's build killed (20 Nov, SW-4434) | "lane ran pkill -f "stitchwort check" … lanes get no "stop only your own PIDs" rule" (19 Nov, SW-4216) |
| 11 | Timing under load (4-84) too noisy; context compaction losing the start time | ~17 | Opus, Sonnet | 30+ | "load 31 made 45 s checks take 9 min" (21 Nov, SW-4559) |

The waiting theme was checked in this lane (25 Nov, as a subagent): a
foreground call with an explicit `timeout` stays in the foreground to about
180 s and is then moved to the background whatever the timeout (130 s
stayed; 200 s moved at 180 s); without a `timeout` the default is 120 s. A
`run_in_background` job's completion notice arrives mid-turn, after the
lane's next tool call, so a lane can keep working or wait in short bounded
loops. `sleep 2` and `/bin/sleep 5` inside an `until` loop both ran; the
block is on long sleeps.

## 2. Quick wins

Instruction changes need Matt's approval; tool changes are tickets the
orchestrator can schedule.

**W1. How to wait** (instruction). In each of `.claude/agents/{sonnet,opus,fable}-lane.md`,
after the "Tests" bullet, add:

> - Anything that may take over two minutes (a first build or test run, a
>   whole-namespace check, `snap:hashes`): start it with the Bash tool's
>   `run_in_background`, output to a log in your scratch folder, and carry on;
>   its completion notice arrives after your next tool call. With nothing else
>   to do, wait in foreground calls of at most 170 s, such as `timeout 170 zsh
>   -c 'until grep -q DONE LOG; do /bin/sleep 5; done'`, repeated. Never `&`
>   inside a call, never a second Monitor or waiter on the same job, never
>   wait on `pgrep` of a name, and don't end your turn to wait: that ends the lane.

In `docs/testing.md` "Running", replace "so give the command a foreground
timeout above 120 s" with "so start it with `run_in_background` (calls over
180 s are moved to the background anyway)". It is the line that sent lanes
the wrong way. SW-3833's "lanes run tests in the foreground" is wrong and
should be dropped from that ticket. Estimate: 5 min.

**W2. Ready worktrees** (tool ticket, Sonnet, 20 min). `task worktree:new`
(`LANE_SETUP`, `Taskfile.yml`) runs `cargo build --release -p stitchwort-cli`
after the cache clones (about 9 s through kache, 72 s cold, per
`docs/workflow.md` "Lane checkouts"), and adds `tools/fmt/.stitchwort`
(325 MB, copy-on-write) to the `aoc`/`games/rogue` loop. Then `docs/testing.md`'s
"A fresh worktree has no binary" becomes one sentence.

**W3. A copied binary finds its std** (tool ticket, Sonnet, 30 min). When the
library isn't found next to the executable, fall back to the source tree the
binary was built from (its `CARGO_MANIFEST_DIR`, if it still exists), and
name `--std-dir` in the error. This retires a rule already documented
(`docs/workflow.md`, "Timing a check") that lanes kept missing: 21 entries,
six after it was written.

**W4. Where things are** (instruction). In the three agent definitions, after
"Work only in the worktree path…", add:

> - Where things are: std is `crates/elab/src/std` (read at run time, so std
>   edits need no rebuild); the CLI is package `stitchwort-cli`, binary
>   `./target/release/stitchwort` (not on the `nix develop` PATH); `check`
>   takes namespaces, run from the project's folder (`cd tools/fmt`), and a
>   std file is `check --std --std-dir crates/elab/src/std FILE`; which
>   package and binary a test is in is `docs/testing.md`, "Features".

**W5. Shell line** (instruction). In `CLAUDE.md` "Lane agents", the sed/zsh
bullet: after "loop with `xargs` or an array", add "; quote globs in
arguments (`--include='*.sw'`), and use the Edit tool for source edits, not
scripts (a script's anchor can match twice or nothing)". GNU `sed` has had
no new entry since the line went in (`4ba6df347`, 23 Nov); zsh globs and
scripted edits still have. To make room, the "Minimal and tactical" bullet
in "Test budget" can lose its load-limit parenthetical (D3542/D3548/D3554,
about 12 lines), which is for the orchestrator and belongs in
`docs/workflow.md`.

**W6. Stop your own runs** (instruction; this is SW-1805, waiting on
D2574/D2576). In the three agent definitions: "Stop your own jobs with
TaskStop or `dev/stop-mine`; never `pkill`, `killall` or `pgrep -f` by name."
`dev/stop-mine` has existed since 7 Nov (`docs/workflow.md`, "Stopping a
lane's own test runs"), but nothing lanes read points at it.

**W7. Board** (instruction plus tool). (a) Rewrite `board/README.md` item 6
to match `CLAUDE.md`: today it says agents point `BOARD_FILE` at the main
checkout and don't commit `tickets.json` from their branches, while
`CLAUDE.md` says commit it on your branch; lanes hit both readings (SW-3969,
SW-3970, SW-4168, SW-4519, SW-4668). Matt or the orchestrator picks one;
I'd take `CLAUDE.md`'s and delete the other. (b) Tool, DeepSeek, 15 min:
`worktree:new` refuses while the main checkout's `board/tickets.json` is
uncommitted (SW-3931, SW-4119, SW-4509, SW-4607, SW-4770). (c) Tool, the
`board note N TEXT` half of SW-4200 (DeepSeek, 20 min); then the agent
definitions' "board edit --body-file replaces the whole body" line becomes
"append with `board note`".

**W8. A probe crib** (doc ticket, Sonnet, 20 min). Twenty lines at the top
of `docs/syntax.md` or the proving guide's §1: a runnable two-namespace
probe project, a `test` block, `main(): {IO} ()`, `[a: Type]` implicits,
`True`/`False`, `n => …`, `≠` vs `== … = False`, record eta needing a brace
type, `import Std (Float)` for a namespace. Review briefs link it.

## 3. Already fixed or stale (don't re-propose)

- **GNU `sed`**: the `CLAUDE.md` line (`4ba6df347`, 23 Nov) stopped it; no entry since.
- **Reading a ticket body**: `board show --body-only` (SW-4349, 20 Nov). Only the append command is missing (W7c).
- **Snapshots for named examples, the `assertion_line` header, `snap:one`**: `docs/testing.md` "Snapshots" and `docs/workflow.md` "Example sweeps" (SW-4682, 22 Nov); `snap:hashes NAME` narrows (SW-4447).
- **Stopping own processes**: the tool exists (`dev/stop-mine`, SW-3786 closed); only the rule is missing (W6).
- **Lane notes conflicting in `tools/fmt/NOTES.md`**: `merge=union` in `.gitattributes`.
- **Seeing a kernel term**: `STITCHWORT_DUMP_KERNEL` (22 Nov). **Big read-backs**: `STITCHWORT_BIG_READBACK` with a source span (SW-4630).
- **Pre-commit hook surprises** (formatting refusals): expected since D3681; `docs/workflow.md` "Pre-commit hook" covers it.
- **`fmt-twin` stale binaries and wrapper paths, toyfmt symlinks**: the toy formatter is deleted (SW-4607) and the twin items are SW-3988.
- **Paper lanes told to move tickets**: `dev/briefs/{design,review}.md` now say never; the remaining fault is in briefs (section 4).

## 4. What the orchestrator's briefs get wrong

Rules for the orchestrator, from the entries that blame the brief. Each
could be a line in `docs/workflow.md` "Writing a brief":

1. **Check every name before sending**: each function, namespace, file,
   flag, task and test filter in a brief is grepped or `--help`ed in the
   lane's base. (`--timings`, `--cache-stats`, `Std.List.Spec`,
   `bareSettles`, `binary(examples)` and `List.memberOfContains` didn't exist.)
2. **Mark guesses as guesses**: a suspected cause says "unconfirmed; first
   show it with a five-line repro on the base". About 37 entries found the
   brief's cause wrong (SW-3728, SW-4182, SW-4480, SW-4661, SW-4773).
3. **A proof brief says "if a statement is false, stop and report"** and
   doesn't assert that a step or fact holds unless a check showed it.
4. **Give a pasteable repro, replayed on the base**: a `.sw` file or command
   and its output, not "see SW-N" or a summary. Replay fuzz cases first.
5. **Times and expected results come from a run, not memory**
   (`target/test-timings.json`, the last report); give each named test's
   duration so the lane knows to background it.
6. **Paste or path the reports and notes a lane needs**: never "see SW-N's
   report" unless it is in `docs/reviews/`; never a path in another lane's
   scratch or a deleted worktree.
7. **Say what else is moving**: lanes editing the same files, and tickets
   about to merge that the lane should wait for.
8. **Never ask for what the lane may not run** (whole-package tests, full-repo
   numbers, `ALL=1`): the verifier measures after merging.
9. **Give clock times**: "started 08:33, report at 09:18, stop at 10:03", so
   a compacted context can still tell (SW-4239, SW-4076).
10. **Write briefs with the Write tool or a quoted heredoc**: an unquoted one
    ate the backticks (SW-4656). Create the scratch subfolder first.
11. **Kind-specific line**: "ticket: none, don't touch the board" for paper
    lanes; the full `package(...) & binary(...) & test(...)` filter for every
    named test; the commit to compare against for "before" numbers.

## Not covered

Entries were grouped by keyword and read, not classified one by one, so
counts are within perhaps 20%. Language, tactic and std friction in the log
(E-RESOURCE bisection, `rewrite` misses, import cycles) is out of scope here;
most of it is on the board already (SW-3984, SW-4198, SW-4208).
