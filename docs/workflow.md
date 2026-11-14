# How work gets done

Stitchwort is built by Matt with AI models doing most of the writing. This
note records who does what, so the split stays consistent between sessions
and any model working on the repo can read it. The kanban board in `board/` is the task list (see [board/README.md](../board/README.md)).

## Who does what

| Model | Used for |
|---|---|
| **Claude Opus** | Design notes, analysis, anything touching the kernel or soundness, proofs, tricky bugs, writing specs for other models, and reviewing every diff before it's merged (and, for changes that generate kernel terms or touch proofs, a dedicated review). Also orchestrates: hands out tasks, merges, runs the test tiers. |
| **Claude Sonnet** | Work near the kernel or proof generation, tasks where generality and design judgement matter, changes across several crates where a wrong guess would spread. |
| **DeepSeek V4.1 Flash** (via OpenCode Go) | The default for well-bounded tasks up to medium difficulty, from a goal-level brief: diagnostics, small features, elaborator changes with a clear goal and a repro, and mechanical work (renames, sweeps, boilerplate, new tests). |
| **GLM-5.3-Flash** (via OpenCode Go) | Fallback when DeepSeek is unavailable. |
| Local model (Ollama) | Offline fallback only; about 20 times slower. |

The aim is to spend Opus on the hard reasoning and hand everything else to
cheaper models. The split is provisional (D2208, 2 Nov 2026): it comes from
SW-1084, where DeepSeek and Sonnet got the same goal-level brief for an
easy, a medium and a hard task. DeepSeek's code matched Sonnet's at every
level; its failures were in process (a backgrounded build that ended its
one-shot run, a test it never ran), which three standing lines in its
brief now cover (`CLAUDE.md`, "Choosing the model"). Each closed task's
ticket records how the model did, and the split is looked at again after
about ten more.

## Significant designs

A design that changes the language goes in a note under `docs/proposals/`,
researched against how other languages do it. Matt decides the open
questions, an independent reviewer reads the note, and only then does
implementation start, usually in stages.

## Paper lanes

A paper lane reads code, docs and the web, and writes one document; it runs
no builds, tests, benchmarks or long commands, so it adds no load to the
machine (D3343). Design notes and code reviews are paper lanes. Their shared
rules are in [`dev/briefs/design.md`](../dev/briefs/design.md) and
[`dev/briefs/review.md`](../dev/briefs/review.md): a lane brief points at the
right one and adds the task, the time estimate and the D number range.
Change those files rather than retyping rules into briefs.

Paper lanes are how idle slots get filled: while a heavy job (the broad
tier, a long build) holds the machine, or whenever a slot would otherwise
wait, pick a design note, a review of recent merges, a literature survey or
a friction synthesis from the backlog (Matt, 6 Nov 2026: "we can do a lot
with analysis-only [lanes]: doing designs or code review or literature
review"). They run beside the build lanes, not in place of them: with spare
weekly capacity Matt asked for one or two Opus paper lanes to be kept going
alongside (7 Nov 2026). How many is a matter of the week's quota, so ask
when it's unclear.

## Handing a task to DeepSeek

1. Make a scratch clone with no git remote, so the model can't push:
   `nix develop -c task scratch:new -- sw-N`, from the main checkout
   (`.claude/worktrees/scratch-sw-N`; see "Lane checkouts" below).
2. Run OpenCode there in the background with the brief (the command is in
   `CLAUDE.md`, "Choosing the model"). The brief gives the goal, a repro and
   the limits, and says: no sub-agents, no commits; never run a command in
   the background; run `cargo fmt`, clippy and the relevant targeted tests,
   and every test it adds, showing them passing; leave new snapshots
   (`.snap.new`) and benchmark changes for the reviewer; finish with a
   report of each command and its result.
   The brief also gives a time estimate; the run stops and reports at 1.5×
   it, and the orchestrator watches the elapsed time and stops a run at 2×
   that is going in circles (D2216; `CLAUDE.md`, "Choosing the model").
   Run it with `--print-logs`, so its log shows activity, and with stdin
   from `/dev/null`: given an open pipe as stdin, `opencode run` waits for
   it to close and never starts (SW-1097; upstream anomalyco/opencode#59287,
   open on 2.1.4 and 2.2.x). A run that still logs nothing past its server's
   start within 2 minutes has hung some other way: stop it, start it again,
   and record it on SW-1097 (D2217).
3. Opus reviews the diff line by line and reruns the tests it relies on.
   DeepSeek has introduced real bugs before, and once handed over a test it
   had never run, so its own "tests pass" isn't enough. Fixes from the
   review go to the same OpenCode session, which keeps the run's context
   (D2438, Matt, 5 Nov 2026): `opencode run --continue` (or `--session
   <id>`) with the same flags and `</dev/null`, the review comments as the
   message, in the same clone. OpenCode 2.1.4 also has `--fork` on `run`,
   but no `--attach`; messages to a run in progress (`opencode serve` and
   `POST /session/:id/prompt_async`) aren't reliable yet, so don't use them.
4. Commit in the clone with the trailer "Done by OpenCode with DeepSeek V4.1
   Flash (OpenCode Go) from a spec by Claude; reviewed by Claude", check the
   commit author, then fetch and merge into `main`.
5. Regenerate snapshots and the benchmark baseline, stage them, and let the
   batch's check run (below). For playground changes also run `task test:browser`.
6. Update the ticket: move it to done and record the commits (`board/board commit N HASH`, `board/board move N done`).
7. Delete the clone (`rm -rf .claude/worktrees/scratch-sw-N`), only once
   the lane is merged: review fixes need its session.

Claude's own lanes work the same way, in git worktrees instead of scratch
clones.

## Merging

A failed merge must stop everything after it: the board edits, the commit
and the worktree removal all assume it worked. On 6 Nov 2026 two merges
joined with `;` carried on past a conflict: `git commit -qam` committed the
conflict markers as the merge, the second merge never ran, and
`task worktree:rm` deleted both lane branches. The same day a merge piped
through `grep CONFLICT` hid its failure the same way. So:

- Merge with `task lane:merge`, joined to the steps after it with `&&`. It
  refuses a main checkout with uncommitted changes (commit board edits
  first), keeps main's side of a conflict that is only in
  `board/tickets.json`, aborts any other conflict, and exits non-zero unless
  the lane's tip is in `main` afterwards. `task worktree:rm` in turn refuses
  a branch not merged into `main`, or a worktree with uncommitted changes
  (a lane still at work), unless given `FORCE=1` (14 Nov 2026: a merge that
  never started, and a test of the task itself, each cost a lane its work):

  ```
  nix develop -c task lane:merge MSG="Merge SW-N: …" TRAILER="…" -- SW-N \
    && board/board commit N $(git rev-parse HEAD) && board/board move N done \
    && git commit -m "Board: SW-N done" board/tickets.json \
    && nix develop -c task worktree:rm -- SW-N
  ```

- Never pipe a merge's output, and never run `git commit -a` in the same
  chain as a merge.
- Remove a worktree only after the merge commit is confirmed.
- `task worktree:rm -- SW-N` deletes the branch `lane/SW-N` as well as the
  worktree. When the branch must survive (work held back, an optional change
  for Matt), run `git worktree remove .claude/worktrees/SW-N` instead. A
  deleted branch is recovered from the reflog or `git fsck --unreachable`;
  `git branch lane/SW-N` doesn't recreate it, it points a new branch at the
  current `HEAD`.
- A lane that adds examples needs their hash snapshots. After merging one,
  check `git status` for its new `.snap` files; if they're missing, make them
  with `INSTA_UPDATE=always` on the `hash_stability` `examples` and
  `projects` tests.

## Checks after a merge

(D2221, Matt, 2 Nov 2026; batches since D2392, Matt, 5 Nov 2026; D3545
and D3546, Matt, 13 Nov 2026.) The orchestrator merges every reviewed lane
that is waiting in one go, then
starts one background verifier over the batch, a Haiku agent, with a short brief: the merge commit,
the exact commands to run on `main` (`task test:affected` with its
filterset, and for a proof lane `task audit:touched --
<Namespace>` from the project's directory, e.g. `aoc/`), and nothing else.
It runs them one after another, never in the background, changes nothing,
and reports pass, or each failing test with the first lines of its output,
plus the wall time and `uptime` before and after. The orchestrator carries
on meanwhile; lanes that finish close together share one verifier, and the
others wait for the next batch, so the tree doesn't change under it. A
failure becomes a fix for an agent, or the merge that caused it is reverted;
bisecting a batch's merges is cheap while the batch is unpushed. Only one
verifier runs at a time, and none while timing-sensitive work is running.

After each batch the tests run are a selection that fits the change, not a
fixed set (SW-1098; D2255, Matt, 3 Nov 2026). The verifier's budget is about
90 s of tests chosen by what the batch touched: hash snapshots always,
example kinds for elaborator changes, and std's own tests and pins for std
changes. What it misses is caught later by Overmind's rolling broad check,
which runs the quick tier and the whole-AoC and roguelike `check --no-cache`
of each newly pushed commit, about an hour behind, and reports only new
failures with the last passing commit.

1. The verifier refreshes the inventory (`nix develop -c task test:inventory
   -- --junit target/nextest/quick/junit.xml`), which lists every test with
   its profiles and last known time. Times come from nextest's JUnit files;
   each run folds in, the latest wins. `task test:selected` folds its own
   JUnit times as it ends, so the next run cannot overwrite them unread.
2. It works out the selection. `nix develop -c task test:affected --
   --dry-run --range OLD..NEW` (OLD the commit before the batch's first
   merge) does it by rule (`dev/test-affected.toml`; docs/testing.md, "The
   affected-test selection"): a filterset, `EXAMPLES`, an estimate and what
   it cut to fit the 90 s budget, always including the fixed core (core,
   syntax, one AoC day). The verifier takes that as the start and adds what
   the diff needs beyond the rules, following [test-selector.md](test-selector.md)
   with the lane's report and the inventory.
3. It runs the selection: `nix develop -c task test:affected -- --range
   OLD..NEW` as it stands, or `SELECTOR_ESTIMATE=N [EXAMPLES=x] nix develop
   -c task test:selected -- '<filterset>'` for an edited one. Both run `task test:features` and
   `cargo fmt --check`, then nextest as `test:quick` does, and logs a line
   to `dev/selector-log.tsv`.

A batch's whole check is the 90 s selection plus `task audit:touched` for a
proof lane's namespaces, and nothing else. **Push after each verified batch,
with no quick-tier run first** (D3545, D3546, Matt, 13 Nov 2026: "I don't
care about main being broken ... As long as we are going to detect it and
fix it later"). Overmind's rolling broad check reports what the selection
missed, with the last passing commit; main may be broken for a while, and
what it finds is fixed or reverted. Board-only commits wait for the next
push. The inventory is refreshed only when a batch adds or renames many
tests.

Ways a selection has gone wrong before (5-6 Nov 2026), each turning a
two-minute check into six or more:

- Pick test names, not whole binaries or packages beyond core and syntax,
  and look up how long the slow ones took before including them. All of
  `package(stitchwort-web)` pulled in the every-AoC-day test (about 3.5
  min); `goal_index` and `search` single tests take about 350 s under load;
  the lsp memory tests about 30 s each.
- `test(=name)` must match the whole name, module path included: the web
  crate's tests are `project::tests::…`, so `test(=every_aoc_day…)` selects
  nothing. Compare nextest's "N tests run" with what you expected.
- A filter naming a binary that doesn't exist makes nextest fail before any
  test runs, which through a `grep` looks like a pass. Check for nextest's
  Summary line.
- A Haiku verifier saves the estimator's output to a file and greps it for
  `ESTIMATE`, rather than piping it through `tail`.

**After a core-language lane** (record eta, `match`, the kernel), the
verifier may add one whole-AoC and roguelike `check --no-cache` in the
background, if it takes two or three minutes (D2507, Matt, 6 Nov 2026: "two
to three minutes is okay, but not 20 minutes"); it stops at 6 minutes and
reports. Measured 6 Nov: 1 min 10 s on a quiet machine, 2-3 min loaded,
plus the release build. Lanes don't run it; any other wide check needs
Matt's agreement first.

## Lane checkouts

The orchestrator makes every lane's checkout itself, from the main checkout,
and deletes it once the work is merged or dropped (D2193, D2200, Matt,
2 Nov 2026):

| | Make | Delete |
|---|---|---|
| Claude lane | `task worktree:new -- SW-N`: `.claude/worktrees/SW-N`, branch `lane/SW-N` | `task worktree:rm -- SW-N` |
| DeepSeek | `task scratch:new -- sw-N`: `.claude/worktrees/scratch-sw-N`, no remote | `rm -rf` the folder |

- Both start from local `main`, so they have everything committed but not
  yet pushed. Claude Code's own `isolation: "worktree"` isn't used: it
  starts from `origin/main`.
- Both build through **kache**, a compiler cache (in the devShell), set up
  in `.claude/worktrees/.cargo/config.toml`, which the tasks write and cargo
  finds above each checkout. A new checkout's release build takes about 9 s
  once another checkout has built the same code (72 s cold). Build-script
  runs aren't cached, so the driver's build fingerprint is always computed
  afresh. The main checkout doesn't use kache: every merge is built and
  tested without it. The same file switches off two of kache's shortcuts
  (see "kache and stale artifacts" below); `task kache:config` rewrites it
  without making a checkout.
- Both clone the AoC and roguelike check caches (`.stitchwort/`)
  copy-on-write, so a first `stitchwort check` of AoC takes about 3 s, not
  a minute.
- The recipe is in `Taskfile.yml` (`LANE_SETUP`), so it changes in one
  place. Measurements behind it: sccache and a cloned `target/` were tried
  first (66 s and 48 s).

### kache and stale artifacts (SW-2936, 11 Nov 2026)

**What happened.** SW-2932's lane edited `stitchwort-elab`, then built the
CLI, and the driver could not see the new methods: kache had served an
`elab` built from the code before the edit, until the lane cleaned and built
with `RUSTC_WRAPPER=` empty. It was not cargo's fingerprints (a worktree's
`target/` starts empty; `worktree:new` clones only the check caches) and
not a feature or path-remapping mix-up. It was kache's key.

**Cause.** kache 1.0.0 (nixpkgs) has a compile-first path: when it has an
input record for a crate (the list of files the last build read) and the key
predicted from it misses, it runs the compile and only then derives the key,
by hashing the files the compile's dep-info lists, as they are *after* the
compile. A file saved while rustc runs (a lane's editor, on a compile that
took 116 s under load) gives artifacts of the old code stored under the key
of the new content. Every later build of that content, in that checkout or
any other with the same key, is a hit that restores the old code. Upstream
fixed it in 1.1 (kunobi-ninja/kache#1489, "never store a compile-first
result after a source changed mid-compile"): the store gate acted on the
changed-file flag only with `modified_input_guard`, which is off by default.
It showed in kache's event log (`~/Library/Caches/kache/events.jsonl`): the
`elab` entry stored at 20:41 lacked `BrokenTest` (checked in the stored
blob), but its key's `sources` hash was the same as the later builds
that did compile it; four later builds hit it; no pre-pass ran
(`dep_info_runs 0`, about 100 files hashed, not 6,000).

**Reproduction.** `dev/kache-stale-check` (below) does it in 40 s: build
`elab`, edit it, start a build, edit it again six seconds into the compile,
build once more with no edit. On kache's defaults the last build is a
`local_hit` taking 0.2 s and the artifact lacks the second edit. Adaptive
incremental compilation hides the bug in a checkout that has edited the
crate before (it compiles outside the cache), so the check turns it off; the
lane's first compile in a fresh checkout is the exposed case.

**Fix.** `.claude/worktrees/.cargo/config.toml` (`KACHE_CONFIG_SETUP` in the
`Taskfile.yml`) sets `KACHE_DEFERRED_DISCOVERY = "0"`, so a missed key is
re-derived by the dep-info pre-pass before the compile, from the files as
rustc will read them (about 0.5 s per miss), and `KACHE_MODIFIED_INPUT_GUARD
= "1"`, so a result is not stored when a keyed file was written after the
compile began. Each alone made the check pass; both are set. The check fails
on defaults and passes with them.

**Applying it.** The file is shared by every checkout and untracked: run
`task kache:config` in the main checkout (or any `worktree:new`) once after
merging; the next build in each checkout uses it. Entries stored before the
fix stay in the cache; one for a crate name and `-C metadata` (the checkout's
path) that no later checkout shares is harmless, but `kache purge
--crate-name stitchwort_elab` (and the other `stitchwort_*` crates) removes
any. `task kache:check` after changing kache's version or this file.
The real fix is kache 1.1 or later (the nixpkgs one is 1.0.0; upstream is at
2.0.x): when the pin moves, the switches can go, and `task kache:check`
shows whether they are still needed.

**Which results could have been affected.** Only lane builds in checkouts
under `.claude/worktrees` (the main checkout, the verifier and the quick
tier build without kache, so a merged result was never kache's). The
symptom is usually loud (a method or type "not found", as in SW-2932) but a
body-only edit would run the old code with no error. A lane is suspect if it
edited a workspace crate while a build of that crate was running, in a
checkout that had no earlier build of it, and then saw a result that
disagrees with its code. Kache's log keeps the builds with their times
(`kache explain <crate>`, or `events.jsonl`: a `miss` with `dep_info_runs` 0
and `key_hash_hits + key_hash_misses` near the crate's file count was keyed
after its compile); compare each such compile's interval with the lane's edit
times. A clean rebuild with `RUSTC_WRAPPER=` empty is the test of one run.

## The test tiers

Tests run in tiers with time budgets ([testing.md](testing.md#tiers)), so
that most of the time the tests being run are fast ones:

- **lane**, under 10 s: a lane runs `task test:lane AREA=…` for the area it
  changed, and `task test:one -- NAME` for the tests it touched (a bare name
  matches test names only; `-E 'binary(name)'` selects a whole test binary),
  while it works.
- **quick**, under 90 s on a 10-core M1 Pro: `task test:quick`, run by
  Overmind's rolling broad check on each pushed commit (D3546), not per
  batch; a batch's verifier runs a selection instead (`task test:selected`).
- **broad**, long: `task test:broad`, or `nix flake check`
  (`task test:gate`), with Matt's approval or in compute mode: the quick
  tier plus the corpus sweeps on their samples, formatting, clippy, the
  examples and their snapshots, hash stability and the benchmark baseline,
  and `debug-builtins` (the
  `stitchwort-driver` `builtins` test binary, which loads the prelude, built
  and run in the debug profile so overflow checks and `debug_assert!`s are
  exercised; every other check is release).
- **all**, hours: `task test:all`, every test over the whole corpus; paused
  (Matt, 12 Nov 2026).

New files must be `git add`ed first, since the flake only sees tracked
files. Long runs (the broad tier, browser tests, builds) go in the
background.

Before committing, run `stitchwort fmt` on the `.sw` files you touched. The
test `crates/cli/tests/tools/fmt_repo.rs` fails, naming the files, if any tracked
`.sw` file is not formatted. It skips `examples/reject`, `examples/soundness`,
`examples/projects/reject`, `crates/fmt/tests/it/golden` and
`examples/accept/list-literal-layout.sw`, so leave those as written.

The formatter chooses every line break itself, from the code's structure, in
120 columns; you keep only your blank lines and the comments
([formatter-style.md](proposals/formatter-style.md)). A declaration whose
formatted text fails the safety checks stays as written: `stitchwort dev
fmt-tree --verbose FILES` lists them, and the other constructs it has no rule
for.

`stitchwort` is not on the `PATH` inside `nix develop`: run
`nix develop -c task fmt:sw -- web/guide/14-map-set.sw` (which builds first),
or `target/release/stitchwort fmt FILE` after a build. File arguments are
relative to the folder you run it from, never to `--project`, so a "No such
file" for a tour page means the command ran from the wrong folder (SW-2618).

The orchestrator pushes `main` after each verified batch, with no quick-tier
run first (D3545, D3546, Matt, 13 Nov 2026). Overmind's rolling broad check
runs the quick tier and the whole-AoC and roguelike `check --no-cache` of each
newly pushed commit, about an hour behind, and reports only new failures with
the last passing commit. Main may be broken for a while; what it finds is
fixed or reverted. Board-only commits wait for the next push. Lanes never
push.

## Stopping a lane's own test runs

Every worktree builds test binaries with the same names (`target/release/deps/<name>-<hash>`),
and VS Code's `stitchwort lsp` shares the release binary's name. A bare
`pkill <name>` or `killall` therefore also kills the same tests in other
lanes and the verifier in the main checkout (three SIGTERMed runs on the night
of 6 Nov 2026, SW-1774). A lane stops its own processes with
`dev/stop-mine`: it signals only processes whose executable lies under
`<this checkout>/target/` (an absolute-path prefix match) and their
descendants, and prints each one. `dev/stop-mine --dry-run` only lists them;
`dev/stop-mine --tree PID` stops one pid and its children, refusing a pid
whose executable is outside the checkout. A lane never runs `pkill` or
`killall`.

The orchestrator follows the same rule when it pauses or stops a run: it
selects the run by its process tree (the background job's pid and its
descendants, `pgrep -P` recursively), never by the binary's path. Matching
`target/release/stitchwort` also matches the language server that VS Code
runs from the main checkout (`stitchwort lsp`, `stitchwort.path` in
Matt's settings): on 3 Nov 2026 pausing a broad run that way froze Matt's
editor for about 55 minutes and then killed its server (SW-1110). Check the
list before signalling. In zsh, `kill $pids` doesn't split a
newline-separated variable; use `xargs`.

## Lanes and the task list

Work runs in lanes (up to three at once), each in its own git worktree and
branch ("Lane checkouts" above), merged into `main` in batches (with one verifier over each batch).
The main session orchestrates: it chooses lanes, hands each to a background
agent, then reviews, merges and keeps the board up to date. Agents move their
own tickets as described in [board/README.md](../board/README.md).

- Agents rename a local, hypothesis, function or theorem with
  `stitchwort rename` ([syntax.md, "Renaming"](syntax.md#renaming-stitchwort-rename)),
  not by search and replace: it edits every use, checks that no meaning
  changed, and writes nothing if it did (`--anyway` to fix by hand).
- Lanes that change performance run the benchmarks before merging
  (`nix develop -c cargo run --release -p stitchwort-bench`) and record an
  intended change with `-- --update`, saying why in the commit. The
  deterministic counts are checked by `nix flake check` (+10% fails).
  For native-code speed, `task bench:instructions -- --save before`, then
  `-- --against before` after the change, compares instructions retired
  over repeated runs (a steady measure under load).
- A lane that proves theorems is told to read
  [proving-guide.md](proving-guide.md) first: its rules (never weaken a
  statement, prove against a spec in the problem's words, report "not
  proved" honestly), workflow, tools, common errors and performance traps.
  A lane brief that hands out proofs links it.
- A lane that writes or reviews docs or comments follows
  [syntax.md, "What to write"](syntax.md#what-to-write), and its brief
  links it. The standard library is documented in full, and application code
  only where the code can't say it. A brief never asks for higher coverage
  outside std.
- Significant design decisions (soundness, the kernel, language semantics)
  get a design note in `docs/proposals/` first, researched against the
  literature, and wait for the user (and possibly an external reviewer)
  before implementation.
- Questions for Matt in a session get a D number (D1454, D1455, …),
  counting up from the highest in use so each is unique. D numbers are
  handles for the session's open questions, not a permanent record: the
  answer goes on the SW- ticket it concerns. Which questions are his, and
  how many to bring, is under "Decisions" below.
- New findings become tickets in `backlog` (label `bug` for known issues),
  not straight into `next`, unless they block what's in progress.
- Design detail lives in `DESIGN.md` and `docs/proposals/`; tickets only
  track what is to do and why. Finished work is in git log;
  [history.md](history.md) keeps what the old `TODO.md` recorded as done.

### Writing a brief

Every brief states the worktree, the estimate and the targeted tests (CLAUDE.md,
"Test budget"). Some kinds of work also need standard lines, each added after a
lane missed it and a batch failed:

- **May add examples:** "new examples get a hash snapshot: `nix develop -c
  task snap:hashes NAME=<the example's file stem>` (comma-separated for
  several), and run `task test:one -- -E 'binary(library) & test(/hash_stability/)'`". `NAME`
  filters example file names, so it's the stem, not `examples` or `prelude`
  (5 Nov 2026: SW-1359, SW-1379, SW-1420; a name matching nothing now fails,
  SW-1440). For a std change, "commit the regenerated prelude snapshot
  (additions only)" (SW-1494).
- **Changes std core** (Int, Nat, Text, Char, Bool definitions or lemmas):
  "run `task test:one -- -E 'test(/bound_to_the_prelude/)'`
  (about 20 s); if it fails, check the computation is unchanged and repin
  the hash in `crates/rt/src/natives.rs`". Natives bind by content hash, so
  editing a definition or anything it depends on unbinds one with no build
  error: on 6 Nov 2026 SW-1558 made an `Int` lemma's arguments implicit and
  `DecEqInt` silently stopped binding (SW-1582 repinned it; SW-1586 is the
  structural fix). The batch's check includes `test(/bound_to_the_prelude/)` for such
  lanes.
- **Touches comments:** say which rules apply ([syntax.md, "What to
  write"](syntax.md#what-to-write)): std's full API docs, or application
  code's few comments. Never "document every X" outside std. Lanes keep
  writing comments that narrate the next line or the change, so review
  diffs for them.
- **Speed work** (an optimisation, a measured attempt, or a profile that drops
  or keeps one): "add an entry to `docs/performance/log.md`: the problem and
  the profile evidence for it, the change, why results stay the same, the
  measurements (instructions on the benchmarks it touches and the `bench:aoc`
  geomean), what was rejected or dropped and why, and links to the ticket,
  commits and notes". Dropped attempts and accepted regressions get entries
  too, so they aren't tried again unknowingly. The orchestrator checks the
  entry in review (D3444, Matt, 9 Nov 2026: "say what we did, why, what we
  objected to, dropped").
- **AoC and other application code:** small domain types, forward-reading
  call sites, statements with operators (CLAUDE.md, "Lane agents").
- **A new AoC day** (Opus, D2427) asks for the gap analysis in its friction
  notes: a newcomer's view, and what would have shortened each step.
- **Proofs** link [proving-guide.md](proving-guide.md).
- **Design notes and reviews** point at `dev/briefs/` ("Paper lanes" above)
  and ask for few D questions.

### Reporting to Matt

**Proposals.** For a proposal or D question, three short labelled parts:
**The problem** (what the user does, what happens, and why, in everyday
words), **The change** (what the code will do differently, a sentence or
two), **What it should do** (the effect, with numbers, saying measured or
estimated). Then at most a short "not known yet". Define internal terms or
avoid them; tables come after those parts, if at all. Open a lane proposal
with one line of impact: which real programs or workflows change, by how
much, and whether that's measured. If it's a guess, propose a cheap
measurement first. Matt asked for this after two explanations led with
context, tables and internal terms (4 Nov 2026: "say what the problem is,
and ... what you're proposing the change is, and what you expect the change
to do"), and declined a mechanism-first proposal whose benefit was only
inferred (D2282, 3 Nov 2026).

**Tickets and epics.** Every SW number gets a few-word hint in brackets,
every mention, even one repeated in the same message: "SW-1421 (day 8's
lookup lemmas into std)" (Matt, 5 Nov 2026: "I can't remember what that
is"). Tables of running or finished work have an Epic column, and prose
names the epic once per group of tickets, by its title in
`board/epics.json`, not its id. Status replies ("aw", "where are we") go by
epic, a line or two each (D2517). A summary of a run is organised by the
items Matt asked for, under his names for them ("partial lambdas", "AoC
cleanup"), each with its status first (done, partly, not started); check
every item against the board before saying it wasn't done (5 Nov 2026,
when finished work under ticket names read as not started).

**Active work.** "aw" means a table with one row for every lane running:
the board's `doing` tickets, background agents, DeepSeek runs and
Overmind's jobs. Every table of running work, not only for "aw", has these
seven columns (Matt, 2 and 7 Nov 2026), with nothing around it beyond what's
needed:

| Column | What goes in it |
|---|---|
| Ticket | SW-N with its hint |
| Epic | the epic's title |
| Machine | **Speedwell** (this Mac) or **Overmind** (the soak laptop): "Overmind isn't a model, it's a computer" |
| Model | Opus, Sonnet or DeepSeek; "DeepSeek, then an Opus review" when a review is part of the lane |
| Paper | ✓ for a paper lane (no builds or tests), empty otherwise (Matt, 7 Nov 2026) |
| Running for | measured fresh each time: `ps -o etime=` on a DeepSeek run's opencode process; an agent's launch time, or its worktree's creation (`/usr/bin/stat -f '%SB' -t '%H:%M' .claude/worktrees/SW-N`); an Overmind job's sending time |
| Summary | one sentence |

**Decisions.** The D questions that are Matt's are direction, scope, a
design's end state, trade-offs he can judge (speed against safety, what
ships, what the language does), user-visible language, trust and process.
Sequencing and implementation details inside an approved design, and
technical soundness details inside an approved kernel design, are the
orchestrator's: he has answered such questions "not sure, you decide"
(D2243), "happy to go with your recommendation" (D2260) and "above my pay
grade" (D2352-D2355, 4 Nov 2026). Bring him the user-visible consequence
instead of the mechanism. Record each such call on its ticket as "the
orchestrator's call" and mention it in a line so he can object. Review and
design lanes produce questions faster than he can answer them (about 150 on
7 Nov 2026: "I can't possibly review 80 decisions. Come on."), so take every
reversible, low-risk or within-a-direction question as recommended, and
bring at most one or two a turn, most important first, only when a lane is
about to need the answer. The rest stay in their notes, unlisted. Never
block a lane on a minor call, overnight least of all (4 Nov 2026: "I'd hate
to wake up and discover that you blocked on a minor decision").

**Time.** Before quoting how long a job takes, look it up (a previous run's
log, nextest's timings, `time` on a small run) and allow for the load of
running lanes. If you can't, say so: "I don't know; probably N, I'll stop it
at 2N". Set the stop point up front and keep it. Matt agrees to low-value
work on the strength of the estimate (5 Nov 2026: a "two-minute" baseline
re-record was still running at 25 min).

**Instructions in context.** An instruction usually fits the situation it
was given in (that night, that lane, that file). Unless Matt says "always",
"from now on" or "put it in CLAUDE.md", ask once before keeping it as a
standing rule, and when writing it down, record its context (5 Nov 2026,
after a one-night usage limit was quoted back as a rule: "when I tell you
something, it's probably contextual"). There is no standing usage cap; ask
if usage looks like it matters.

### Keeping the agent list honest

Claude Code keeps listing subagents after they finish. Matt doesn't want to
see zombies (3 Nov 2026), and they make the active-work table wrong:

- Run `ListAgents` after each merge or dropped lane, after a verifier
  reports, after a context compaction, and before any status table. Compare
  it with `board/board list --status doing`: a `doing` ticket with a worktree and
  no agent is a lane that was set up and never launched (SW-1754 sat an
  hour that way).
- `TaskStop` every agent whose result has been acted on (merged, dropped or
  superseded), at once, including those that reported "waiting on its own
  background work", and every background watcher whose job is done. After
  a compaction, stop every completed agent, not only the ones remembered.
- Match an agent's status line by its elapsed time and tokens against each
  agent's usage report, not by its activity text.
- Never stop a lane or verifier still awaited; if one looks stalled, check
  its worktree's commits or message it first. Mention what was closed in a
  line.

### Overmind, the soak laptop

Overmind is Matt's old laptop: NixOS, x86_64, an i7-6700HQ (8 threads),
15 GiB RAM. It runs Overmind's rolling broad check of each pushed commit
(the quick tier and the whole-AoC and roguelike `check --no-cache`), and
long fuzz and soak runs (SW-2100's `dev/soak/run`). Its Claude Code session
shows in `ListAgents` as `overmind`
(Remote Control): `SendMessage` reaches it, and it answers with
`SendMessage` to "Stitchwort Orchestrator". It runs Matt's default model
(Opus as of 7 Nov 2026). Its checkout, `~/repos/mdr/stitchwort`, pulls from
GitHub, so it sees only what has been pushed; the orchestrator pushes after each
verified batch (see "The test tiers").

First soak report (7 Nov 2026): whole-AoC `check --no-cache` 134 s against
65 s on Speedwell (about 2x slower; std's cold check about 4x); an
incremental CLI build 2 min 10 s; 100k syntax fuzz cases 4 s; 2,000 elab
fuzz cases 40 min. Quirks: no `/usr/bin/time` (use Nix's `time`); the
binary is at `target/x86_64-unknown-linux-musl/release/stitchwort`; it has
a desktop session and an existing checkout, so it isn't a clean machine;
its Claude Code moves commands into the background after 10 min; the 16 GB
fuzz memory cap is more than its RAM.

### How a proof lane finishes

A lane that adds or changes theorems (AoC proofs, the roguelike's, std's)
follows [proving-guide.md](proving-guide.md) while it works (§7 there is
what its report says), and runs `stitchwort audit` on the namespaces it touched before it reports
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
- The report quotes the summary line (`audited N theorems: …`, or
  `audited N theorems and M generated lemmas: …` when the compiler
  generated lemmas too).

**At merge** (D2043, Matt, 30 October 2026; trimmed by D2441, 5 Nov 2026): a proof lane's touched namespaces are audited with the search (`task audit:touched -- Aoc.Year2024.Day06`) before it is merged. It isn't inside `task test:quick`, whose 90 s budget the search would break.
