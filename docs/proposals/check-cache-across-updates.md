# A check cache that survives Stitchwort updates (SW-4405)

**Status:** design note, 20 November 2026, for Matt's decision (D3702 asked
for it). Nothing is built. One question, D3703, is at the
[end](#9-decision-for-matt).

It builds on [check-cache.md](check-cache.md) (what exists; D1660: a cache
hit is trusted), [check-cache-key.md](check-cache-key.md) (SW-1753: a
narrower compiler key wins 3 to 4%, a hand-bumped version is rejected;
D2560 to D2562) and [check-cache-trust.md](check-cache-trust.md) (SW-1971:
the three-part contract for replay, D2800 to D2802). It reopens one thing
those notes took as fixed: that an entry is only ever read by the build that
wrote it.

Claims are **[checked]** when I read the code (on `main` at `bc550643d`),
**[measured]** when I ran the command or counted git history, and
**[estimate]** when they are my reasoning.

## 1. In short

**The problem.** A check-cache entry is filed under the fingerprint of the
whole compiler, so every Stitchwort update makes every entry a miss. On
`tools/fmt` that is 428 s and 4.0 GB instead of 2.6 s and 0.8 GB, and it
happens many times a day: 508 commits on `main` in the last ten days
changed something every entry is keyed on [measured, §3].

**The change.** Keep today's exact entries, and add a second, weaker kind of
hit, a **carried-over** entry: one written by another build from the same
source. It is used only when the part of the compiler that decides whether
a proof is accepted (the kernel side, `crates/core`) is unchanged, or after
the kernel has checked its terms again. It is always labelled, and never
used by the gates, the tiers or Overmind's rolling check.

**What it should do.**

- After an update that leaves the kernel side alone (74% of compiler
  commits, and every std-only commit [measured]), the editor and a lane's
  namespace check start warm: about today's warm cost plus whatever really
  changed [estimate].
- After an update that changes the kernel side, a carried entry costs a
  kernel-only re-check: about a fifth of a cold check [measured share: 21%
  on `Syntax.ParseWalk`'s closure], so roughly 90 to 120 s for `tools/fmt`
  instead of 428 s [estimate].
- Nothing carried over can make a false theorem accepted. What it can hide
  is a change in what the elaborator would now produce from the same
  source: a new error, a different warning, or a statement that now means
  something else (§5). In the last ten days at least 92% of elaborator-only
  commits changed no pinned hash in the 721-source snapshot corpus
  [measured, §3], and the full checks that already run after every push
  find the rest.

**The answer to the brief's question** ("is it the statement the source now
means?"): no check short of elaborating again can say. So the design
doesn't claim it. It separates the two questions an entry answers, keeps
the first exact, and labels the second.

## 2. Two questions in one key

A check answers two questions about a unit, and different code decides
each.

| | Question | Decided by | A wrong answer is |
|---|---|---|---|
| **K** | Are these core terms accepted: well typed, terminating, positive? | the kernel side: `crates/core` (checker, evaluator, natives, hashing) and the modes and limits | an accepted false theorem |
| **E** | Are these core terms what this source means: names resolved, implicits and instances chosen, operators and abilities translated, errors and warnings raised? | the parser, the elaborator, the prelude and the library's names | a stale answer, never an unsound one |

The kernel treats the elaborator's output as a suggestion and checks all of
it (check-cache.md §3, core.md "Elaboration": "safe because the kernel
re-checks everything"). So K never depends on which elaborator made the
terms. Today's key folds both questions into one fingerprint, `FINGERPRINT`,
over the driver's whole crate graph (`crates/driver/build.rs`) [checked].
That is why a change to an error message's wording throws away every proof
the kernel accepted.

Three inputs make every entry a miss today [checked, `cache/mod.rs`
`library_keys`, `namespace_cache_key`, `library_interface`]:

1. **The compiler fingerprint**: any Rust change in `driver`, `elab`,
   `core`, `syntax`, `rt`, `js`, `host`, `dev-features`, or `Cargo.lock`.
2. **The library interface**: the core's text and the index of every std
   name. Adding one std lemma changes every key in every project, because
   a new name can make a short name ambiguous anywhere.
3. **A std file's text**: misses the units that load that file.

The second one matters as much as the first: std gets new lemmas daily.

## 3. Measurements

**Which inputs change, and how often [measured].** First-parent commits on
`main` in the ten days to `bc550643d` (3,603 commits, most of them board
bookkeeping), sorted by what they touched. "Kernel side" is the test
cache's existing evaluation fingerprint (`core`, `rt`, `dev-features`,
`driver/src/test_run.rs`, the manifests and `Cargo.lock`:
`fingerprint::evaluation_files`); "elaborator side" is the rest of
`FINGERPRINT`; "std" is `crates/elab/src/std/**/*.sw`. The last column
counts commits that modified an existing `hash_stability` snapshot (the 721
pinned sources: the prelude and the accept and extract examples).

| Touched | Commits | Changed a pinned hash |
|---|---|---|
| Elaborator side only | 306 | 24 (8%) |
| Elaborator side and std | 13 | 9 |
| Std only | 78 | 62 |
| Kernel side (with or without the others) | 111 | 32 |
| **Any** | **508** | |

- Of the 430 commits that changed the compiler fingerprint, **319 (74%)
  left the kernel side alone**. With the 78 std-only commits, 397 of 508
  invalidations (78%) are ones where the kernel that accepted the cached
  terms is, byte for byte, the kernel now.
- Of the 306 elaborator-only commits, **282 (92%) changed no pinned hash**.
  This is a lower bound on how often the elaborator's output is unchanged
  for that corpus (a commit that edited an example's source also counts as
  a change), and says nothing certain about programs unlike the corpus,
  such as `tools/fmt`. The std rows are not informative: adding a lemma to
  the prelude modifies the prelude's snapshot.
- The kernel side changes about 11 times a day. So a checkout updated once
  a day has nearly always crossed a kernel-side change: the kernel re-check
  path (§4, stage 2) is what the editor mostly needs, and the no-re-check
  path is what a lane branching from a recent `main` mostly gets.

**The kernel's share of a check [measured].** `--timings` already splits
elaboration from the kernel (`crates/elab/src/timings.rs`: "kernel ms" is
the time inside the kernel's declare and define calls; conversion checks
the elaborator itself asks for count as elaboration). One run, release
binary, `nice -n 19`, load average 11:

`stitchwort check Syntax.ParseWalk --no-cache --timings=15` in `tools/fmt`:
24.7 s wall, 678 MB, 15,256 declarations.

| Units | Elaboration | Kernel | Kernel share |
|---|---|---|---|
| Library files | 11.8 s | 2.4 s | 17% |
| `Syntax.ParseWalk` | 0.81 s | 0.20 s | 20% |
| `Syntax.LexProofs` | 0.78 s | 0.16 s | 17% |
| `Syntax.ParseProofs` | 0.55 s | 0.15 s | 22% |
| **Everything** | **18.6 s** | **5.0 s** | **21%** |

This agrees with the two older figures: 19% from a sampling profile of
`aoc` (check-cache.md §3, 21 Oct), and stage 2's warm run with the kernel
re-checking, 9.9 s against 35.6 s cold on `aoc` (28%, which includes
decoding and replaying the tables).

**Not measured.** The kernel's share on the whole fmt project (the brief
rules out the 7-minute run; the per-unit shares above are all within 17 to
22%, proof-heavy units included), the memory a kernel-only re-check of the
whole project needs (somewhere between 0.8 and 4.0 GB), and how many std
commits change the name index. Overmind can measure the first two with one
`--no-cache --timings` run of `tools/fmt`.

## 4. The design: carried-over entries

### 4.1 The rule

An entry is found by **what was read** and stamped with **who read it**.

- **Source key** (in the file name, as now): the format, the modes and
  limits, the unit's text, and its dependencies' source keys. The Merkle
  chain is unchanged; the compiler fingerprint and the library interface
  move out of it.
- **Stamp** (in the sealed header): the kernel-side fingerprint, the whole
  compiler fingerprint, the library interface digest, and, as entries
  already hold, the library files a namespace used with their keys and
  every outside declaration it refers to with its content hash.

Reading an entry then gives one of three results:

| Result | When | Cost | Meaning |
|---|---|---|---|
| **Exact** | the whole stamp matches this build and session | as today | this build checked this unit from this source (D1660, unchanged) |
| **Carried over** | the source key matches; every declaration it refers to exists now with the same content hash; and the kernel-side fingerprint matches, or the kernel has just accepted its terms again | a replay, plus the kernel's share if it had to re-check | some build with this kernel accepted these terms from this source; this build's elaborator has not confirmed they are what it would produce |
| **Miss** | anything else, or carried-over entries are off | a full check | |

An entry written from carried-over dependencies is itself not exact until
they are: exactness passes down the chain only through exact entries.
"Carried over" is reported, never silent (§6).

### 4.2 Why this accepts no false theorem

The argument has the same three parts as check-cache-trust.md §1, with the
first one split.

1. **K's inputs are still all covered.** A carried entry's terms were
   accepted by a kernel with this fingerprint, under these modes and
   limits, in an environment where everything they refer to had the content
   hash it has now. A hash covers a declaration's kind, type, body,
   theorem flag, opacity and `unfolding` list, and through references
   everything below it (core.md "Tests and content hashes", "Opaque
   definitions") [checked]. So the judgement the kernel made then is the
   judgement it would make now. What the hash leaves out (names, the `fold`
   flag) can change how much work a check takes, not what is derivable.
2. **The dependency check already exists.** Replay compares every outside
   reference's path and content hash before admitting anything
   (`decode`, `cache/mod.rs`) [checked]. Today the library file keys are
   compared first (`library_unchanged`), which is stricter; carried
   entries rely on the hashes alone. That is the "early cutoff" of D280,
   at the boundary where it pays most: a std commit that adds lemmas
   changes no hash a project refers to.
3. **Undo is unchanged** (`Kernel::forget_since`).

Two things become load-bearing that the whole-build fingerprint made
redundant, and each gets a mechanical guard:

- **The decoder now reads bytes another build's encoder wrote.** `FORMAT`
  is bumped by hand [checked: `FORMAT = 37`]; a forgotten bump was harmless
  while every build had its own entries. Guard: on a carried-over entry,
  hash the decoded declarations and compare with the hashes the entry
  records, instead of seeding the recorded ones as replay does today
  (`admit_replayed`, "What the entry says the declarations hash to")
  [checked]. A term decoded wrongly then misses. This costs one walk of
  the terms, far less than checking them [estimate]. Side tables decoded
  wrongly fall under E: stale, not unsound.
- **The kernel-side fingerprint must cover the kernel.** Use the evaluation
  fingerprint's construction, which takes whole crates from the manifests
  and has a test against the crate graph (`fingerprint.rs`), not a file
  list. It is wider than needed (`rt` is in it), which only costs a few
  extra re-checks.

When the kernel side did change, the entry's terms go through the ordinary
checking calls (`declare_def`, `define_group` and the rest), as stage 2's
replay did before D1660. That is option A of check-cache.md §3: it adds
nothing to the trusted base, so it is sound whatever changed in the kernel,
including a fix that now refuses a term. A refusal is a miss.

### 4.3 The end state

- **One cache, three kinds of answer**: exact, carried over, checked now.
- **A full check heals the cache.** Whenever a unit with a carried-over
  entry is elaborated (a `check` with carried entries off, or `--no-cache`
  made to compare), the fresh entry is compared with the carried one. Same
  bytes: the entry is restamped as exact. Different: the entry is replaced
  and the unit is named in a report line, "this update changed what
  `Fmt.Kinds` elaborates to". That is check-cache-trust.md's verify mode
  (D2802) running on real history at no extra cost, and it is a new
  regression signal for elaborator changes that nothing gives today.
- **`check --recheck`**, the kernel-only pass over a cache, falls out of the
  re-check path: Lean's `lake check` (check-cache.md §A.4).

### 4.4 Stages

1. **Split the key and stamp; carry over when the kernel side matches.**
   Covers 78% of invalidations [measured]. The label in the CLI and the
   editor. The decode self-check.
2. **Kernel re-check for a changed kernel side.** Needed for a checkout
   that updates once a day (§3). `check --recheck` with it.
3. **Healing and the "update changed what X elaborates to" report**; the
   editor re-elaborating carried units when idle.

Stage 1 is useful alone for lanes; the editor needs stage 2.

## 5. What a carried-over entry can hide

All of these are E, and all end when the unit is next elaborated.

- **A new refusal.** The elaborator now rejects this source (a tightened
  rule, a new error) and the carried entry says it is fine.
- **A changed statement.** The source now means something else: an operator
  translated differently, an instance or implicit chosen differently, a
  precedence fix in the parser, a new std name that makes a short name
  resolve elsewhere. The carried theorem is still true, and its proof still
  proves it, but it is the old reading. For a proved tool this is the case
  that matters: a top theorem could be the statement as an earlier
  elaborator read it. No kernel re-check can see it.
- **Checks only the elaborator makes.** Ability rows (`E-ABILITY`,
  `E-EFFECT-ESCAPE`), `E-STD-INTERNAL`, unsolved metavariables,
  exhaustiveness messages, open-goal and unreachable warnings. The stored
  warnings are the old ones.
- **Old behaviour.** `run`, `test` and `build` on a carried unit run the old
  elaboration. Test results are keyed by content hash, so they stay
  consistent with the entry, and equally old.
- **A mixed session.** A unit edited after the update is elaborated by the
  new elaborator against carried side tables (instances, records, scope).
  The result is kernel-checked and sound, but may be one that neither build
  would produce alone, and could show or hide an error only in the mix.
- **The reverse case, a lane changing the elaborator.** A lane that edits
  `crates/elab` and checks a namespace to see the effect would see nothing
  from a carried entry. This is why carrying over is never the CLI's
  default (§6).

**How this sits with check-cache-trust.md.** D2800's contract says a key is
"a hash of every input that can change what checking the unit gives".
Carried-over entries keep that for exact hits, keep it for K on every hit,
and knowingly drop it for E, with a label. The note's "stale but sound"
(check-cache.md §3.2) was a bug to be prevented; here it is a state that is
entered on purpose, reported, and left by the next full check. D1660's
trust in the cache files and the decoder is unchanged, plus §4.2's two
guards.

## 6. Who gets what

| User | Behaviour | Why |
|---|---|---|
| **Editor (LSP)** | Carried over by default. Units carried over are shown as such (a status line: "41 namespaces carried over from an earlier build"). Stage 3 re-elaborates them when idle. | The editor's answer is advice; waiting 7 minutes and 4 GB after every pull is the cost Matt sees. |
| **Lanes' namespace checks** | Opt in: `--carry-over` (or `STITCHWORT_CARRY_OVER=1`, set by the proof lanes' task). The output's summary line says how many units were carried. Lanes that change Rust don't set it. | A proof lane wants its dependencies warm; a compiler lane must see its own change. The verifier and Overmind follow every lane anyway (D3546). |
| **CLI by default** | Exact, as today. | A bare `stitchwort check` keeps meaning "this build checked it". |
| **Verifier, tiers, test suites** | No change: no cache, or exact entries from an empty folder (check-cache.md "The gates still run the kernel"). | They are where E is checked. |
| **Overmind's rolling check** | No change: `check --no-cache` of whole AoC and the roguelike, about an hour behind each push. With stage 3 it could also heal a kept cache and report which units an update changed. Adding `tools/fmt` to its loop is worth a ticket: fmt is the project where a changed statement matters most. | It bounds how long a carried-over answer can be wrong: to the next rolling check. |
| **A user on releases** | Same rule: carried over only by the editor or by request. | A release upgrade is the same event as a commit here. |

## 7. The options, compared

**Option 1: store kernel terms, re-run only the kernel.** Entries already
hold the terms, so this is stage 2's replay path, kept for the case where
the kernel side changed. *Trust:* no false theorem, whatever changed
(option A). It hides everything in §5. *Cost:* the kernel's share, 21%
[measured on one closure]: about 90 to 120 s on `tools/fmt` [estimate].
When the kernel side is unchanged that work is redundant, since the same
kernel already did it. So option 1 alone pays a fifth of a cold check on
every update for a guarantee that 78% of updates don't need. It is the
right tool for the other 22%.

**Option 2: key entries on what each declaration produced.** Computing the
key needs elaboration, which is the 79%; all it can skip after an update is
the kernel, and only where the kernel side is unchanged, which the
kernel-side fingerprint gives without elaborating. As a way to stay warm
across updates it saves at most a fifth. Its real uses are the two in this
design: validating a carried entry by its dependencies' content hashes
(§4.2), and certifying after the fact that a carried entry was exact
(§4.3, healing). It is also D280's early cutoff for comment-only edits,
which is a separate win.

**Option 3: an explicit elaborator version.** check-cache-key.md rejected
the hand-bumped form: "a forgotten bump is exactly a stale cache hiding a
failure". It can be enforced better than that note assumed: the
`hash_stability` snapshots pin the hash of every declaration in 721
sources, so a test could require a version bump whenever a snapshot
changes, and §3 shows that would keep the version still for 92% of
elaborator-only commits. But the enforcement reaches only programs like
the corpus, hashes cover neither diagnostics nor side tables, and std's
name index would need the same treatment. Its entries would have exactly
the staleness of a carried-over entry while being reported as exact. The
carried-over design gives the same speed, needs no discipline, and says
what it is. Rejected again.

**Option 4: hybrids.** The recommendation is one: carried over in the
editor and on request, exact by default, full checks in the verifier and
Overmind. The variant in the brief (kernel-only re-check in the editor on
every update) is option 1's cost without need; the kernel re-check belongs
only where the kernel side changed.

**Option 5: pay the cold check once, somewhere else.** Overmind checks each
pushed commit anyway; it could publish the exact entries it writes, keyed
by the fingerprint, for checkouts at that commit to fetch. Mathlib's cloud
cache works this way (from memory, not checked). *Trust:* none added beyond
accepting entries this machine didn't write (the salt forbids that today,
check-cache.md §3.1). *Cost:* still 7 CPU-minutes per update, and the
editor is cold until it arrives; a lane with its own Rust change never
matches. It complements carried-over entries (it is the healing step done
for you) and is not a substitute. Not proposed now.

**Migration** doesn't count (D2303): the format and file names change, and
every cache starts cold once.

## 8. Risks

- **A carried-over answer is taken for a full one.** The label is the whole
  defence, so it must be in the CLI's summary line, the `--json` output and
  the editor, and lane reports must quote it. Review should treat a missing
  label as a bug.
- **A changed statement in a proved tool goes unnoticed for up to a rolling
  cycle**, or longer for `tools/fmt` until it is in Overmind's loop. The
  milestone checks for proved tools should always be exact.
- **`FORMAT` discipline.** Covered for kernel terms by the decode self-check
  (§4.2); a side-table field read under an old meaning is stale, not
  unsound. A cheap extra: derive the format tag from a hash of
  `crates/elab/src/cache/` so a codec edit always changes it.
- **The kernel-side fingerprint has a hole.** It is built from whole crates,
  like the evaluation fingerprint, so the hole would have to be kernel
  behaviour decided outside `core`. The one such door I found is the
  elaborator choosing which marks to set and which built-ins to bind; both
  are stored in the entry and replayed as written, and built-in binding is
  re-validated on replay [checked]. An Opus review of stage 1 should read
  that door again (it generates kernel state: D2364).
- **Mixed sessions confuse.** An error that appears only with carried
  dependencies would be hard to understand. The fix for the user is one
  exact check; the message for a failing unit with carried dependencies
  should say so.
- **The re-check estimate is from one closure.** If the whole-project share
  is nearer 40% than 21%, stage 2 is worth less; measure before building it
  (§3).
- **Eviction** keeps one entry per unit and source key per build today; two
  builds sharing a folder must not evict each other's exact entries in
  favour of carried ones. An implementation detail, noted so it isn't
  missed.

## 9. Decision for Matt

- **D3703: add carried-over cache entries: used by the editor by default
  and by lanes' namespace checks on request, always labelled, never by the
  verifier, the tiers or Overmind; trusted without a re-check only when the
  kernel side of the compiler is unchanged, and re-checked by the kernel
  otherwise? [rec: yes, in the three stages of §4.4.]**
  - *The problem:* every Stitchwort update, about 50 a day, throws away
    every cached check; `tools/fmt` then takes 428 s and 4 GB in the editor
    and in a lane's first check.
  - *The change:* an entry another build wrote from the same source is
    reused when this build's kernel is the one that accepted it (78% of
    updates, measured) or after the kernel accepts it again (the rest,
    about a fifth of a cold check, estimated 90 to 120 s for fmt).
  - *What it should do:* the editor and proof lanes start warm after most
    updates. No false theorem can get in. What can be hidden until the next
    full check is a change in what the source elaborates to, including a
    theorem's statement; at least 92% of elaborator-only commits changed
    nothing in the pinned corpus (measured), the label says which units are
    carried, and the verifier and Overmind's rolling check stay exact.

Mine, as implementation details: the flag's name, the stamp's layout, the
status line's wording, reusing the evaluation fingerprint as the
kernel-side fingerprint, and the order of the stages.

## 10. Tickets to file, if D3703 is yes

1. **[Overmind, compute]** One `check --no-cache --timings` of `tools/fmt`:
   the kernel's share and peak memory for the whole project. Decides how
   much stage 2 is worth.
2. **[Opus] Stage 1**: source key and stamp, carried-over hits when the
   kernel side matches, the decode self-check, the label (CLI summary,
   `--json`, editor status), `--carry-over`. Opus review (D2364).
   Differential tests: a carried session's kernel dump equals a fresh
   one's when the two builds differ only outside `core` (two stores with
   different stamps stand in for two builds).
3. **[Opus] Stage 2**: kernel re-check of a carried entry; `check
   --recheck`.
4. **[Sonnet] Stage 3**: compare on re-elaboration, restamp or report; the
   editor's idle refresh.
5. **[Sonnet]** Add `tools/fmt` to Overmind's rolling check (a full check
   of the proved tool behind every push), if its 7 minutes fit the cycle.

## 11. What this note doesn't cover

- Making the cold check itself faster (428 s is elaboration-bound; that is
  the performance work's subject).
- D280's early cutoff inside a project (a comment-only edit in
  `Aoc.Common`); §4.2 gives it only at the std boundary.
- Sharing caches between machines (option 5).
- Whether `check --verify-cache` (D2802) is built: `CacheArgs` has only
  `--no-cache` and `--cache-dir` at `bc550643d` [checked], so stage 3's
  comparison would be its first form.
