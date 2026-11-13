# SW-3087 review: building a test fact from a proof of its reading (D3549a)

Opus review lane, 13 Nov 2026, of `lane/SW-3087` (4 commits on
`0cefba183`: `1dff2c3d0`, `8e5f1f3a3`, `2bb37bd19`, `b5c88d1c7`). Read:
the whole code diff (`build.rs`, `reading::candidates`, `compare_failed`,
`lambda_not_function`, `with_local_retries`/`local_retries`, `Decl.builds`,
`Options.build`, `Detail.build`, hover), the design note and its "As built"
section, SW-3105, the parent note's §5/§6.6, and the surrounding code the
retry interacts with (`Attempt::reset`, `branch_errors`, `undo::Snapshot`,
the queue's resumed comparisons, the error frames). Probes were run on the
lane's release binary (`target/release/stitchwort` in the worktree), some
also on main's; files in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3087rev/`.

## Verdict

**Merge with fixes.** The mechanism is the careful one the design asked
for, and I found no way for it to change a program that checks today, or
to make a failing program check with a meaning nobody wrote. Two
diagnostics problems in declarations with several failing `match` arms
should be fixed before merging (M1 is a small change; M2 can be the same
change). The rest can be follow-ups.

## Soundness and meaning

- **Every build is kernel-checked**, and is the reading's `backward` (or
  `Decidable.toBoolOfNot (Bool.decTrue e) p`) applied to the user's term,
  so a build can only prove the expected fact; the question is only
  whether it can pick an unintended route. I found none.
- **The retry fires only on the recorded mismatch at that span.**
  `build::again` (`build.rs:321`) reads `Detail::build` off the error the
  attempt returned, and nothing else. The field is set in exactly two
  places: `compare_failed` (`check.rs:6134`, after every other step in
  `compare` failed) and `build::lambda` (`build.rs:302`). The queue's
  resumed comparisons build their mismatch with `cx.mismatch` directly
  (`queue.rs` `Failure::…` arm), so postponed failures carry no field, as
  designed. Error frames that rebuild a diagnostic lose the field (a missed
  build, never a wrong one).
- **State between rounds.** Each round starts with `clear_metas` (metas,
  queue, obligations, drafts, defaults, local dictionaries: the same reset
  the existing local-definition retry relies on), `local_keys` cleared,
  and `build::start_attempt` clearing `made` and `reads`. Navigation
  records roll back with marks (`Logged`), so a build undone inside a
  speculative attempt leaves no hover. The one per-attempt table that is
  *not* reset is `branch_errors`, which is M1. The probe below also showed
  the `--index` output (types, hovers, goals) of
  `Aoc.Year2024.Day15` byte-identical with `STITCHWORT_BUILD=0` and `=1`.
- **Can a retry's build change a choice made elsewhere (x13 mirrored)?**
  Everything before the first build in round *n*+1 replays round *n*
  exactly (same state, deterministic), and everything after it is new
  ground round *n* never reached, so no choice that "checked" before is
  overturned. The one theoretical hole is that a permission is keyed on
  the **span alone** (`allowed.contains(&at)`, `build.rs:150`): in the
  retry, *every* failing comparison at that span builds, including a
  speculative one that round *n* recovered from by a fall-back (record
  update `records.rs:1182`, the `cases` body tried before splitting,
  `cases.rs:357`). For that to matter, the same span must be compared
  twice, against two test facts, with a fall-back between. I couldn't
  construct it (`p10_record.sw`: the x13 update stays `x ∈ xs` when a
  *later* `let` in the same declaration builds; lane accepts, main errors
  only at the later `let`), and in `cases` it only changes which proof
  closes a case. L4 suggests a cheap hardening.
- **Several errors in one declaration.** Sequential code reports one
  error at a time, and the retry handles it: `Both m (Nat.leRefl x)` builds
  `m` and reports only the real error (`p2`), and with the real error first
  `m` is never reached (`p3`). `match` arms are where it goes wrong: M1, M2.
- **Recursion and mutual groups** check (`p6_recursion.sw`,
  `p7_mutual.sw`): the retry is per body inside `group`, and
  `retype_total`'s re-run starts a fresh build set. Builds under implicits
  (`p8`), as an explicit `auto` argument (`p9`), and lambdas in `match`
  arms against an `if`-shaped fact (`p9`) all check.

## "Programs that check today are unchanged"

From the code: `build::build` returns at once unless the span is in
`allowed`, which is empty in every first round (`with_local_retries`
takes the outer set and starts empty) and only grows from a failed round.
So a body whose first round succeeds never builds. What does run on
success paths is `build::site` and `build::lambda`'s candidates, on every
*speculative* failed comparison against a test fact (inside `auto`,
`cases`, fall-backs). They:

- unify only under a `Snapshot` that is restored (`build.rs:121`);
  `reading::read`/`candidates` take `&Ctx` and make no unknowns;
- only add a note or the `build` field to an error that is then dropped.
  No caller that recovers decides by those (the only note-reading caller,
  `numbers.rs:603`, looks for "because of the literal");
- cost evaluation steps. Measured: `check --no-cache Aoc.Year2021.Day09`
  5.67 s off / 5.44 s on, `Aoc.Year2024.Day15` 5.80 s / 5.70 s (noise).

Residual leaks, both Low (L5): `site`'s `?`s can turn the mismatch into a
different non-fatal error (from `candidates`/`quote_folded`), and the
unify inside `fitting(keep = false)` swallows a fatal error
(`matches!(unified, Ok(true))`, `build.rs:125`): out-of-budget there is
read as "doesn't fit" and the budget error surfaces later, if at all. And
the work counts against the step budget, so a declaration at its limit
could tip over. The Overmind switch run (§5.1 oracle 1) is the real test
of this; nothing here argues against running it.

## Cost

A body with *k* sites is checked *k*+1 times on its first (uncached)
check and on every edit of it in the editor, capped at 9 checks. Each
round re-checks the whole body, `omega`/`auto` calls included. For
`match` arms this is needlessly serial: every arm's mismatch is visible in
round 1 (in `branch_errors`), so allowing all of their sites at once would
make it 2 rounds (fits with the M1/M2 fix). For sequential code (`Both a
(Both b c)`) *k*+1 is inherent to form R. `p12_eight.sw` (8 builds)
checks instantly; a long proof with 5 builds will be 6× slower to check
the first time. Acceptable for now; the design's "seed the set across
edits" idea is the follow-up if the editor feels it.

## Findings

### Medium

**M1. Stale `branch_errors` from an earlier round are reported as errors
at places that now build.** `local_retries` (`lib.rs:2706`) doesn't reset
`attempt.branch_errors` between rounds, and `Attempt::reset` leaves it to
"the declaration's code". A round that fails in one `match` arm pushes the
other bad arms' errors there; the next round, where some of them build,
pushes again; when the declaration finally fails, `group` reports the
whole list (`lib.rs:2999`), so arms that *did* build are reported as
mismatches of exactly the kind the feature accepts.
Repro (`p1_arms.sw`):

```
theorem arms (k: Nat) (x: Nat) (xs: List Nat) (ys: List Nat) (m: x ∈ xs) (n: x ∈ ys): xs.contains x := match k with
  | 0 => m
  | 1 => m
  | _ => n
```

reports the real error at `n` and also `| 1 => m`: "expected
`xs.contains x`, but this has type `x ∈ xs`" (`p1b_arms.sw`, with three
building arms, reports two of them). Fix: note
`branch_errors.len()` on entry to `local_retries` and truncate to it at the
start of every round (it also protects the existing preadmit retry, which
has the same exposure).

**M2. A build site that isn't the first error is reported as a plain
mismatch, with no retry and no note.** Only the returned error's field is
read; the other bad arms' errors keep their field and are reported as
they are. Repro (`p1c_arms.sw`): `| 0 => k` then `| _ => m` reports the
`k` error, whose note says "a proof of `x ∈ xs` is accepted here", and
then `m: x ∈ xs` refused with a bare mismatch. Fix (one of): in `again`,
also add every build site found in `branch_errors` (then retry; this is
also the 2-round speed-up above), or at least give a reported error that
still carries a field the note "a proof of this is accepted here once the
other errors are fixed". The first is better.

### Low

**L1. The `.read` guard matches by end position, so a call whose last
argument is `h.read` is refused, with a wrong note.** `is_read`
(`build.rs:65`) compares only `end`. Repro (`p4_call_read.sw`):
`xs.contains x := idMem x xs h.read` (with `idMem: x ∈ xs → x ∈ xs`) is
refused with "`.read` gives the proposition … give the proof of `x ∈ xs`
itself", though the term is a call, not a `.read`. Record the whole
`.read` expression's span (receiver start to field end) and compare both
ends. (The guard is syntactic either way: `let r := h.read; r` builds,
which I think is fine and the design's intent.)

**L2. "(by by its decision)".** `described` (`build.rs:160`) wraps
`Found::last` in "(by …)", and `last` already says "by its decision" for a
decision. Seen in an error note (`p13_decision.sw`): "builds the test fact
`(x == y) = False` from a proof of `x ≠ y` (by by its decision)"; hover
shows the same string. Make `last` return the bare phrase or special-case
it.

**L3. `rfl` is never built only because bare `rfl` never reaches
`compare`; `is_refl` is practically dead, and an ascribed `rfl` builds.**
`(rfl: b = b)` against `(b == b) = True` checks (`p11_refl.sw`). That's
harmless and arguably right (the user wrote the equation's type), but the
docs (syntax.md: "never from `rfl`") overstate it, and
`reject/build-refl.sw` fails with `E-REFL` from `check_value`'s own `rfl`
arm, so it doesn't test the guard. Either drop `is_refl` and say "bare
`rfl`" in the docs, or make the guard see through ascriptions; not worth
much either way.

**L4. Permission keyed on span alone** (see "Soundness" above). Cheap
hardening: store the expected fact with the span (as shown text, or keep
the `Candidates.fact` and compare with `conv`) and build only where the
expected fact matches the one the failure named.

**L5. Success-path residue in `site`** (see above): a non-fatal error from
`candidates` replaces the mismatch; a fatal error inside `fitting`'s
undone unify is swallowed. Make `site` infallible except for fatal errors
(`undo::fatal`), returning `Site::Nothing` on anything else, and propagate
a fatal from the undone unify.

**L6. Messages show the fact normalised, not as written.**
`reject/build-compound.sw` writes `x < 3`; the note says "the test fact
`(xs.contains x && x <= 2) = True`, which reads as `xs.contains x ∧ x ≤
2`". Mixed `<=`/`≤` and a changed literal. Cosmetic; same printer as the
existing `.read` notes.

**L7. `made` isn't rolled back with a speculative attempt.** A build inside
an attempt that is undone stays in `made`, so a later error at that span
can get "here, the compiler builds …" for a build that isn't in the final
term. Only affects a note.

## Tests

- `accept/build-from-reading.sw` proves the rule: with
  `STITCHWORT_BUILD=0` it has 17 errors, with the build none. It covers
  every row of §1's table, two layers, the lambda forms, the plain
  candidate and five builds in one theorem.
- `accept/build-keeps-meaning.sw` is a real oracle for over-building:
  under a direct step (form D) the x13 update would keep its old type and
  `let member: x ∈ xs := again.why` would fail.
- Rejects: `build-after-read`, `build-cap` (cap note on the ninth),
  `build-compound` (the `Both` note), `build-second-branch` (asks for
  `.read`) each fail as described. `build-refl` doesn't test the guard
  (L3). Missing: a reject with several `match` arms (M1/M2), and an accept
  with eight builds (I checked `p12_eight.sw`: it checks).
- Hover test `hover_on_a_term_a_test_fact_was_built_from` read, not run.

What I ran (lane binary, one at a time, `nice -n 19`, `--no-cache`): the
probes `p1`–`p15`, the five reject and two accept examples, `--index` of
`Aoc.Year2024.Day15` with the switch off and on (identical), and timings
of `Aoc.Year2021.Day09` and `Aoc.Year2024.Day15`. `p10_record.sw` also on
main's binary.

## Before merging

1. M1: truncate `branch_errors` to its entry length at the start of each
   round in `local_retries`.
2. M2: in `again`, also allow the build sites carried by `branch_errors`
   (or note them); add a reject example with two building arms and one
   real error, whose snapshot shows only the real error.

L1 and L2 are a few lines each and could go in the same fix-up; L3–L7 can
be filed.
