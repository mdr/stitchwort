# SW-4422: review of lane/SW-4409, carried-over check cache stage 1 (D3703)

Fable paper review, 20 November 2026. Branch `lane/SW-4409`, commit
`31eaee168`, read with `git diff main...lane/SW-4409` and `git show`. Nothing
was built or run.

## Verdict

**Merge after named fixes.** The kernel-side argument holds as built: I found
no way for a carried entry to put a false theorem, or a theorem over changed
dependencies, into the kernel. There is one exactness leak (M1), the editor's
label is not actually shown to the user (M2), and three smaller things that
keep the argument from rotting silently (M3 to M5).

## Must fix before merge

**M1. A late miss of a carried entry leaves the session untainted, so what it
then writes is stamped exact.**
`replay_namespace` (`crates/elab/src/cache/mod.rs`) applies the entry's
pre-state before `decode` and `admit_replayed`: `set_library_reach(&pre.needs)`,
`scope.insert(k, Global::Failed, ..)` for each of `pre.early`,
`session.replayed_names`, and `load_needs`. A failure after that is
`Miss::Late`, and the namespace "is then elaborated in what the replay left".
For an exact entry that state is this build's own. For a carried entry it is
another build's (or, when the decode self-check refused it, a mis-decoded
entry's). `carried_anything()` reads only `cache_stats.carried_over()`, which
is counted on success only, so the fresh elaboration over that left-over state
is written with `exact: true`, and no label is printed. A later plain `check`,
the verifier, or anything sharing that cache folder then takes it as exact.
The lane made this path routine: with `library_unchanged` skipped, a library
change under a carried namespace is found in `decode`, which is a late miss.
Fix: taint the session when a `Hit::Carried` replay gets past the early stage,
whether or not it succeeds (a session flag set in the `Miss::Late` arm, read
by `carried_anything()`), and count it for the label. Add a test: carried
entry, late miss (the `fail_replays_late` hook will do), and the entry written
afterwards is not an exact hit.

**M2. The editor's label is a line on the server's stderr, not something the
user sees.**
`Checker::step` does `eprintln!("stitchwort lsp: {note}")`, only when a check
reaches `done: true`. The design Matt approved says the editor's carried units
"are shown as such (a status line ...)" (§6), and the CLI's own comment says
"the label is the whole defence". The server already sends
`window/showMessage` elsewhere (`crates/lsp/src/lib.rs`, lines 462 and 1207).
Send the note to the client (`window/showMessage`, or at least
`window/logMessage`), once per increase as now. If it stays log-only, that is
a D question for Matt, not the lane's call: the editor is the one place where
carrying over is on by default.

**M3. `docs/core.md` still describes the old cache.**
Line 557 says entries are "keyed by the compiler build" and that "the cache
files, their reader and the key are part of the trusted base". The key no
longer has the build; the trusted base now also includes the stamp, the
kernel-side fingerprint's coverage, and the decode self-check. CLAUDE.md
requires the kernel spec to be updated in the same lane as a change to what
the kernel is given to trust.

**M4. The kernel side borrows `EVAL_FINGERPRINT` without saying so where that
fingerprint is defined.**
`crates/driver/build.rs` and `fingerprint.rs` are untouched. They document the
evaluation fingerprint as "only the Rust that decides what a test computes
once its term is fixed", and still say "the check cache keeps the whole-graph
fingerprint above". Someone narrowing it for the test cache (the type checker
and termination checker don't decide what a test computes) would silently
narrow the kernel side. Fix: give the kernel side its own name
(`KERNEL_FINGERPRINT`, equal for now), say in `fingerprint.rs` and `build.rs`
that carried-over soundness rests on it covering all of `crates/core`, extend
`NOT_EVALUATION`'s comment to say why `syntax` is also outside the kernel's
verdict, and add an assertion to the existing coverage test that names
`check.rs`, `termination.rs`, `hash.rs`, `pins.rs` and `registry.rs`.

**M5. No test of the one check the lane removed.**
Nothing tests a carried namespace whose library dependency changed content
with the namespace's own source unchanged. That is the case where
`library_unchanged` is now skipped and `decode`'s hash comparison is the only
defence. The three driver tests change only project namespaces, where the
Merkle key already misses. Add a test: write as another build, change a
library declaration the namespace refers to, carry over, and assert a miss, a
fresh elaboration and (with M1) a non-exact write. Also the reverse: a library
change elsewhere in a file the namespace loads still carries. If the test
harness cannot swap the library, the lane should stop and say so.

## The six questions

**1. Can a carried entry make the kernel accept what it wouldn't fresh? No,
as far as I can find.**
- Every outside reference goes through the header's `deps` (`In::ext_defs`),
  and `decode` requires each path to name one final declaration whose content
  hash equals the recorded one. A dependency without a hash is a miss.
- The hashes of dependencies that were themselves carried are recomputed
  (`hashes_as_recorded`), before the recorded ones are seeded. I checked the
  order: seeding happens after the comparison, and `forget_since` undoes a
  refusal.
- The content hash covers the kind, path, type, body, theorem flag, instance
  flag, opacity and `unfolding` hashes, and for data the sort, parameters,
  auto parameters, `no_eta`, indices, record flag, constructors, implicit and
  braced flags (`crates/core/src/hash.rs`). The marks it leaves out (`fold`,
  `tailrec`, parameter defaults, run bodies) don't change what is derivable:
  `set_run_body`'s doc says a run body never unfolds in the kernel.
- Termination and positivity run inside core's `define_group` and
  `define_data_group`, not in the elaborator, so "a build with this kernel
  side accepted it" does mean those checks ran.
- Dropping `library_unchanged` for carried entries is sound for the kernel.
  What it gives up is elaborator fidelity (the namespace's side tables are the
  old ones against a changed library), which is the labelled state D3703
  accepted.

Two residual points, neither a hole I can exhibit, both follow-ups (F1, F2).

**2. Does `EVAL_FINGERPRINT` cover the kernel's verdict? Yes.**
It covers all of `crates/core` (checker, conversion, natives, `pins.rs` with
the pinned hashes, `registry.rs` which binds built-ins by name, `hash.rs`),
`crates/rt`, `dev-features`, the manifests, `Cargo.lock`, `rustc -vV` and the
target. `syntax` is excluded; core uses it for `Diagnostic`, `Span`,
`SourceMap` and the stack probes only, which can cause a refusal but not an
acceptance. Std core's native bindings are covered by content, not by the
fingerprint: a native is bound only through a pin in core, and replay compares
the bound built-ins with the entry's (`bound_builtins`). See M4 for keeping it
that way.

**3. Can exactness leak? One way: M1.** Otherwise no.
- `usable` gives `Exact` only for this build's own file, with the exact flag,
  this build's stamp and this library interface. `read_others` can only give
  `Carried`.
- The taint is read at write time and `cache_stats` is not rewound
  (`Session::mark` and `rewind` leave it alone), so in the editor it is
  sticky. Per session is conservative, not leaky.
- Every other command never sets carrying over, so `test`, `run`, `audit` and
  `axioms` treat a non-exact entry as a miss and overwrite it with an exact
  one.
- `plan_namespace` skips only on `Hit::Exact`.
- `STITCHWORT_CARRY_OVER` is read only in the `check` arm. It is ambient,
  though: see F6.

**4. Is the label always shown? CLI yes, editor no (M2).**
`report_carried_over` runs on both `check` paths, after errors too. The
"checked N namespaces" line above it is unchanged, and `--index` output
carries no mark (F5). With M1, a late-missed carried entry is also unlabelled.

**5. Is the editor default safe as approved?** For the kernel, yes. The
editor's writes are non-exact once anything is carried, so they can't mislead
the CLI (given M1). As approved it also needs the visible label (M2).

**6. Are the tests sufficient? No.** The four tests cover: used only when
asked, kernel-side mismatch is a miss, tainted writes are not exact, the
editor carries and notes once. Missing: M5 (must), M1's test (must), and the
follow-ups in F3.

## The lane's own risks

| Risk | Judgement |
|---|---|
| Kernel side too narrow (marks, built-in bindings the elaborator chooses) | Sound. Marks are hashed or don't affect derivability; bindings are made by core's registry by name and guarded by pins and the `bound` comparison. Residual: F1. |
| Dropped library-key check | Sound for the kernel; untested (M5); makes late misses routine (M1). |
| Skipping excludes carried entries | Right, and conservative. |
| Self-check only on carried hits | Right: exact entries are this build's own encoder. It has no negative test (F3), and it covers only what the hash covers (F2). |
| Exact taint per session | Conservative. The leak is the late miss (M1), not the granularity. |
| Eviction parsing assumes no `-` in the build prefix | Harmless: the fingerprint is hex; a wrong parse only changes what is evicted. Entries are still matched by the key in the sealed header. |
| Directory-listing mtime race | Harmless: a stale listing is a missed carry, a vanished file is skipped. This build's own entry doesn't use the listing. |

## Follow-ups (tickets, not blockers)

- **F1. Record the core built-ins' bindings in the stamp.** The kernel reads
  some registry entries that have no pin: `Comp`, `FloatLeq`, `FloatLess`,
  `FloatToText`, `NatAddZero`, `NegSucc`, `None`, `OfNat`, `Plus`, `PlusRes`,
  `Rec`, `RecRes`, `SigMap`, `Some`, `Text` (from a grep of `Builtin::` in
  core against `PINS`; not all may matter to conversion). A carried term that
  uses one normally also refers to its declaration, so the hash comparison
  catches a change; that rests on a typing argument, not a check. A digest of
  (built-in, content hash) for the bound core built-ins in the stamp,
  compared for carried hits, makes it mechanical.
- **F2. Extend the self-check to derived fields the hash leaves out.**
  `admit_trusted_data_group` takes `field_sorts` and `field_erased` from the
  entry. A mis-decoded one (the forgotten `FORMAT` bump the self-check exists
  for) would pass. Recompute and compare them for carried entries.
- **F3. Tests:** a negative test of the decode self-check; this build's exact
  entry preferred over another build's when carrying is on; `read_others`
  order; eviction keeping each unit's newest entry; the CLI line with the
  flag and with the environment variable, and its absence otherwise
  (`carried_over_line` has no unit test); a differential run with carrying on
  across a library change.
- **F4. Eviction never drops a removed unit's last entry.** Each unit's
  newest entry now lives for ever, including units renamed or deleted. Add an
  age cap.
- **F5. Label gaps in the CLI:** `--index` output from a carried session is
  unmarked; "checked N namespaces" could say "(M carried over)" on the same
  line.
- **F6. The environment variable is ambient.** If a task or shell exports
  `STITCHWORT_CARRY_OVER=1`, a verifier or tier run started from it carries
  over, with only a stderr line to show it. Have the verifier and tier tasks
  unset it, or drop the variable in favour of the flag.
- **F7. `read_others` cost:** `names()` clones the whole listing per lookup
  and every miss filters all of it. Index the listing by unit.
- **F8. Other docs:** `check-cache.md` and `check-cache-trust.md` still
  describe the build as part of the key.

## What I did not check

Nothing was run. I did not read `options.cache_key()` (I took "modes and
limits" on the design's word), the `LibraryBundle` path beyond its `Store`
defaults, or how assumptions are replayed. The unpinned built-ins list in F1
is from a grep, not from reading each use.
