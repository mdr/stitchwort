# SW-2278: review of SW-2266 (soundness fuzzer keeps the whole file)

Reviewed: `crates/driver/tests/soundness_fuzz.rs` as merged in `eb82c88c5`
(SW-2266) and `c8ac89ddc` (SW-2265), read only. Opus, 7 Nov 2026.

## Verdict

The change is sound. Keeping the declarations after the theorem can't
make a false mutant count as accepted. The only thing that does is the
theorem's own definition reaching `State::Final`, and the kernel gives
that state only when everything the definition refers to is final too
(`crates/core/src/globals.rs:17`). A later declaration that fails
because of the mutant either isn't used by the theorem (so it doesn't
matter) or makes the theorem fail with it (so the mutant counts as
rejected, which is the truth). The no-op check is also sound: two
declarations format to the same text only when their syntax trees are
equal. The counts mean what the report says, with one gap: skipped
no-ops aren't counted anywhere. No high or medium findings.

## Findings

| # | Severity | Confidence | Finding | Size |
|---|----------|------------|---------|------|
| 1 | low | high | No-op mutants vanish from the tally | S |
| 2 | low | high | `examples/accept` files are still cut after the theorem | S |
| 3 | low | high | `outcome_of` counts an accepted mutant with a refused axiom as plainly accepted (older than this change) | S |
| 4 | low | medium | The new comment gives the wrong reason the later declarations are harmless | S |

### 1. No-op mutants vanish from the tally (low)

`soundness_fuzz.rs:1106`: a mutant that `same_after_formatting` matches is
skipped with `continue`, so it's in neither `total` nor any per-kind row.
Mutants are planned up to `wanted` (`count += chosen.len()`, around
line 1050), so a run with many no-ops checks fewer mutants than it asked
for and doesn't say so. Nothing is wrongly accepted; the run is just less
thorough than its line implies. **Fix:** count the skips in `JobResult` and
print "N no-op mutants skipped" in the summary line.

### 2. `examples/accept` files are still cut (low)

`soundness_fuzz.rs:803`: `Home::File` still loads
`text[..decl.start] + decl` and drops everything after the theorem. SW-2266
made the project path keep the rest of the file ("it may use them"), and
std always kept it, but a single-file example whose theorem uses a later
helper still fails its unmutated check and is skipped. It's the same
coverage loss SW-2266 fixed for projects. **Fix:** append
`&site.text[site.decl.end..]` there too; `find_theorem`'s `last()` still
picks the right theorem, since names in one file are unique.

### 3. A refused axiom counts as accepted (low, older than this change)

`outcome_of` (line ~897) looks only at `audit.status == Checked`. An audit
that is `Checked` but has a `Check::Axioms` finding of severity `Fail`
counts as `Accepted`. If its search then finds a counterexample, it is
reported as `SOUNDNESS`, even though the cause is an axiom the user
declared, not the checker. This errs on the safe side: it gives a false
alarm and never hides a real finding. Today it's latent: `aoc/src` and
`games/rogue` declare no axioms, and lemma swaps use qualified names (mostly
std). Whole-file loading makes it a little more reachable, since an `axiom`
after the theorem is now in scope. **Fix:** treat a refused axiom as its own
outcome, or as `Rejected` with a note.

### 4. The comment gives the wrong reason (low)

`soundness_fuzz.rs:828`: "They can't make a mutant check, since only the
theorem itself is audited." The real reason is the kernel's invariant that
a final definition's dependencies are all final, so a later declaration that
fails can't leave a theorem that uses it accepted. Suggested wording: "The
declarations after the theorem stay, since it may use them. They can't make
a mutant check: a definition is final only once everything it uses is."

## The four questions

1. **Accepted and findings.** Sound, from these facts:
   - *A later declaration that fails because of the mutant.* If the
     theorem uses it, the theorem can't be `Final`, so the mutant counts as
     rejected. If it doesn't, the failure only sets `load_error`, which
     `outcome_of` ignores. That's right: the error belongs to another
     declaration.
   - *A cycle:* the theorem uses a later lemma that uses the theorem. Only
     reachable now in a file alone in its namespace. If the elaborator ever
     accepted such a cycle, that would be a real soundness bug, and the
     fuzzer now has a better chance of finding it. It isn't a false result.
   - *Later `test` / `example` / instances / notation.* These are what the
     theorem means in the real project. If anything, cutting them was the
     unfaithful choice, since the theorem could then elaborate differently
     from how it does in the real file.
   - *The search reading later definitions.* It evaluates only what the
     statement refers to, and those must be final.
   - *Budget.* `Limits.work` resets for each operation
     (`budget.rs:349`), so checking the later declarations can't use up the
     search's steps and hide a counterexample.
2. **History.** `git log -S alone` shows only the original fuzzer commit
   (`44fccadd6`, SW-687) and SW-2266. Neither gives a reason beyond the doc
   comment "can be cut after the theorem". The `alone` restriction (cut
   only when no other file shares the namespace) suggests the cut was a
   speed shortcut: cutting a file that other files use would break them.
   Nothing suggests it was there for soundness. The not-alone path always
   kept the rest of the file.
3. **The no-op check.** `stitchwort_fmt::format` refuses anything that
   doesn't lex or parse. It also checks its output: the same tokens apart
   from commas and parentheses, the same comments, and the same syntax tree
   (`equivalence::shape`: the full AST's `Debug` text without spans, so
   names and literals are included). So `format(a) == format(b)` implies
   `shape(a) == shape(b)`. Two genuinely different mutants can't both match
   the original. A mutant that differs only in a comment or in
   layout-neutral whitespace is correctly treated as no change. If either
   side fails to format, the raw text is compared, which never skips a real
   mutant. Mutations never touch comment or string tokens. The fragment
   starts at the declaration with no file context. That only makes
   formatting fail more often, which is again the conservative side.
4. **Counting.** "checked unmutated" is `calibrated`: sites whose original
   wasn't `Rejected`. "mutants" is the mutants actually checked, without
   no-ops (finding 1). "accepted" is `total - rejected`, which includes
   counterexample outcomes. Those also fail the test, so in a passing run
   accepted = searched + unsearched. The "under half checked unmutated" check
   still means what it says, and keeping the whole file can only raise
   `calibrated`.

## Checked and sound

- The SW-2265 skip message: `load_error` is only the first line of the first
  diagnostic. It is printed only on skips and never changes an outcome.
- `first_line` uses `errors[0]` after `errors.first()` has returned `Some`,
  so the index can't panic.
- Std sites: unchanged, and they always kept the whole file.

## Not in scope

This review didn't sweep the 1 Nov whole-codebase review
(`docs/research/rust-codebase-review.md`), because that review has no
finding on this test file. The full code-review template was not used, as
the brief asked for a short review.

## Tickets to file

One lane, Sonnet or DeepSeek, about 30 min. Fuzzer tidy-ups (findings 1-4):
- count and print the skipped no-op mutants;
- keep the rest of the file for `Home::File` sites;
- give a refused axiom its own outcome;
- fix the comment at line 828.

Check: `task test:one -- mutated_theorems_have_no_counterexample` (about
10 s), comparing the summary line with the run before.

No D questions.
