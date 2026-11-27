# SW-4955: Fable review of SW-4954 (std's deferred equations in the check cache)

27 Nov 2026. Read-only review of commit `ffb51240c` on `lane/SW-4954`.
Trust decision: D3768 (Matt, 27 Nov 2026: cached equations are trusted as
cached std declarations are, D1660).

**Verdict: sound.** No way found for a replayed segment to admit an equation
the kernel wouldn't have accepted against the same declarations, to be filed
under the wrong definition, or to leave anything behind on undo.

## Why

- **Same statement as fresh.** `equations_pending` and `first_equation_unmade`
  (`crates/elab/src/cache/equations_entry.rs:135-172`) reproduce every early
  return of `ensure_equations_of` (`crates/elab/src/equations.rs:6334-6369`);
  where they say "nothing to make" the fresh function runs, so a divergence
  costs only a miss. Generation's inputs are covered by the key (file text,
  edges, modes), the stamp (core text, index names) and the dependency hashes.
- **Wrong definition.** Exactly one `equations_done` push happens between
  `cache_before()` and the encode, and nothing inside generation calls
  `ensure_equations`, so an honest segment marks exactly its own key; the
  "marks its own key done" check catches mis-filing.
- **Write-set.** The outer-unit `equations_done` push is caught by `GrowVec`'s
  mark diff (`state/tables.rs:489`); everything else is inside
  `in_library_file`'s nested unit.
- **Undo.** Before `admit_replayed` succeeds only the kernel is touched; a
  refusal is undone by `forget_since` plus the owners and paths truncation
  (`cache/mod.rs:4748-4763`). With `library=false` no built-in is bound.
- **`--recheck`, `--no-cache`, carry-over, cancellation, the installed bundle
  (SW-2163), Float primitives (SW-1204)** all checked; `eqs.` units are
  exact-only and never read from the bundle. Not bumping `FORMAT` is correct.

## Findings

1. Performance, not soundness: stores that drop `eqs.` units (`LibraryOnly`,
   `LayeredStore` for the playground and LSP, `BundleStore`, `BundleRecorder`)
   still encode every segment and discard it. *Sent back to the lane.*
2. A segment that encodes but can never replay (changed names or tests) is
   rewritten every warm run. *Sent back.*
3. `equations_lookup`'s comment overstates its guard: a project namespace's
   `Capture` doesn't set `scope.log`. *Sent back.*
4. The pre-checks are a hand copy of `ensure_equations_of`'s and may drift.
   *Sent back as optional.*
5. Replay doesn't check a segment holds only equations (defence in depth).
   *Sent back.*
6. A cached skip can freeze a stack-headroom decision made in a tight-stack
   session: a missed equation in search, never a false theorem. Same exposure
   as equations inside library-file entries.
7. Search sessions could admit equations as stated without decoding proofs: a
   further trust step, Matt's call (SW-4970).

## Not checked

Hermetic generation (assumed, as library-file entries already assume under
D1660); `encode_pass`, `Kernel::forget_since` and `journal.segments_since`
read only at their interfaces; every `Elaborator` field generation might
write (relied on the lane's differential dump test); LSP rewinds after a
replay; whether hidden helper names depend on generation order (a miss, not a
wrong admission, if so).
