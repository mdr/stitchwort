# The trial's promises after rule I (SW-4778)

Paper note, 25 Nov 2026. Since SW-4701 a reference to a final theorem with a
proof is hashed as its interface hash, its statement alone
(`hash::has_interface` = `Def::proof_hidden`; docs/core.md "references to
other declarations"; sealed-theorems.md §3.8 "As built"). This note asks which
parts of the trial's promises and report (`live/trial.rs`, `declhash::compare`,
`trial_cmd.rs`, and the sweeps built on them) still do work. Read from the
code, not run.

## When does a proof edit still move another declaration's hash?

Only where the edited proof is not behind an interface:

1. **A proof written inside a definition** (the definition's own body): a
   structure's invariant field given inline, `Quot.lift f (proof)`, a
   `[decreasing := p]` argument or the proof `auto` finds for one (it sits in
   `f.%step`'s body, so `f.%step`, `f.%go`, `f` and every caller move), a
   `by` block in a computing position's proof argument, a `match` lifted
   from a definition's proof (lifted helpers take the enclosing
   declaration's `theorem` flag, `lift.rs` `declare_helper`, so it is a
   `def`). Example, from SW-4773's fixture: editing `def five: Nat := keep 5
   (Nat.addZero 5)` to `keep 5 (((n: Nat) => Nat.addZero n) 5)` moves `five`
   and `user`.
2. **A `def` whose type is a proposition** (not declared `theorem`): cited by
   its full hash (sealed-theorems.md §3.8 "As built").
3. **A computing definition in a group with a theorem**: the group's hash
   covers every member's body (docs/core.md, "A theorem in a group with a
   computing definition"). Example: a recursive `def f` with a local
   `theorem` about `f`'s recursive call, lifted into `f`'s group;
   re-proving the local theorem moves `f`. [Not verified by a fixture; the
   group rule and the lifting are read from the code.]
4. **A proof that fails** (its stand-in is cited by its own hash). The trial
   refuses it for the new error anyway.

A theorem that gains or loses a `?` does not move its users (the `?` is an
assumption inside the theorem's body; the theorem itself stays behind its
interface). Statements, data types' indices and constructor fields cite
theorems by interface too, so a proof inside a data type's index moves the
data type only when it is case 1 or 2 there.

## Part by part

| Part | Still reached by | Verdict |
|---|---|---|
| `SameMeaning` | renames (`stitchwort rename`, the editor's rename), moves, formatting | keep |
| `SameStatement` | any edit to a theorem's proof; rejects cases 1-2 | keep; the doc's "a theorem that uses another that changed only in its proof has another hash too" is now false (delete) |
| `ProofsOnly` | cases 1-2 (the `oracle readings`/`builds` sites are mostly inside definitions) | keep; its doc's examples ("theorems' proofs that definitions embed") should say "proofs written inside definitions" |
| `proofs_changed` | every `SameStatement` trial that edits a proof | keep; it is now exactly the theorems the edits touched, no cascade |
| `proofs_only` | cases 1-2 under `ProofsOnly` | keep |
| `reproved` | case 3 only, under `SameStatement`. Under `ProofsOnly` it was always a false lead (a changed definition's proofless hash cites accepted declarations by their proofless hashes, which held), and under `SameStatement` it now names any re-proved theorem a definition that moved *for its own reasons* mentions | drop the cone; keep at most "its group holds re-proved theorem T" |
| Binder sweep, `refuse_moved`'s re-proved branch (SW-2690) | case 3 only: the sweep edits theorems, so a definition can move only through a group | drop; refuse a converted theorem in a computing group by group membership |
| Binder sweep, `refuse_changed_proofs` (refuse every re-proved converted theorem when something unexplained moved) | nothing: a re-proved theorem can't be the cause outside case 3 | drop; unexplained movement is a sweep bug, reported with exit 1, not pinned on innocent theorems |
| `sweep theorem-binders --proofs-only` | nothing: the sweep edits only theorems, so it gives the same result as the default | drop the flag |
| `term_diff` first difference | any `ProofsOnly` trial where a definition's computation did change (an oracle site in a computing position) | keep; rule I doesn't touch it |
| `uses` (another changed declaration it mentions) | any trial with two changed definitions | keep |

## Who uses the trial

No doc, `.claude/` file, `dev/briefs/` brief, script or Taskfile task calls
`trial-edits`; it appears in four tickets (SW-2669, SW-3126 open; SW-4754,
SW-4770 done) and in reviews. The promises are used by:

- `stitchwort rename` and the editor's rename (`SameMeaning`,
  `driver/rename.rs`);
- `stitchwort sweep theorem-binders` (`SameStatement`, optionally
  `ProofsOnly`; SW-2655, SW-4571);
- `stitchwort oracle readings|builds` (`ProofsOnly`; SW-3111's corpus);
- `stitchwort trial-edits` itself, for lanes checking an edit by hand.

## Recommendation

Simplify. Keep the three promises, `proofs_changed`, `proofs_only`, `uses` and
the first difference; they all still do work, and `ProofsOnly` is now on
firmer ground (under rule I the kernel never compares proofs, so a hash
without proofs that held means the checker can't tell the two apart; this
needs the hash to keep a cast's ends, which rule K computes by, as it has
since SW-4786). Delete
the `reproved` cone (`reproved_cone`, the `outside` filter, `reproved_all`
in `declhash::compare`, the field in `ChangedMeaning` and `HashChange`, the
JSON key), the sweep's two refusal-by-proof paths and its `--proofs-only`
flag, and the false sentence in `SameStatement`'s doc. Replace the cone with
one direct check for case 3 (a changed definition whose group holds a
re-proved theorem names it), after a fixture confirms case 3 is reachable;
if it isn't, nothing replaces it. Delete
`a_definition_that_mentions_a_reproved_theorem_names_it`, which can no
longer fail.

A further option, not recommended here: hash references to *definitions*
without their proof positions too, so case 1 would move only the edited
definition, not its callers. That is an identity question (pins, the test
cache, the check cache) for its own note.
