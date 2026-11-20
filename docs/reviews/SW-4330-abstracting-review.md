# SW-4357: review of lane/SW-4330 (abstracting fallback for continuation arguments)

Reviewer: Opus, paper only (no builds or tests). Read from `git diff main...lane/SW-4330`
(9 commits: `43e328fa7` elab change, then 8 fmt proof files dropping `[j :=][k :=]`).

## Verdict

**Merge after F1**, with F2 and F3 as small follow-ups in the same lane if cheap. The core
argument (abstract *every* occurrence) holds. I found one gap in it: unknowns inside the
other side, which `rename` prunes. That makes the solution a choice, not the only one. It
costs completeness, not soundness, but it is a one-line refusal to close.

## 1. Soundness: can it silently pick an unintended solution?

The kernel checks the final term, so the only risk is choosing a solution that type-checks
but means something different from what the user wrote.

- **When it fires.** Only in `finish_application`, only for a call with lambdas held for
  after the expected type (`after_expected` non-empty) and an `expecting_named`. It fires
  after plain `unify`, `unify_solving_arguments`, `compare_waiting` and instance guessing
  have all failed, which used to be a hard error at that point. So a program that
  elaborated before can change only where a caller recovered from that error. The one such
  caller is `propagate` → `propagate_failed`, which elaborates again without propagation.
  The lane's report of no hash changes across prelude, examples and projects is the right
  evidence that no existing program moved.
- **Is the solution unique?** Take any solution `?m := λx. B`. Then `B` can't mention `v`,
  the variable that `e` uses and `?m` can't see, and `B[x := e] ≡ rhs`. Because `e` is stuck
  on `v`, conversion can't look inside it except through proof irrelevance and eta, and
  both of those identify the candidate solutions anyway. So `B ≡ rhs[e := x]` up to
  conversion, as a function and not only at `e`. That matters for programs as well as
  proofs: `j` is a parser continuation (program-valued), and its behaviour on other inputs
  is fixed. **Except for F1 below.**
- **Typing of the solution.** Like Lean's `kabstract`, abstracting can in general give an
  ill-typed motive. Here the solution must be free of `v` (any other occurrence makes
  `rename` fail), and every in-scope variable's type is free of `v` too (scopes are
  prefixes). So an occurrence whose typing depends on being exactly `e` would need a
  convertible but differently written form of `e` somewhere, and that form still mentions
  `v`, so the solve is refused. I couldn't build an ill-typed case. If one exists, the
  kernel rejects it as an error; it can't be silently accepted.

## 2. Is abstracting all occurrences justified?

Yes, for occurrences written in `rhs`: every occurrence of `e` mentions `v`, and `B` can't,
so each must come from `x`. Keeping some occurrences is impossible rather than a
different choice. The "`v` also occurs outside `e`" refusal is what makes this true, and it
is enforced implicitly by `solve`'s `rename` at `level + 1` failing on `v`, not by
`solve_abstracting` itself (see F3).

**Counterexample class (F1): unknowns in `rhs`.** `rename` prunes another unknown's
dependence on variables outside the renaming (`rename_meta` → `prune`). In ordinary pattern
unification that is complete, because the solution can't mention `v` at all. Here the
solution *can* reach `v`, through `x`. So for

    ?m e  =  F (?n v)          (e stuck on v; ?n made where v is in scope)

there are solutions `?n := λv. G e[v]`, `?m := λx. F (G x)` for any `G`, and also
`?n := λ_. c`. The inner `solve` prunes `?n` to `λ_. ?n3`, which commits to the second
family. It is a guess, not the most general solution. The usual result is a later
mismatch or an unsolved-unknown error, not a wrong term. Still, it breaks the doc
comment's claim that this is "not a choice among several".

## 3. Scope

- **Prop-only or proof positions only: no.** The motivating unknowns `j`/`k` are parser
  continuations, program-valued, so that limit would remove the feature. It also isn't
  needed, since §1's uniqueness argument doesn't depend on proof irrelevance.
- **Unknowns standing for whole arguments only: not needed.** The flag reaches every flex
  pair inside the fallback comparison (hence `?alike := SameBool`), but the uniqueness
  argument is per unknown and holds for each. `solving_arguments` being on is the same
  exposure `unify_solving_arguments` already has one step earlier.
- **Conservative corners (fine, worth a line in the doc).** `solve_abstracting` refuses a
  spine containing a `()` argument or an `ignorable` position, which `solve` would accept.
  It also requires the variables to be distinct, where `solve` drops repeated ones. So
  `?j () e` isn't solved.

## 4. Undo and transactions

- `undo::unify_abstracting` uses `transaction` like its siblings, so a failed fallback
  undoes everything, including unknowns made since.
- Inside it, `solve_abstracting` takes the trail before the inner `solve` and calls
  `undo_since` if either the solve or the re-check fails. The inner `solve` may already have
  pruned (solved) other unknowns, and those are undone too. This is correct.
- Unknowns made by a prune that was then undone stay in the store, unsolved and
  unreferenced, when the outer transaction succeeds. `proof_position` already does the same
  (`solve` then `undo_since`), so this is the established behaviour.
- `Attempt::abstracting` is guard-scoped (`ScopedCell`), added to the `_` lists in all four
  mark/restore destructurings as `solving_arguments` is, and reset on `Err` by the guard's
  drop. The `_once` guard turns it off inside `solve_abstracting`, so the re-check can't
  recurse into abstracting. `call_memo` is cleared for the fallback, so no memo entry made
  under the flag leaks out. Correct.

## 5. Cost

The fallback is one extra whole-type `unify` (memo off) per failing `finish_application`
of this shape. Each flex pair with a stuck argument then also pays for
`quote_as_written(rhs)`, a substring scan of `rhs` (|rhs|·|e|), `abstract_needle`, an
eval, a `solve` and a re-`unify`. The fallback runs only where the call would otherwise
have failed, but in this code base failure paths are hot: propagation trials, then
`propagate_failed`. That is where the "~78 tries per unknown in one file" comes from. Not
blocking, but the lane should record one before/after check time for the heaviest edited
fmt file (`FollowsDeclData.sw`) in the ticket, or in `docs/performance/log.md` if it moves
(D3444).

## 6. Docs

- The proving-guide addition is accurate and well placed.
- The `solve_abstracting` doc comment is good (Lean `kabstract` named, worked example) but
  overclaims uniqueness while F1 is open (F3).
- The example file `examples/accept/continuation-solved-by-abstracting.sw` is clear and has
  its hash snapshot.
- No `docs/core.md` change is needed: the kernel is untouched.
- The fmt proof diffs change proof bodies only. No theorem statement changed, so this is
  not a narrowing (D3688).

## Fixes

- **F1 (before merge).** In `solve_abstracting`, after quoting `hay`, return `Ok(false)` if
  `hay.subterms().any(|(t, _)| matches!(t, Term::Meta(_)))`, mirroring the existing check
  on `needle`. If that stops any of the 8 fmt files elaborating, use the narrower form
  instead: refuse only unknowns whose spine mentions a variable outside `seen`. Then
  re-check the 8 fmt namespaces and the new example.
- **F2 (small).** Add one `examples/reject` case where `v` also occurs outside `e` (for
  example the goal also mentions `m` or `m.left` beside `m.offset`). Expect the old
  mismatch: this pins down the refusal that the all-occurrences argument rests on.
- **F3 (small).** In `solve_abstracting`'s doc, say that the "variable outside `e`" refusal
  comes from the inner `solve`'s `rename`, that unknowns in `rhs` are refused (after F1),
  and that `()` and ignorable positions aren't handled.
- **F4 (note, not blocking).** One before/after check time for `FollowsDeclData.sw` on the
  ticket.
