# SW-4367: review of lane/SW-4356 (accessor calls as projections in the abstracting fallback)

Reviewer: Opus, paper only (no builds or tests). Read from `git diff main...lane/SW-4356`
(one commit, `c6490cabc`), against `solve_abstracting` on main and
docs/reviews/SW-4330-abstracting-review.md.

## Verdict

**Merge after G1-G3 (small).** The rewrite is definitional for every term the
structural test admits, except for opaque definitions and definitions with a native
(G2). Even then the re-check against the original `rhs` turns a mismatch into a refusal,
never a wrong solution. The uniqueness argument (SW-4330 review §1, F1-F3) still holds.
The one real side effect: the rewrite also applies to the existing SW-4330 solves, which
are now spelled with `Proj` (G1).

## 1. Is `Proj(D, i, r)` the call, in every case the test admits?

The test admits exactly `λx1..xn. case x_n of C f1..fk => f_j`: `count_lams == args.len()`
(saturated, no over-application), the peeled body is `Case(0, D, [b])` (a case on the
*last* parameter), and `b.body` is exactly a `Var` below `b.names.len()` (a field binder).
So:

- **let, nested match, computed result:** refused. The branch body has to be a bare
  `Var`, so a `Let`, a nested `Case` or any call fails the match.
- **Extra parameters after the record:** refused. The scrutinee would be `Case(k>0, …)`.
- **Non-eta record:** refused (`g.data(d).eta()`), which matches what the kernel's
  `infer_proj` requires.
- **Leading arguments dropped:** sound whatever they are. The branch body can only
  name a field, so the call's value can't depend on them. The doc says they are "types and
  instances". In practice they are, but a hand-written `def g (n: Nat) (p: P) := match p
  with | {a, ..} => a` drops `n` too, which is still correct (G3).
- **Index arithmetic:** `value::branch` binds the fields by pushing them in order (rule 2's
  `eta_fields`), so `Var(0)` is the last field. `names.len() - 1 - field` is right.
- **Conversion:** by record eta rule 2 (`docs/core.md`, "Record eta"), a `case` on a
  neutral record of an eta type takes its only branch with fields `Proj(D, k, n)`, so
  `acc {ps} n ≡ n.i`. There are two exceptions. Rule 2 is off in the case tree of a
  definition with a native (`eta_held`). An **opaque** definition is a rigid head and
  never unfolds. `Def::body()` returns the body for both, so the test admits them, and for
  them the rewrite is *not* definitional (G2).

Why G2 is not a soundness hole: the solution is built from the rewritten `hay`, but
`solve_abstracting` then unifies `?m spine` (the original `e`) with the original `rhs`.
A non-convertible rewrite fails there, and `undo_since` rolls it back. What it can cost is
completeness. An opaque accessor-shaped call *elsewhere* in `rhs`, unrelated to the needle,
is now spelled `Proj` in the solution, and the re-check refuses a solve that main makes.
Rare, and fixed with one line.

## 2. Uniqueness (F1-F3) with a normalised needle and haystack

- **The solution is re-checked against the original `rhs`.** Yes. `unify(g, level,
  ?m spine, rhs)` uses the unrewritten `rhs`, and `spine` holds the unrewritten `e`.
- **The argument carries over.** The SW-4330 argument needs *some* `rhs'` convertible to
  `rhs` in which `v` occurs only inside occurrences of `e`. Uniqueness is a statement about
  solutions up to conversion, so it transfers from `rhs'` to `rhs`. The rewrite produces
  that `rhs'` (when definitional, §1), and the inner `solve`'s `rename` checks the
  "`v` outside `e`" condition on it. The syntactic refusal on main was a sufficient
  condition, not a necessary one.
- **The dropped-argument risk (lane's stated risk).** There are two directions.
  - *Needle side:* `free_levels(needle) ⊆ seen` refuses. Dropping arguments can only
    remove variables, so this check refuses **more**, never less. One example: `acc {T[v]} s`
    with `s` in scope used to pass because of `v`, and is now refused. That is the
    conservative direction. It is also right, because `T[v]` is not really "stuck on `v`".
  - *Haystack side:* this is where more is accepted. Construction: a parameterised record
    `Sized (n: Nat)`, with `Sized.val {0 * m.offset} s` in `rhs`, where `s: Sized 0` is in
    scope. `0 * m.offset ≡ 0`, so this elaborates. Main refuses, because `m` occurs outside
    `e`. The lane accepts, with the solution reading `s.val`. That solution is genuinely the
    unique one, because the only `m` outside `e` sat in a position that conversion ignores.
    So it is correct. The same holds for the F1 "no unknown in `hay`" check and the "no
    unknown in the needle" check: an unknown that sat only in a dropped argument can't
    affect the value, so dropping it doesn't create a choice. One caveat: in the re-check,
    the same-definition shortcut may still unify that dropped argument's unknown with the
    other side's first-order. That is ordinary unifier behaviour, not something this lane
    introduces.
- **The reject example still rejects.** `continuation-abstracting-variable-outside.sw`
  has `m.left` beside `m.offset`. After the rewrite this is `Proj(m)`, which still mentions
  `m`, so the solve is still refused.

## 3. Side effect: SW-4330's existing solves change spelling (G1)

`accessors_as_projections` runs on every call of `solve_abstracting`, not only on the calls
that need it. So every continuation solved on main now has every accessor call in its `rhs`
written as `Proj` in the elaborated term. That includes the 8 fmt files from SW-4330 and
`continuation-solved-by-abstracting.sw`, whose goal has `Parse.mark().left`. The meaning is
the same, but:

- hashes of those theorems may change. The lane's report doesn't mention running
  `hash_stability` for `continuation-solved-by-abstracting` or checking the SW-4330 fmt
  namespaces;
- later goals and `rewrite` motives under those continuations now see projections where
  the user wrote accessors. That worked in the new example and in FollowsFormsBinders, but
  nothing shows it for the other 8 files.

The cheapest end state is to **try the solve as written first and rewrite only on
failure**. Refactor the body after the spine scan into `attempt(normalise: bool)`, and call
it with `false` and then `true`. Main's outcomes and spellings stay exactly as they are,
the extra cost is paid only where main failed, and an `e` that is half-matched (some
occurrences written each way) still reaches the second attempt, because the first one
fails in `rename`.

## 4. Cost

`rewrite_up` rebuilds the whole quoted `rhs`. At each `App` node it calls `spine()`, which
allocates a `Vec`, so a long spine costs its length squared. It runs once per flex pair
with a stuck argument inside the fallback. That is the same order as the `quote_as_written`
and the |rhs|·|e| scan already there, and only on paths that would otherwise fail. Not
blocking. G1's ordering removes it from every solve that succeeds as written. No timing was
recorded. An F4-style before/after on `FollowsFormsBinders.sw` on the ticket is enough.

## 5. Docs and the rest

- `solve_abstracting`'s doc says "generated field accessors". The test is structural, so it
  should say that any definition of that shape counts, generated or hand-written, and that
  the solution is spelled with projections (G3).
- `accessors_as_projections`'s doc: "the arguments before the record are types and
  instances the projection leaves to inference". It should say that they are dropped because
  the body can't name them, whatever they are, and that opaque definitions and definitions
  with a native are skipped (after G2) (G3).
- The example is clear, has its snapshot, and the lane reports that it fails on main
  (`E-REWRITE-NOTHING`), which meets D3608's before/after rule.
- FollowsFormsBinders: only the proof body changes, and no statement changes, so this is
  not a narrowing (D3688).
- Optional: one clause in the proving guide (around line 799), "…even where the goal reads
  a field through its accessor and the parser holds it as a projection".
- Optional, completeness: an over-applied accessor (`r.f x`, a function-valued field) isn't
  rewritten, so `r.f x` doesn't match `(Proj r) x`. Rewriting the saturated prefix would
  cover it. File it only if it comes up.
- No `docs/core.md` change: the kernel is untouched, and `Proj` was already a core term.

## Fixes

- **G1 (before merge, small).** Run the abstracting solve as written first, and with
  `accessors_as_projections` only if that fails. If that is skipped, the verifier must at
  least run `hash_stability` for `continuation-solved-by-abstracting` and check the 8
  SW-4330 fmt namespaces, accepting any hash change as an intended re-spelling.
- **G2 (before merge, one line).** In `accessors_as_projections`, skip a definition that
  is opaque (`g.def(d).opaque()`) or has a native (`value::eta_held(g, d)`). Neither is
  convertible to the projection.
- **G3 (before merge, comments).** Fix the two doc comments as in §5. Add a sentence to
  `solve_abstracting`'s doc saying that the refusals are applied to the rewritten, convertible
  goal, so a variable or unknown found only in a dropped argument doesn't count.
- **G4 (note).** One before/after check time for `FollowsFormsBinders.sw` on the ticket.
