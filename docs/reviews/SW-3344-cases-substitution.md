# SW-3344 review: `cases` substitutes equations taken apart from constructor equations

Reviewer: Opus review lane, 15 Nov 2026. Branch `lane/SW-3344` (14cf35382).

## Verdict

**Merge, with two follow-ups (F1, F2) filed.** I found nothing unsound, and
couldn't have: the kernel re-checks every proof. Nothing in the existing corpora
or snapshots regresses. The substitution is correct on every dependent case I
tried. Two medium findings came up: a `cases in t` that names the replaced
variable now fails where it checked before (F1), and the cost grows
exponentially with the number of substituted fields (F2). Both are narrow and
can be fixed on their own; neither affects anything in the repo today. If the
orchestrator would rather not merge a known regression, F1's fix is small and
could go in first.

## What I ran

- `cargo build --release -p stitchwort-cli`: ok.
- `cargo nextest run --release -E 'binary(running) & test(/examples::(soundness|reject|accept)/)'`:
  **5 passed** (accepted, rejected, soundness examples and projects; 71 s).
- `cargo nextest run --release -E 'binary(library) & test(/hash_stability/)'`:
  **10 passed**. `prelude`, `projects` and `a_namespace_checked_alone…` are
  unchanged, so no std prelude hash moved. The only hash changes are the
  lane's regenerated snapshots: `cases-data` (`parseSmallSome`),
  `function-induct` and `match-induct` (`firstBigIsBig`, `…Implies`), plus the
  new `cases-constructor-equations`. AoC and std proofs outside the prelude
  that meet a constructor equation in `cases` may change hash in the same way.
  That only invalidates check caches (D2303), and Overmind's rolling check
  will show it.
- Probe files in
  `/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3344-review/`,
  each checked with the branch binary and with main's.

## Correctness of the substitution

The proof is `J (z q => (d…: D…[z/x]) → G[z/x]) (d… => cases') e d…`. Here
`e: t = x` is either the fact itself or the fact turned round by
`J (z q => z = x) rfl fact`. I checked both against `docs/core.md` §J
(`p: x = y`, `d ⇐ P x rfl`, gives `P y p`): the motive's `q: t = z` and the
de Bruijn indices (`Var(1)` for `z`, `Var(n+1-x)` for `x` under the two
binders, `a` shifted by 2) are right.

Probes, all accepted by the kernel on the branch:

| Probe | What it exercises | Branch | Main |
|---|---|---|---|
| `p2_dep.sw` `chain` | `i: Fin m`, `hi` mentions `i`, eliminate `m` | ok | ok (closer) |
| `p2_dep.sw` `leftVar` | variable on the left (`n = m+1`), `i: Fin n` copied, `cases in` names the copy | ok | E-TYPE-MISMATCH |
| `p2_dep.sw` `otherDep` | other side mentions a dependent of `x` (skipped, no crash) | ok | ok |
| `p2_dep.sw` `pingPong` | `Some x = Some y` and `Some y = Some x` | ok, terminates | E-CASES |
| `p2_dep.sw` `pair` | four variables, two pair equations crossing | ok | E-CASES |
| `p3_let.sw` | `let k := y` in the context, `i: Fin (k+1)` and `f y i` needing `k ≡ y` | ok (the let is unfolded in values, so `i` counts as a dependent) | E-CASES |
| `p5_split.sw` `caseBound`, `caseBoundLeft` | the variable is bound by a split (`o = Some value`), on either side, with `%case` mentioning it | ok | E-CASES |

Points checked by reading the code:

- **Variables whose type mentions `x`, and hypotheses that depend on each
  other.** `deps` takes every later level whose quoted type mentions `x` or
  an earlier dependent, transitively in level order. That is enough because
  a type only mentions earlier levels. `t` and the equation's type `a` must
  not mention `x` or a dependent, which is right.
- **Parameters versus case-bound variables.** These are treated alike.
  `is_var(env[x], x)` and `lets[x].is_none()` keep let-bound names and
  solved variables out.
- **Other facts.** A fact that mentions `x` is a dependent and is copied
  under its own name, so it stays in `injected`. The fact being used is left
  out of `deps` and stays in scope, so messages show it.
- **(Low, latent) A dependent whose type mentions the fact itself.** Such a
  hypothesis is put into the motive as `D[z/x]` with the original fact
  (`t = x`) inside it, where it would need `q: t = z`. The motive would then
  be ill-typed and the kernel would refuse the theorem. I don't think this
  can be reached: the fact is named `%factN`, which a user can't write, and
  neither `take_apart`'s nor `apply_guarded`'s facts mention proofs. It is
  an unstated invariant, though. Worth a one-line comment, or replacing that
  level by `q` in the motive (the Lean `subst` way).

## Termination

Each substitution removes `x` from everything visible: the goal and the
visible hypotheses are replaced by copies, and `mentioned` only counts the
goal and visible dependents. Every fact made later (by `take_apart` on the
copies, or by `apply_guarded`) comes from visible hypotheses, so it can't
mention `x` again. New variables only come from splits, which the 64-case
budget bounds. So the restart loop is well-founded even without the
`substituted` guard. The guard (by name, and copies keep the name) also
stops the "used again, replaced back" case. `pingPong` and `pair`
terminate. I found no ping-pong.

## Order and existing proof terms

Substitution runs after the closers and `cases in t`, and before guarded
implications and splits. The code comment says this is "so a proof they gave
before substitution existed keeps its term". That only holds at the node
where the closers succeed. A proof that used to close deeper down, after a
split, a guarded implication or `omega`, now goes through the substitution
first. That is why `parseSmallSome` and `firstBigIsBig` changed hash. This
is acceptable (migration cost doesn't count), but the comment overstates it.
The real cost is F1.

## Findings

### F1 (medium): a `cases in t` that names the replaced variable now fails

`p1_cases_in_names_y.sw`:

```stitchwort
def k (b: Bool) (n: Nat): Nat := if b then n else n
theorem lem (p q: Nat → Prop) (step: (m: Nat) → q m → p m) (n: Nat) (hn: q n): p n := step n hn
theorem namesY ∀ (p q: Nat → Prop) (step: (m: Nat) → q m → p m) (b: Bool) (x y: Nat)
    (h: Some x = Some y) (hy: q y): p (k b y) := cases in lem p q step y hy
```

Main checks this. On the branch: `E-TYPE-MISMATCH: expected q y, but this
has type q x` (in the case `b = False`). At the root `t` fails because the
goal still needs a split. Then the substitution replaces `y` by `x` in the
goal and in `hy`, but `y` stays in scope as a separate variable. So in the
leaf, `t` mixes the two. The message is confusing too: the user never wrote
`x` here.

Suggested fix: in the substitution's base, also bind the eliminated
variable's visible name as a `let` of the other side (`y := x`, or `x := 3`
for `Some 3 = Some x`). A term that names `y` then still checks by
conversion. The `lets[x].is_none()` check already stops the alias from
being substituted again. A cheaper alternative is a note in the `cases in`
type-mismatch message ("in this case `y` was replaced by `x`, from `h`"),
but that leaves the regression in place.

### F2 (medium, performance): exponential in the number of substituted fields

`perf_N.sw`: `h: MkBig x1 … xN = MkBig y1 … yN`, goal
`x1 + … + xN + 0 = y1 + … + yN + 0`, with two extra hypotheses mentioning
every `yi`:

| N | branch | main (closes by omega) |
|---|---|---|
| 8 | 0.49 s | – |
| 10 | 1.41 s | 0.63 s |
| 12 | **14.5 s** | 0.95 s |
| 12, no extra hypotheses | 2.2 s | – |

The time grows about 3× per field. The cause is that `deps` includes the
*hidden* originals. After `y1` is replaced, the shadowed `h` and its visible
copy both still mention `y2`, so the next step copies both, and so on: 2^k
copies after k steps. Each copy is also a Pi in the motive.

Suggested fix: copy only what is needed. Start from the goal and the
visible hypotheses that mention `x`, then close under "this copied type
mentions that level". Leave hidden levels that nothing copied mentions
alone. They don't need abstracting, and nothing can name them. The
`types` quoting of every level at every node, once any fact exists (below),
can be made lazy in the same change.

### F3 (low, performance): a quoting pass at every node once a fact exists

Once `injected` is non-empty, every later node in the run quotes the types
of all hypotheses in scope before it checks whether any fact can be used.
Quote the fact's sides first, and the context only for a fact that has a
variable side.

### F4 (low, messages): the eliminated variable stays in the messages

`p4_msg.sw`: an open case shows `fact 1 (added by cases): x = y`,
`h: Some x = Some x` and `hy: f x = 3`, where the user wrote `hy: f y = 3`.
The fact does explain the change, so this is readable. Two things would
read better: leaving out the copy of the source equation once it has become
trivial (`Some x = Some x`), and a note such as "`y` is replaced by `x` (from
`h`)" in place of the bare fact. The new `fact N (added by cases)` naming
is a clear improvement on `%factN`. The `cases-later-field` snapshot's
reordering (facts now listed before `h`, because `h` is the newer copy) is
harmless.

### F5 (low, docs)

`docs/syntax.md` "Each case" and the guide's section are accurate.
`docs/proving-guide.md`'s `cases` paragraph (around line 288) doesn't
mention the substitution. One clause there would help proof lanes reaching
for `rewrite`.

## Not checked

- I ran no AoC or std checks beyond the hash snapshots (lane test budget).
  The lane reports clean checks of several AoC days and toyfmt.
- I didn't time a real 64-case run with facts. F3 is from reading the code.
