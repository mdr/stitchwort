# SW-2730: review of the same-closure walk's charging and memo

Paper review of commit 0fbe1c440 ("Kernel: charge and memoise the
same-closure shortcut's walk"), read at main 53309c0b0. No code was run.
Line numbers are `crates/core/src/value.rs` unless another file is named.

| Question | Verdict |
| --- | --- |
| 1. Can the memo make `identical_within` answer true for things that aren't identical? | SOUND |
| 2. Is "the answer is the conjunction over all pairs" true of the walk as written? | SOUND |
| 3. Does charging change a yes/no answer, or only add `E-RESOURCE`? | SOUND |
| 4. Anything else that could make the kernel accept more? | SOUND (nothing found) |

No counterexample found. Three findings worth tickets are at the end; none
is a soundness bug.

## 1. The memo: SOUND

The memo skips a pair whose key `(tag, address of left, address of right)`
is already in `seen` (4991-4993). That is sound if (a) one key always
means the same two parts with the same contents, and (b) a recorded pair
is always either fully compared or the cause of a `false`.

**Address reuse.** Every key in a walk's `seen` comes from a `Same<'v>`
on that walk's `work: Vec<Same<'v>>`; `same_layer`, `same_closure_layer`
and `same_term_layer` push only `&'v` references reached from their `&'v`
arguments (5018, 5061, 5177). So each recorded address is borrowed from the
walk's inputs for the whole call, and can't be freed or reused during it.
`same_when_solved` (4908-4918) does make owned temporaries (`force_solved`
of clones), but it compares them in a *separate* `identical_within` call
with its own `seen` (4985), which is dropped before the temporaries are. No
temporary's address ever enters the outer walk's set. `force_solved` works
on clones, so the borrowed inputs' `Rc`s are never unique and nothing is
mutated in place (`Rc::make_mut` at 523, `into_unique` at 85 both need sole
ownership).

**Contents unchanged.** The only interior mutability reachable from a
`Value` is `Unfolding::kept` (263), inside `Value::Call`'s third field. The
walk never reads it: `same_layer` compares two calls' unfoldings by
`Rc::ptr_eq` only (5136). Metavariable solutions are read (4910) but
nothing in the walk solves one. A pair's answer depends only on the two
parts (no level, environment or mode is threaded through the layer
functions), so the same key has the same answer.

**Two kinds at one address.** The tag separates values, closures and terms
(4937-4946), so a `Value::Lam` and the `Closure` inline in it can't
collide. Within one tag, both sides are the same Rust type, and neither
`Value`, `Closure` nor `Term` can contain itself inline, so two references
of one type to one address are one object. `&Shared` and `&Rc<Term>`
deref to the heap value (106, 5178), so "inline vs Rc'd" gives the
address of the value itself either way. An `Elim` is never a pair: its
`Value`s are pushed (5114, 5126-5127), each at its own address in the
spine's allocation. Keys are ordered, so `(p, q)` doesn't stand for
`(q, p)`.

**The truncation in the solved path.** This is the case the brief asked to
look at hardest. For a pair P = `Values(a, b)` with `g` given
(4995-5006): P is recorded, `same_layer` may push some of P's sub-pairs
and then answer false, `work.truncate(len)` removes them, and
`same_when_solved` decides. `len` is taken after P was popped and before
`same_layer` pushes, so the truncation removes only what this call pushed,
never another pair's pending sub-pairs. Then there are three outcomes:

- `Ok(false)`: `alike` is false and the walk returns `Ok(false)` (5010).
  Nothing is skipped later because there is no later.
- `Err`: propagated by `?`.
- `Ok(true)`: the inner walk returns true only when its own work list is
  empty (5013), so P's forced forms were compared completely, sub-pairs
  included, before the outer walk goes on. A later P is skipped
  correctly: it was fully established, not assumed.

So there is no path on which a pair is recorded, loses its sub-pairs, and
the walk continues without them having been compared. The dropped
sub-pairs belonged to the unforced comparison, which had already failed.

**Where it matters beyond `same_closure`.** `identical_within` also backs
`identical_charged`, used by the tree memo's and `ShapeMemo`'s lookups
(4419-4420, 4525-4526), where a true can return a remembered
*different*. So the memo's soundness carries a "different" verdict too,
not only "equal"; the argument above covers it (those calls pass no `g`,
so there is no truncation at all).

## 2. Conjunction over all pairs: SOUND

The walk returns `Ok(true)` in one place, after the loop, when `work` is
empty (5013). Every early exit is `Ok(false)` (5010) or `Err` (4988,
5001). A pair leaves `work` only by being popped (then compared, or
skipped as a recorded pair) or by the truncation, which per section 1
removes only sub-pairs of a pair whose comparison is being replaced by a
complete inner one. A recorded pair's sub-pairs were pushed when it was
first compared and stay on the list until popped. Because this is a work
list and not recursion with assumed results, "recorded" never means
"assumed true while still open" in a way that could be circular: `true`
needs every pushed pair popped, and values are acyclic.

The layer functions that push sub-pairs and then return false (`i1 == i2`
after pushes at 5075, 5079, 5083, 5089) lead straight to `Ok(false)`, so
their leftovers are never read.

## 3. Charging: SOUND

Charging adds only `Err`. In the kernel both call sites propagate with
`?` inside the match guard (3432, 3693), and `shortcuts_disabled` gives
`Ok(false)` as before (4885-4887). Every kernel caller of `conv`
propagates too: `check.rs:188`, `unify_index.rs:181` and `191`,
`native.rs:503`, `float.rs:642`, `nat_add.rs:288`, `value.rs:3554`,
`3788`, `3831`. I found no place in `crates/core` that turns a conversion
`Err` into false or true. `identical` keeps `unwrap_or(false)` (4957) but
passes no budget, and with no `g` either nothing in it can fail.

`same_when_solved` still maps a `force_solved` failure to `Ok(false)`
(4914-4916): "not shown identical", after which the long way runs and
reports the exhaustion. That is the equal-only direction and was there
before. Its inner walk's `Err` now propagates (4917), which is right.

In the elaborator both sites propagate (`crates/elab/src/unify.rs:314`,
`1429`). Some elaborator callers do turn an `Err` from `conv` or `unify`
into false (`cases.rs:941`, `1063`, `1066`; `closing.rs:851`, `896`;
`records.rs:1266`; `calc.rs:501-502`; `interfaces.rs:1258`). Those were
there before and could already see `E-RESOURCE`; this change makes one
more source of it. It isn't a soundness matter, since the kernel re-checks
the elaborator's output (`docs/core.md:11`), but it means a search step
can now quietly miss where it used to match, if the walk is what runs the
budget out.

One real behaviour change, in the safe direction: a comparison that used
to succeed with a large free walk can now be `E-RESOURCE`. The commit
message and Rule C say so.

## 4. Anything else: nothing found

- `same_term` (4923) is unchanged in meaning: no `g` before or after.
- The 64-pair threshold only delays recording; unrecorded pairs are always
  compared.
- `HashSet` compares keys by equality, so `QuickHasher` collisions can't
  merge two pairs.
- `docs/core.md` Rule C (297) describes the change accurately. One
  wording point: "compares each pair of parts shared by both sides once"
  holds for the kernel's form; see finding B for the elaborator's.

## Findings worth tickets

**A. No test exercises a skip that matters.** `shared_parts_are_compared_once`
(5651) finds its difference on the first path down, before any skip. A
small property test would pin the argument above: random DAG-shaped value
pairs, the walk with the memo against the walk with
`IDENTICAL_UNRECORDED = usize::MAX`, same answers; and one case for the
solved path with more than 64 pairs and a repeated meta-headed pair.

**B. The elaborator's form is still exponential under solved metas, though
now charged.** Each `same_when_solved` starts an inner walk with an empty
`seen` and a fresh count (4917, 4984-4985), on freshly forced values at new
addresses. With `?1 := [?2, ?2]`, `?2 := [?3, ?3]`, ..., compared against
the matching doubled value, each level's two fields are two distinct
addresses holding the same meta, each forced and walked separately: 2^n
inner walks. Before this commit that would hang; now it ends in
`E-RESOURCE`, so it's a completeness and speed gap in unification, not in
the kernel (`same_closure` passes no `g`). Unconfirmed by a run.

**C. `same_closure_solved`'s "no evaluation" claim is loose.** With gluing
off, `force_solved` is `force` (871-877), which computes a head. Sound
(a forced value is convertible with the original), and not part of this
diff, but the comment at 4844-4848 says more than the code does.
