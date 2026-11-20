# Proposal: `match` and `rewrite` unfold only the calls on the path to a hidden occurrence

**Status:** built as the middle step (SW-4419, 20 Nov 2026): `crates/elab/src/unfold_path.rs`,
wired into `rewrite`, `match`/`cases` (and guards) and the transport; metrics outcome `partial`.
Not built: the per-cell memo of §2.1 rule 2(d) (a cap of 64 openings per walk instead), and the
"outside proof positions" refinement of the relevant variables. Draft 1 was design only (SW-4412,
from SW-4355; Opus paper lane, 20 Nov 2026).
Written against `main` at `9a6caf2d2`. Nothing in the repository was edited; the probes ran
the release CLI from that commit on a scratch copy of `tools/fmt` and `aoc` (§9). Migration
cost (hashes, snapshots, proof edits) is not counted (D2303).

Related: [goal-as-written.md](goal-as-written.md) (stages 1–4, option A, built),
[bounded-readback.md](bounded-readback.md) (D2538, D2542: decided, stages 3, 6a, 6b not built;
tickets SW-1838, SW-1839, SW-1840), [bounded-readback-remaining.md](bounded-readback-remaining.md).

Labels: **[checked]** read at the place given; **[ran]** run for this note (§9);
**[inferred]** my reasoning from checked or ran facts.

## 0. Summary

**The problem.** `match e` and `rewrite p` first look for `e` (or `p`'s left side) in the goal
as written. When it is there only *inside* a folded call, the as-written search finds nothing
and the fully unfolded search runs instead. Its motive is the goal's whole normal form, so the
arm's goal (or the next goal) has every definition unfolded: `Parse.Follows`, `Mark.Alike`,
`runFrom`, the parser itself already run against a `state`. In the formatter's two-run proofs
that leaves a continuation `?j` that the abstracting unifier can't solve, so two proofs still
carry hand-written `[j := …][k := …]` pairs (`followsRowStart`, `followsBlockLine`).

**The change.** A middle step between the two searches: walk the goal as written and unfold a
call only if its body, not its arguments, produces an occurrence. Everything else stays folded.
The motive keeps `Follows` and its thunks; only `rowStart` (or the left `blockLine`) is opened.

**What it should do.** Both proofs check without the pair. I checked this by stating the goals
this step would produce by hand: both check with no pair, while the theorem without the pair
fails today **[ran]**. In the parser proofs I sampled, about 60% of `match`es and 5% of
`rewrite`s take the unfolded path today; in three AoC 2020 days the figures are an upper bound
of about 57% of `match`es and 9% of `rewrite`s (§6). The arm and next goals of all those sites
become partly folded, so they are smaller and closer to the source. Every step this changes
keeps a goal *convertible* with today's, checked, except where the step also abstracts an
occurrence written differently that today's syntactic search leaves (§4.1). Nothing that checks today can fail at the
`match` or `rewrite` itself. A later step in the same arm can (§4.2), and that needs one
measurement run before merging.

**It is not a new design.** It is the decided D2538 ("motives from the opened calls") with one
correction to bounded-readback's walk order (§2.3), built earlier than planned. Today's code
(option A, completeness and agreement checks) uses it as a middle step. Stages 6a and 6b
(D2542) later make it the only fallback. Recommendation: build it now as stage 3 (SW-1838)
plus the wiring. This is the orchestrator's call; there is no D question (§8).

## 1. The two cases

**`followsRowStart`** (`tools/fmt/src/Syntax/FollowsDeclHeaders.sw:529`). Goal:

    Parse.Follows SameCode RowsAlike (() => rowStart self modes open lower second)
                                     (() => rowStart selfTwin modes openTwin lower second)

`match lower && isSome Colon second`: the scrutinee is `rowStart`'s `if` condition
(`DeclParser.sw:513`), visible only once `rowStart` is unfolded. **[checked]**

**`followsBlockLine`** (`FollowsFormsBlocks.sw:480`). Goal `Follows … (() => blockLine more self
… before items) (() => blockLine more selfTwin … before others)`. `rewrite deafOfStripped
nextIndex nextIndexDeaf items others same` has left side `nextIndex items`. That term is inside
`blockLine`'s body, `blockPeek … { modes | allow = nextIndex items }` (`Parser.sw:734`).
**[checked]**

**Today.** Without the pair, `followsBlockLine` fails with E-TYPE-MISMATCH. The expected type
is `Follows` unfolded (`∀ state other … Mark.Alike … → runFrom state … = Ok …`), and
`_j` meets `Std.Effect.bind (statementOn …)`. **[ran]** The metrics show both sites as
`nothing` as written. Today's search then runs (`STITCHWORT_MATCH_METRICS`,
`STITCHWORT_REWRITE_METRICS`). **[ran]**

**With the goals this step would produce, stated by hand** (scratch theorems, no pair):

- `Follows … (() => blockPeek more self … before { modes | allow = nextIndex others })
  (() => blockLine more selfTwin … before others)`, proved by `followsThenEq (followsPeek …)
  (seen => followsBlockKind …)` as the real proof does: **checks** (1.8 s, cached deps).
  The right side stays the folded `blockLine` call; that is what §2 produces, since the
  right thunk holds no occurrence. **[ran]**
- The `False` arm, `Follows … (() => rowVariable modes open (rowAbilities self modes
  (modes.at RBrace) (modes.at Pipe))) (…twin…)`, proved by the real arm's body: **checks**.
  **[ran]**

## 2. Mechanism

### 2.1 The walk

The input is a target value `T`: the goal unforced, as bound (goal-as-written.md §5.2), or a
hypothesis's type for `at h` or a `match` copy. The other input is the needle `N`. Its
*relevant variables* are the free variables of its unfolding, outside proof positions and the
rule's own unknowns (bounded-readback.md §4.2 rule 1, unchanged). The walk reads `T` back as
`quote_folded` does and builds the motive body with a fresh variable `x`:

1. **An occurrence as written** (head as written, then the site's own comparison: unification
   solving nothing for `match`, solving the rule's unknowns for `rewrite`) becomes `x`. This
   is today's as-written test, unchanged.
2. **A glued call `f a₁ … aₙ`** that doesn't step at once:
   - (a) Walk the **arguments first**, giving `a′ᵢ` (occurrences in them already `x`).
   - (b) If no `a′ᵢ` mentions a relevant variable of `N`, the call's unfolding can't hold a
     further occurrence (definitions are closed). It is kept as `f a′₁ … a′ₙ`.
   - (c) Otherwise **open it**: unfold one step (`unfold_once`, `value.rs:981`) the call with
     `a′ᵢ` substituted (evaluated with `x` a neutral variable), and walk that.
   - (d) If the walk of the opening found at least one occurrence, the opened result is kept,
     and the call is **on the path**. If not, the call is kept folded as in (b). The negative
     answer is memoised per value cell within one meta epoch (bounded-readback §4.2 rule 3).
3. **Anything else** (binders, constructors, `Eq`, neutrals) is walked structurally, as
   `quote_folded` does.

**"On the path" is exactly the calls in step 2(d)**: those whose *own body*, with the
arguments' occurrences already abstracted, produces an occurrence. Callers of such a call
are not on the path when the call sits in their argument (`Follows` around a thunk). They are
on the path when the call sits in their body (`f a := … g a …`, so `f` opens and `g` opens
inside it).

### 2.2 The cases the brief names

- **Nested calls.** Bottom-up through arguments and top-down through bodies. In
  `followsRowStart`, `rowStart`'s arguments mention `lower` and `second`, so it opens and its
  `if` condition is found. The thunks, now `() => if x then … else …`, no longer mention
  `lower` or `second`, so `Follows` stays folded by rule (b) and is never opened. In
  `followsBlockLine`, the left `blockLine` opens. Inside it, `blockPeek`'s argument `{ modes |
  allow = nextIndex items }` holds the occurrence, so `blockPeek` stays folded with `allow =
  x`. The right `blockLine` mentions `others` but not `items`, so it stays folded. Result:
  `Follows … (() => blockPeek … {allow = x}) (() => blockLine … others)`, the shape probed in §1.
  **[inferred from §1's ran probes]**
- **Several occurrences.** The path is the union of each occurrence's chain. Both
  `rowStart`s open. For a rule with unknowns, the instance is the first occurrence in
  pre-order of the walked term, then every occurrence of that instance. Under today's option
  A it must also equal today's instance (`todays_instance`, `rewrite/as_written.rs:571`), or
  the step falls back. **[checked]**
- **Under a binder.** The walk enters binders as the read-back does, with the bound variable
  as a fresh neutral. An occurrence that mentions a variable bound inside the target is not
  an occurrence (`mentions_bound`, as today). `rewrite`'s occurrences that use such variables
  stay with `rewrite/under.rs`'s congruence steps, which run before any as-written search
  (`rewrite.rs:1099–1139`; the as-written path runs only when `steps` is empty), so nothing
  changes there. Both thunks in the two cases are such binders (`() =>`), and their
  occurrences use no bound variable. **[checked]**
- **Copies (`match`).** Each variable's type is walked the same way. The copy rules are
  unchanged, including that a `let` is never copied (`matching/as_written.rs`, check 1).
- **A call that steps at once** is forced, as `quote_folded` does, before rule 2 sees it.
  A call field `(f x).i` goes through `unfold_once`'s projection case. An opaque or
  well-founded definition does not unfold in today's read-back either, so it is never opened.
  **[checked]**

### 2.3 How this differs from bounded-readback's `find`, and why it matters

Bounded-readback §4.2 states the skipping rule top-down: "if some relevant variable is
mentioned by no argument of a call … it is read as written. Otherwise it is unfolded one step
and the walk goes on inside". Applied to `Follows (() => rowStart … lower second) …`, that
opens `Follows` first, because its thunk arguments mention `lower`. It then finds the
scrutinee through `runFrom state (rowStart …)`, and "the opened calls" include `Follows` and
`runFrom`. The motive would then unfold `Follows` again, the very shape that defeats the
continuation. Two refinements fix it, and the stage 3 brief should carry both:

1. **Arguments first** (2(a)): an occurrence reachable through an argument is abstracted in
   the argument, and its substituted copies in the body come for free (the motive is applied,
   then computed).
2. **Opened is not on the path** (2(d)): a call opened and found empty stays folded in the
   motive. D2538 says "motives from the opened calls"; this reads "opened" as "opened and
   found something", which I take to be its intent. Otherwise every opened call would unfold
   in the motive, even when there was nothing in it.

Neither changes the free-variable rule or the memo, and both only make the walk open less.

## 3. Where it goes in the search order

Today (goal-as-written option A, built): **as written** (kept if complete and in agreement
with today's result) → **today's search over the whole normal form** → **rescue** (the
as-written result, hidden copies and all, when today's finds nothing).

**Now: a middle step.** As written → **partial unfolding (§2)** → today's search → rescue.
The partial result is kept under exactly the as-written result's conditions, reusing the
code:

- `rewrite`: the motive type-checks and computes back to the goal, the premises are
  discharged, no copy of the left side remains hidden (`hidden_copy`, `:504`), and the
  instance is today's.
- `match` and `cases`: checks 1–4 of `matching/as_written.rs`. Among them, the generalised
  targets, read back unfolded, *agree* with today's generalisation (`Finder::agree`), and the
  motive is checked now.
- The transport (SW-1629): the same agreement test.
- Anything failing or running out on this path: fall back, with the attempt's own spare
  budget so a failed attempt costs today's search nothing (as `attempt` does,
  `rewrite/as_written.rs:248`).

It is a middle step, not a replacement, because under option A the replacement would be
D2542's rule: no agreement check, and hidden copies left. Matt decided that for stages 6a and
6b, which also migrate the proofs it breaks (bounded-readback §8). Building it as a middle step
now gets the benefit at once with no proof migration, and the code becomes 6a's and 6b's step 2
unchanged. Those stages then only delete the agreement checks and today's search, as already
planned.

**The rescue** keeps its place. As built, the partial step never rescues: where today's
search finds nothing, its result is discarded (counted as `nothing`) even when it found an
occurrence written differently inside an opened call, so the arms keep the goal unchanged, as
now, and the rescue sees the same situation (SW-4430 M1; `examples/goals/
match-no-rescue-through-calls.sw`).

**`rewrite repeatedly`** has a cheap first pass over the goal as written only, where a rule
set's rules are only ever looked for. The partial step is skipped there: it would let set rules
fire where they didn't, in a different order, and make that pass dearer. The full pass uses it
through the same `rewrite` search (SW-4430 M2).

**A whole `rewrite` is retried without the step.** A rule's check sees only its own step,
but the goal it leaves is partly folded, and a later rule (or the proof after `then`) can fail
on that goal where it passed on the computed one: in `tools/fmt`'s
`PrintHangProofs.stepColumn`, `Bool.andFalse glue` opened only `step`, and `staleBlocks`
then failed its round trip inside the still-folded `past`. So a goal `rewrite` that fails after
any rule kept a partial result is elaborated again, from a snapshot, with the step off, and
that outcome stands: success, or the error it gave before the step existed
(`examples/accept/rewrite-partial-unfold-retried.sw`). A `match` has no such retry yet: it
keeps a partial result once its own checks pass, and an arm that then failed only because its
goal stayed partly folded would be the same kind of break (none seen in `tools/fmt`).

## 4. D3688: can anything that checks today stop checking?

D3688 is about proved tools accepting less and conditions added to top theorems. This change
alters no statement, grammar or driver, and a proof it breaks is fixed by editing the proof,
never the statement. So it is outside D3688's scope by construction. The real question is
whether proofs that check today stop checking, which is migration (D2303) but should still be
small and known before merging.

### 4.1 At the `match` or `rewrite` itself: no

The partial result is used only if it passes every check today's as-written result must pass,
including agreement with today's generalisation. So the motive is the same as today's up to
the representation of the calls kept folded, and each arm's goal (or the next goal) is
*convertible* with today's, checked by `Finder::agree` and the motive check, then by the kernel.
Every failure on the path, running out included, falls back to today's search, which is
byte-for-byte what runs now. So a `match` or `rewrite` that succeeds today still succeeds, and
one that fails today still fails, except where the partial result succeeds and today's would
have failed: only a gain. **[checked: the fallback structure, `rewrite.rs:1142–1199`,
`matching.rs:1441–1485`]**

One qualification (SW-4430 W1). The agreement check lets the new reading abstract *more*
than today's: an occurrence written differently (up to computation) inside an opened body,
which today's syntactic search over the normal form leaves. Where that happens, the arms are
today's with that extra occurrence replaced, so they are not convertible with today's. Stage 2's
folded reading already does the same, and that was accepted there. A strict agreement mode for
the partial reading would make the claim exact, if the measurement run shows breakage of this
kind.

### 4.2 Later in the arm: yes, possibly, and the fallback does not reach it

The fallback is reached for every failure of the step itself, but not for a failure in a
*later* step. Once the partial result is kept, the arm is elaborated against the partly
folded goal, and nothing backtracks to retry the `match` unfolded. So a proof can succeed
differently and then break later. Where the representation can matter:

- **Later `match` and `rewrite`: robust.** Their own chain ends in today's search over the
  goal's *unfolded* read-back. The goal is convertible with today's, so that read-back is the
  same normal form, and so the same result. An earlier as-written or partial hit is kept only
  if it agrees with that same result. So by induction a chain of searches in the arm gives
  today's results up to representation. **[inferred; normal forms of convertible values
  coincide up to the read-back's canonical choices: eta and stuck natives]**
- **`rfl`, `decide`, `omega`, conversion: unaffected.** They compute.
- **Unification against a lemma, and inference of implicit and higher-order arguments:
  exposed.** The unifier compares as written first and unfolds on failure. A folded goal can
  lead it to a *different* solution than the unfolded one did (first-order on calls versus
  on bodies), and a different solution can make a later step fail. This is the case the
  change exists to help (the continuations of §1), but the same mechanism could in principle
  hurt elsewhere.
- **Messages and hovers:** the goals shown change, for the better (folded).

**How likely, from precedent.** goal-as-written stage 1 made the same kind of change for
`rewrite` (1,556 AoC next goals kept folded). Its blunt prototype broke one declaration, which
was a motive failure on the step itself (now a fallback); none broke in a later step
(goal-as-written §5.3). SW-1628 (stage 2) made it for `match` with the same agreement check.
The changes here are smaller in kind: the same convertible goals, with fewer calls unfolded
than today. **[inferred]**

**Could the fallback cover later failures too?** One way: re-elaborate a failing declaration
with the middle step off, and keep that result if it checks. That would guarantee no
regressions at the cost of double elaboration on failure only. I recommend against it. It
gives two semantics with an implicit switch, it hides the breakages a measurement should
surface, and it goes against D2540, under which a limit or retry never chooses the answer.
Instead: one measurement run before merging (§7), with any breakage fixed by a proof edit,
listed, and never by a statement change.

## 5. Terms, hashes and check time

**Terms.** The kernel is unchanged. At every site where the step is kept, the `J` motive of a
`rewrite`, and the motive and copy types of a `match` helper, contain calls where today's
contain the whole normal form. They are smaller (SW-1762's shape: `resolveOutOfWalls`'s proof
term 4.6k → 106k nodes because of an unfolded motive) and checked by the kernel as before (it
checks with gluing off). The arms' later terms change too, since later steps see a different
goal: lemma arguments are inferred differently and `rewrite`s keep folded motives more often.
**[inferred]**

**Hashes.** Every declaration with a site that takes the middle step gets a new proof-term
hash, and so do its dependents wherever the hash covers proofs. §6 puts that at a large share
of the formatter's two-run and walk proofs and of AoC's proof namespaces. The hash snapshots
are re-recorded in the lane (not a cost to weigh, D2303).

**Check time.** The step runs only where today already runs the unfolded search. Under option
A today's search must still run for the agreement check, so the step *adds* one walk: the
folded goal, plus the bodies of the calls it opens, plus the opened-and-empty ones up to their
memo. It also adds one motive check and one agreement comparison, roughly the cost of the
as-written attempt that already runs. Stage 1 measured that as-written attempt at about +10%
user time as an upper bound (both searches run) (goal-as-written §5.3). Against that, every
later step in the arm works on a smaller goal: stage 1's "feeds on itself" effect, 276 more
folded rewrites downstream. Estimate: between −10% and +10% on namespaces dense with such
sites, near zero elsewhere. **Not measured**; the lane reports `--timings` for the namespaces
of §6. Under 6a and 6b the agreement check and today's search go, and the step is then
cheaper than today's whole read-back almost everywhere.

## 6. How many sites take the unfolded path today

**Method.** `STITCHWORT_MATCH_METRICS` and `STITCHWORT_REWRITE_METRICS` print one line per
attempt with its outcome as written. `incomplete` (a copy hidden in a call) and `nothing`
(not visible) are the sites that fall to today's unfolded search. A namespace was re-elaborated
by appending a trivial theorem in a scratch copy, so the cache doesn't answer for it, and
`--timings` was used to confirm which units ran. Release CLI, `nice -n 19`, under 20 s each.
**[ran]**

| Namespace (units re-elaborated) | `match`: folded / incomplete / nothing / other | `rewrite`: folded / nothing / other |
|---|---|---|
| `Syntax.FollowsFormsBlocks` | 4 / 3 / 13 / 1 | 27 / 3 / 1 |
| `Syntax.FollowsDecl` | 5 / 1 / 7 / 0 | 35 / 1 / 0 |
| `Syntax.FollowsStatements` | 14 / 4 / 10 / 1 | 69 / 5 / 1 |
| `Syntax.FollowsForms` | 15 / 1 / 21 / 0 | 78 / 6 / 1 |
| `Syntax.ParseWalkOutside` | 11 / 1 / 30 / 0 | 23 / 0 / 3 |
| `Syntax.ParseWalkLadder` | 17 / 1 / 23 / 6 | 66 / 0 / 0 |
| **fmt, 6 of ~25 proof namespaces** | **66 / 11 / 104 / 8 (115 of 189, 61%)** | **298 / 15 / 6 (15 of 319, 5%)** |
| AoC 2020 days 7, 13, 18 (each day's program, Spec and Proofs) | 403 / 52 / 488 / 1 (540 of 944, 57%) | 1,904 / 198 / 32 (200 of 2,134, 9%) |

("other" is `failed`, `unchecked` or `rescued`.)

**How good the estimate is.**

- **`nothing` is an upper bound for `match`.** It also counts generalisations where today's
  search finds nothing either. Those leave the arms unchanged, and since SW-2554 they already
  get the folded goal. In AoC it includes program code, whose `match`es generalise over an
  expected type that seldom mentions the scrutinee. In the parser proofs it is close to exact.
  Of `FollowsFormsBlocks`' 13, I could attribute 9 to source lines, and all 9 are of this
  kind (`match kind == KwHandle` and four siblings inside `exprKeyword`, `kind == KwIf`,
  `modes.limit` inside `exprBlock`, `…column == limit` inside `exprRuns`, `goal.level`). The
  other 4 have offsets that fall in other files.
- **Sampling:** 6 fmt namespaces of the ~25 with two-run or walk proofs, and 3 of 21 AoC
  2020 days chosen for having the most `match`/`rewrite` lines. So the AoC ratio leans high.
- **The rewrite ratio agrees with stage 1's whole-AoC measurement**: 759 of 5,282 rewrites
  unfolded-only, 14% (goal-as-written §5.3), against 9% here.
- So, roughly: **in the formatter's proofs, more than half the `match`es and about one
  `rewrite` in twenty; in AoC, perhaps a third to a half of proof `match`es and a tenth of
  `rewrite`s.** Likely over a thousand sites repo-wide, each of whose arm or next goal
  becomes partly folded. That is the population §4.2's risk applies to, and the reason for
  the measurement run.

**Hand-written continuation pairs.** 68 `[j := …]` lines remain in 23 files (`git grep`),
mostly the formatter's walk and two-run proofs and std's `Parse/Reads*.sw`. SW-4355 traced the
two above to this cause. The lane should try removing each pair once the step is in, and
report which go.

## 7. Plan

One lane, **Opus, Opus review** (it generates kernel terms, D2364). Estimate **120 min**
(stages 1 and 2 were planned at 120 each; this reuses their checks and adds the walk).

1. **The walk** (§2), as bounded-readback stage 3's `find` (SW-1838) with the two refinements
   of §2.3. Unit tests: bounded-readback §4.2's five, plus *argument first* (`Follows`-like
   wrapper around a thunk whose call hides the occurrence; the wrapper stays folded), and
   *opened but empty* (a call whose arguments mention the variable but whose body drops it;
   kept folded).
2. **Wired as the middle step** in `rewrite_once` (goal and `at h`), `generalised_now` (and so
   `cases`), and the transport, with today's checks (§3). Metrics gain a `partial` outcome.
3. **Accept examples:** a reduced `followsRowStart` shape (an `if` inside a call inside a
   thunk inside a wrapper whose unfolding defeats an inferred continuation) and a reduced
   `followsBlockLine` shape (`rewrite` of a term in a record update inside a call), each
   checking without hand-written arguments. Also one where the step must fall back: a copy
   hidden where the partial walk can't see it, so the agreement check fails.
4. **The two pairs removed** (`FollowsDeclHeaders.sw:539–542`, `FollowsFormsBlocks.sw:495–497`),
   each checked with `--only`. Then try the other 66 and report.
5. **Measurement before merging.** This is a behaviour change across a thousand sites, so the
   orchestrator gets Overmind to run `check --no-cache` on the lane branch for `tools/fmt`,
   `aoc` and `games/rogue`, plus std, the same run stages 6a and 6b plan (D2536). Any
   declaration that fails is fixed in the lane by a proof edit and listed. No fix may change a
   statement; if one seems to need it, the lane stops (D3688). The lane itself runs only its
   named tests and `--only` checks.
6. **Docs:** goal-as-written.md gets an "as built" paragraph. bounded-readback.md §4.2 gets the
   two refinements, and §7's stage 3 is marked as this. `docs/syntax.md` "rewrite" and
   "Generalised `match`" get a sentence: when the term is inside a call, only the calls it is
   inside are unfolded.

## 8. Recommendation

**Build it now as a middle step, as bounded-readback stage 3 (SW-1838) plus its wiring into
today's option-A searches. Then 6a and 6b reuse it unchanged as D2542's step 2.** It removes
the last two continuation pairs SW-4355 left, and probably more. It makes the arm and next
goals of over a thousand sites smaller and closer to the source. Every `match` and `rewrite`
step keeps a result convertible with today's, checked.

**No D question.** This is the orchestrator's call:

- **Scope (D3688):** no proved tool accepts less and no statement or condition changes. A
  later-step breakage is migration, found by §7.5's run and fixed by proof edits only.
- **Design:** the end state is already Matt's (D2538: motives from the opened calls; D2542:
  this is the fallback when nothing is visible). Building it earlier, as a middle step under
  today's checks, is sequencing. The arguments-first order and "opened means found something"
  (§2.3) are implementation readings of D2538 that open fewer calls than its text could be
  read to allow, and they don't change what users see beyond what D2538 already decided.
- **User-visible:** goals shown in a `match` arm or after a `rewrite` are more often folded,
  the direction goal-as-written.md (D2475–D2480) already took.

One thing to bring Matt only if §7.5 finds it: if the measurement breaks many proofs in a
way that needs more than local proof edits, that is a scope question (D3704) before merging.

## 9. Probes run for this note

All with `target/release/stitchwort` at `9a6caf2d2`, `nice -n 19`, on clonefile copies of
`tools/fmt` and `aoc` in the lane's scratch folder; repository untouched.

- `check --only Syntax.FollowsFormsBlocks.probeBlockLinePartial`: the partly unfolded
  `followsBlockLine` goal, no pair. Checks, 1.8 s.
- `check --only Syntax.FollowsDeclHeaders.probeRowStartElse`: the `False` arm's goal with
  `rowStart` opened, no pair. Checks, 11 s.
- `check --only Syntax.FollowsFormsBlocks.followsBlockLine` with the pair removed:
  E-TYPE-MISMATCH as in §1.
- §6's counts: `STITCHWORT_MATCH_METRICS=1 STITCHWORT_REWRITE_METRICS=1 check --timings=1
  <Namespace>`, after appending `theorem probeDummy: 1 = 1 := byComputing` to the namespace's
  file in the copy (a trailing comment does not make the cache miss). Each 3–20 s.
