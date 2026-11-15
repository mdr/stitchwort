# Review: SW-3335 (catch-all facts: `auto` proves `x ≠ lit`, goals list the facts)

Opus review, 15 Nov 2026, of `lane/SW-3335` at `3c5b3af86` against `main`
(`4b660ece7`). Probes are in the reviewer's scratchpad (`sw3335rev/p1.sw` to
`p7.sw`), run with the worktree's release binary (rebuilt from the branch) and
the main checkout's.

**Verdict: merge after fixes 1 and 2.** 3 and 4 are small and can go in the
same fix lane. The proof side is sound. The `lift` change regresses one common
editing case, and the goal display names a variable the reader can't see.

## Findings, most important first

### 1. `lift.rs:733`: obligations are now solved before the goals are assumed, so a `?` in an `[auto]` argument gives a spurious error (must fix)

On `main`, a declaration with no helper of its own runs `lift` → `assume_goals`
→ `finish` → `settle_queue` (obligations). The branch solves the obligations
first, before `assume_goals`, so an obligation whose goal mentions an open `?`
is tried while the `?` is still an unsolved metavariable. It fails, and the
error prints the raw metavariable:

```
def apartFromFive (n: Nat) [auto ok: n ≠ 5]: Nat := n
def holey (k: Nat) (hk: k ≠ 5): Nat := apartFromFive ?
def holey2 (k: Nat) (hk: k ≠ 5): Nat := match k with
  | 3 => apartFromFive ?
  | j => j
```

- `main`: two goals, no errors.
- branch: also `E-AUTO-STUCK: can't decide ?0 k hk ≠ 5 here` (and `?0 hk ≠ 5`
  for `holey2`), so 2 errors.

This is an ordinary thing to write mid-proof: a hole as the argument of a
function with an `[auto]` bound, such as an index. The `holey2` shape (a
top-level `match` is the definition's own tree, not a helper) is exactly the
case the change targets.

**Fix:** in the new branch, call `self.assume_goals()` before
`solve_obligations_until_stuck()`. That restores `main`'s order for these
declarations. `assume_goals` skips metas that are already solved, so calling
it again further down the draft path is harmless. Then add `holey`/`holey2` as
a `goals/` example.

**Pre-existing, file separately:** declarations that do have helpers already
behave like this on `main`. `def withDraft (k: Nat) (hk: k ≠ 5): Nat := (match
k with | 0 => 1 | j => j) + apartFromFive ?` gives `E-AUTO-STUCK ?1 k hk ≠ 5`
on `main` too (p3), because the draft path also solves before it assumes. The
same reordering in the draft path would fix it. It's a separate ticket because
it changes the draft path's order for every declaration with a `match`.

**The other questions about the change:**

- *Waiting instance obligations.* Safe. The new call is the `until_stuck`
  variant, so instances waiting on a row default (D1123) are kept for
  `finish`'s `settle_queue`/`settle_rows`. One caveat: when the early solve
  does draft a helper, the code falls through to the strict
  `solve_obligations()`. That reports a still-waiting instance before
  `settle_rows` could settle it. The draft path on `main` already has this
  quirk, and here it can only happen in a declaration that uses the new step,
  so it's low risk.
- *Error order.* `compare_awaiting_helpers` (in `finish`) now runs after the
  obligations instead of before. With no drafts there are no comparisons
  waiting on helpers, so it does nothing and the order doesn't change.
- *Hashes.* For existing no-draft code, the same obligations are solved in the
  same state, one step earlier. Only the open-goal case above changes, and
  only by adding an error. No term change was found. The verifier's
  hash-stability snapshots should still run, as for any elaborator change.
- *Should `lift_signature` match?* Not needed for this feature. A literal fact
  needs a `match` catch-all around the obligation, and in a signature every
  `match` is a draft, so `lift_signature` already reaches `solve_obligations`.
  The gap it shares with the old body path is `cases.rs::family`
  (`by_contradiction`'s no-confusion motive is also a lifted helper drafted
  from `auto`). In a signature with no `match`, such a draft made in `finish`
  is never lifted. That gap predates this branch.
- *Should every lift solve first?* The draft path already does (strict).
  Better than a third code path: one order for both paths (resume, assume
  goals, solve until stuck, then lift if anything was drafted). Also a
  `debug_assert!` in `finish` that `attempt.drafts` is empty after
  `settle_queue`/`settle_rows`, so a draft made after lifting (say by an
  obligation that a row default unblocks) is a clear internal error, not an
  unsolved frozen meta. That could be a follow-up ticket.

### 2. `goals.rs:561`: the facts are computed before the context is trimmed, so a line can name a variable the goal doesn't list (should fix)

`shown_facts` looks each fact's level up in `context` *before*
`drop_superseded` and `drop_split_leftovers` remove entries. The updated
snapshots show it:

- `arm-as-written-nested.snap`, `expression` (`match q s with | "ab" | _`):
  the context is `p, q, s: Nat` and the fact line is `s✝ ≠ "ab"`. `s✝` is the
  compiler's variable for `q s`, which the list doesn't show, and it's next to
  an unrelated `s: Nat`.
- `arm-as-written-text.snap`, `equation` (`match e: s with … | _`):
  `s✝ ≠ "ab"`, while the goal is about `s`.

The note under it says "`auto` and `byDecision` prove them", but the reader
can't write `s✝`. `q s ≠ "ab"` and `s ≠ "ab"` aren't provable that way either,
since neither is the marked variable.

**Fix:** compute the lines after the drops, from the final `context`, and
leave out a fact whose variable isn't listed or has an inaccessible (`✝`)
name, unless that entry is listed under that name (the `clauses` case, where
`s✝: Text` is listed, is fine). Then refresh the two snapshots.

### 3. `lib.rs:4171`, `lib.rs:5408`: facts are keyed by the address of the arm's right-hand side (should fix, small)

`arm_facts` maps `ptr::from_ref(rhs) as usize` to the facts, and is cleared
only per declaration. `equations.rs` builds `Expr::Match` values during
elaboration (`equations.rs:2710`, `2733`, `6115`). If one of those is dropped
and another is allocated at the same address within the same declaration, an
arm with no facts inherits the stale entry and shows a false `≠` line. I
didn't construct a repro. It's display only: `auto` still goes through the
marks and the kernel. But it is the one way I found for the display to list a
false fact.

**Fix:** carry the facts on the leaf (`Tree::Leaf`), as `count_cases` does for
`cases`, and read them in `check_leaf`. That also drops the `HashMap` and the
per-declaration reset entry. At least, remove every key for a compile's rows
before inserting. Also, the `decl.rs` doc refers to `arm_display::arm_key`,
which doesn't exist.

### 4. Tests miss two paths of the pre-check (small)

`differs` has a `k + x` branch (`n < k`, or `n - k` in the marks) and a
constructor-tree branch. Neither is in `examples/accept/catch-all-facts.sw`.
Both work (p7): `n + 2 ≠ 7` after `| 5`, `Some n ≠ Some 5`, and
`(n, c) ≠ (5, 'x')` all check. Add those three to the accept example.
syntax.md claims "a literal nested in constructors works too", so that claim
should have a test.

### 5. Soundness of `literal_facts.rs`: safe (no change needed)

- **Every term reaches the kernel.** The transport `h => J motive Trivial h`
  is part of the declaration's body. The motive is a helper drafted through
  `lift::draft` and admitted by `resolve_batch` like any `match` helper.
  Nothing is assumed and nothing bypasses the kernel. The kernel computes its
  own marks in `check_num_case`, so the proof stands or falls on the kernel's
  reading, not on the elaborator's.
- **What a wrong pre-check could do.** If `differs` said `Some(true)` where
  the kernel's motive is stuck, the kernel would reject the declaration: an
  internal-looking error, not unsoundness. If it said `None` where the kernel
  would accept, `auto` just goes on to its other steps. I checked it against
  the evaluator's rules. The NumCase default when `n < k` or `n - k` is in
  the base's apart set matches the kernel rule. The constructor walk goes
  depth-first, field 0 first, and skips erased fields, which is the same
  order as `tree` builds (fields are pushed in reverse, so they pop in order,
  and sub-fields go on top). The walk returns at the first field that isn't
  a definite "matches", as the tree takes `Unit` at the first mismatch. It's
  conservative wherever the tree would be stuck.
- **No panics found.** `ctors()[c]` uses a constructor index from a value
  whose type was checked equal (`d == d2`), and `field_erased[i]` is indexed
  within the zip of the two field lists. Indexed families and anything not a
  number, text or constructor give `None`. De Bruijn indices: `y` is `Var(1)`
  under `h, y, q`. The flip's types are shifted by 3 from the obligation's
  context. Branch field `i` is at `n - 1 - i`, with pending matches shifted
  by `n`. All consistent.
- **Speculation.** A draft made inside an `attempt` that's undone is dropped
  (`AttemptMark` truncates `drafts`), so a discarded proof leaves no helper.
- **Order in `auto`.** The step runs only after the decision is stuck and the
  fact and hypothesis steps fail. Goals that differ without marks (a
  constructor mismatch, `n + 1 ≠ 0`) are decided earlier, so existing proofs
  keep their terms. The proposal says "only where `auto` would otherwise
  fail", but the step actually runs before `by_contradiction` and
  `from_rules`. I found no existing goal that reaches it and that those
  steps used to prove. Moving it last, just before `E-AUTO-STUCK`, would
  make the claim literally true at no cost. Optional.
- **Maintenance.** `differs` duplicates the evaluator's NumCase step. Add a
  comment naming the evaluator function it mirrors, so a change to the rule
  updates both.

### 6. The fact rule: no listed fact found false (apart from 3)

The argument: by first-match semantics, if `x == lit`, an earlier row with no
condition, `lit` (or an or-alternative that is `lit`) in this column, and a
variable or `_` in every other column, matches, so a later arm is never
reached with `x == lit`. I checked:

- conditions are excluded (`afterGuard`, and the reject example);
- or-patterns count only if every alternative is a literal;
- nullary constructors (`True`, `None`) in another column are `Ctor`, not
  `Var`, so `| 5, True =>` gives no fact for `| m, c =>` (p1);
- a `match` that is the whole right-hand side, inner matches in brackets,
  `match e:` on a `Nat`, clauses and a shadowing binder (`| k =>` with a
  parameter `k`) all show the right lines (p5);
- a fact not known gives the normal `E-AUTO-STUCK` (p6).

Header columns (`< skip`) aren't arms' patterns, so ignoring them is right.
The rule is stricter than the proposal's "a line only when the transport
would check at every leaf", and so stays true. The cost is that a few facts
the marks would give are left out (a `List Char` column, for instance).
That's fine.

### 7. `Obligation.scope` (the brief's question 4): fine

`Obligation`s are built in two places (`check.rs:4874`, and the copy in
`prove_now`), both now with the scope taken alongside the same
`env`/`types`/`names`, so the levels are consistent. Before, `from_parts` gave
an empty scope, so obligation messages printed names without the shadowing
information. Now they print the arm's names, as intended. `prove` resolves no
source names, so the scope changes only how things print, not what is
proved. Other `reject/` snapshots whose `auto` messages mention a shadowed
name may be reworded. Since the change touches the elaborator, the verifier
should run the `reject` example kind.

### 8. Smaller points

- `goals.rs` puts the facts only in the label text, not in `GoalData`. The
  language server's goal panel and `goal --at` JSON won't show them. Fine
  for now; could be a backlog ticket.
- Lines are listed inner match first (`k ≠ 0`, then `k ≠ 5`, p5). Source
  order (outer first) would read better.
- `note_arm_facts` returns `Result<()>` but never fails.
- The rule is O(rows² × columns) per match. That's fine at the sizes seen
  (AoC keyword tables are tens of arms).

## Tests run (reviewer)

- `EXAMPLES=catch-all-facts task test:one -- -E 'binary(running) &
  (test(goal_examples_report_their_goals) | test(accepted_examples_check) |
  test(rejected_examples_fail_for_the_expected_reason))'`: 3 passed.
- Probes p1–p7 with the branch's release binary, and p2–p4 with `main`'s, as
  quoted above.

## Suggested tickets

- The draft path also solves obligations before assuming goals:
  `apartFromFive ?` next to a `match` gives `E-AUTO-STUCK ?1 k hk ≠ 5` on
  `main` (p3).
- Drafts made after `lift` (`cases.rs::family` in a signature with no `match`,
  or obligations a row default unblocks in `finish`) are never lifted; add a
  `debug_assert!` and one order for both lift paths.
- Facts in `GoalData`, for the language server and `goal --at`.
