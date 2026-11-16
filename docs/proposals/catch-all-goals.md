# What a catch-all arm's goal shows

**Status:** design note, 15 November 2026 (SW-3301, a paper lane; found in
SW-3293). Nothing is built. The recommendation changes only what goals
display, so it is an implementation call (the orchestrator's), not a
question for Matt.

Claims are marked **[source]** (read at `397c2da84`), **[measured]** (the
main checkout's release binary, built 03:53 today; probes in the lane's
scratchpad, `p1.sw` to `p6.sw`, quoted below) or **[recalled]** (other
languages, from their documentation, not re-run here).

## In plain words

**The problem.** In a proof's catch-all arm, the goal doesn't talk about the
thing being matched. After `match s with | "ab" => … | _ => ?`, the goal
reads `p (MkText [MkChar code✝ valid✝, ..tail✝])`, with three unnamed
variables listed, instead of `p s`. Writing `| other => ?` doesn't help:
`other` isn't shown either. Worse, the goal is only one of several the arm
must prove, and can be the wrong one to read: after `| Some True => …`, the
goal of `| _ => ?` reads `p (Some False)`, but the same body must also prove
`p None`. This is not specific to literals: any arm reached through more
than one leaf of the case tree shows its last leaf's goal.

**The change.** Show each arm's goal as the arm is written: the match's goal
with only the arm's own patterns substituted. A catch-all `_` sees `p s`; an
arm `| other =>` sees `p other`; `| Some _ =>` sees `p (Some value✝)`. The
elaborated term is untouched: the body is still checked at every leaf, so a
proof whose catch-all computes the program (`f s` stepping to `f`'s default)
keeps working.

**What it should do.** A catch-all's goal names the scrutinee and lists no
unnamed cells. Today 10 of the 12 catch-all probes below list up to three
cells or show one case of several [measured]; with the change none would
[estimated]. No term, hash or kernel rule changes.

## 1. How it happens today

A `match` compiles to a case tree; each leaf checks its arm's right-hand side
against that leaf's goal (`check_tree`, `check_leaf`, `crates/elab/src/lib.rs`)
**[source]**. At a `Tree::Case` the scrutinee variable is substituted by the
constructor value, in the goal and the whole context, as the kernel does
**[source]**. So a catch-all reached through four leaves is checked four
times, each time with a differently refined goal. Each check notes a goal at
the same span, and `flush_goals` keeps the last: "a goal at a span already
printed replaces it" (`crates/elab/src/goals.rs`) **[source]**. Errors come
from the first leaf that fails.

Literal patterns make this common, because `'a'` is `MkChar 97 _` and
`"ab"` is `MkText ['a', 'b']`: matching them splits the `Char` and `Text`
wrappers and the list, leaving cells behind. Number patterns don't: a number
test leaves the variable in place in its default branch.

SW-3293 hid cells that nothing shown mentions (`drop_split_leftovers`). In a
proof the goal usually mentions the scrutinee, so the cells stay.

## 2. Probes [measured]

| Probe | Arm | Goal shown at the catch-all |
|---|---|---|
| `p: Text → Prop`, `match s` after `"ab"`, `""` | `_` | `tail✝ code✝ valid✝ ⊢ p (MkText [MkChar code✝ valid✝, ..tail✝])` |
| same, `(h: p s)` | `_` | the cells, `h: p (MkText […])`, `⊢ p (MkText […])` |
| same, `match e: s` | `_` | `s`, the cells, `e: s = MkText […]`, `⊢ p (MkText […])` |
| same | `other` | the cells, `⊢ p (MkText […])`; `other` not listed |
| `p: Char → Prop`, after `'a'` | `_` | `code✝ valid✝ ⊢ p (MkChar code✝ valid✝)` |
| `p: Nat → Prop`, after `5` | `_` | `n: Nat ⊢ p n` (fine) |
| `(n, c)` after `(5, 'x')` | `_` | `⊢ p n c` (a tuple scrutinee refines nothing) |
| `Option Text` after `Some "a"` | `_` | the cells, `⊢ p (Some (MkText […]))`; also covers `None` |
| `List Char` after `['a']` | `_` | the cells, `⊢ p [MkChar code✝ valid✝, ..tail✝]`; also covers `[]` |
| `match q s` (an expression) after `"ab"` | `_` | the cells, `⊢ p (MkText […])` |
| `Option Bool` after `Some True` | `_` | `⊢ p (Some False)`; the body must prove `p None` too |
| `List Nat` after `[x]` | `_` | `x✝ head✝ tail✝ ⊢ p [x✝, head✝, ..tail✝]`; also covers `[]` |

Two more facts the options depend on:

- **The body is checked per leaf.** With `"ab"` and `""` before it, the
  catch-all is checked at four leaves: first character not `'a'`, `"a"`,
  `"a"` then not `'b'`, and `"ab"` followed by more. A body `hp _` with
  `hp: ∀ (c: Char) => p (MkText [c])` fails at the fourth: "expected `p
  (MkText ['a', 'b', head✝, ..tail✝])`" — a shape the goal never showed.
- **Per-leaf checking is what lets a proof compute.** For `f` with arms
  `"ab"`, `""`, `_ => 2`, a proof's catch-all goal `f s ≠ 0 ∨ s = ""`
  "computes to `2 ≠ 0 ∨ …`": each leaf is one of `f`'s own leaves, so `f`
  steps. `s` can also be written in the body (`k s` checks), since in the
  leaf it stands for the leaf's value.

## 3. How others show it [recalled]

- **Lean 4.** Literal patterns on `String`, `Char` and `Nat` are value
  patterns, compiled to `decEq` tests (`caseValues`); the scrutinee is never
  taken apart. Each alternative is elaborated once, against the motive
  applied to its patterns, so `| _ => ?_` shows `⊢ p x✝` (with `match h : s`,
  also `h : s = x✝`). The price: in a proof, `f s` doesn't compute in the
  catch-all. One uses `split` (which adds overlap hypotheses `s = "ab" →
  False`) or `f`'s equation lemma, whose catch-all case has those
  hypotheses.
- **Agda, Idris 2.** A clause is checked once against its own left-hand
  side; the case tree is built afterwards. A hole in `f _ = ?` shows the
  variable. A catch-all clause holds definitionally only where the tree
  agrees (Agda's `--exact-split` warns otherwise; `CATCHALL` silences it).

Both show the arm as written. Stitchwort's per-leaf check gives proofs more
(the program computes in the catch-all) and need not cost the display.

## 4. Options

**A. Show the arm as written (display only).** At a leaf, the goal and
context a hole records (`Pending.expected`, `.context`) are rebuilt from the
state before the splits, applying only the splits this leaf's arm needed,
that is, those where the arm's row had a constructor or literal in the
column split, not a variable or `_` [the match compiler knows this when it
pushes a wildcard row into every branch]. The other splits are undone by
position, not by searching for the value, so a goal `p o ∧ q None` at the
`None` leaf doesn't turn into `p o ∧ q o`.

- The scrutinee is shown by the name the user knows: the arm's binder
  (`other`), else the scrutinee variable (`s`), else the scrutinee
  expression as written (`q s`) for a generalised `match` on one.
- The target is the same at every leaf of the arm, so which leaf's goal is
  printed last stops mattering. The "computes to" line still comes from the
  leaf (it is what conversion sees), with the leaf's value folded back to
  the scrutinee's name where it occurs whole.
- A `match e:` equation that would read `e: s = s` is shown as at the leaf
  (`e: s = MkText […]`, its cells with it): it is the one place the leaf's
  shape is information a proof can use, by `rewrite`.
- Errors in the body keep naming the leaf that failed. A follow-up, minor
  wording: when an arm is checked at several leaves, the goal says so ("this
  arm is checked in 4 cases") and an error names the case ("where `s` is
  `"ab" ++ …`"). goal-at-any-point.md planned one goal per leaf for steps;
  this is the smaller step.
- Cost: elaborator display code only, around `hole_of` and the case tree's
  leaf (a record of which splits a leaf owns, and the pre-split state on a
  stack). Estimated 3 to 5 lane hours, Opus or Sonnet (it is near `match`,
  but changes no term). No elaborated term, hash, or kernel change; goal
  snapshots (`examples/goals/`, `goal --at`, the language server) change, as
  intended. SW-3293's `drop_split_leftovers` then rarely fires; it stays for
  the cases A leaves (the `e:` equation, a computes-to line).

**B. Check the catch-all once, with the scrutinee kept as a variable.** The
catch-all becomes a join point: a local function of the scrutinee, checked
once against `p s` and applied at each leaf. This is text-patterns.md's
stage 4 for programs, extended to proofs.

- The display comes for free, and so does checking time for large catch-alls.
- It changes what proofs mean and what users write: `f s` no longer computes
  in a proof's catch-all, so today's proofs that rely on it (the `t8`
  probe; char-pattern proofs in `examples/accept/`) need `f`'s equation and
  facts like `s ∉ ["ab", ""]` that the arm doesn't have, unless B also adds
  overlap hypotheses as Lean's `split` does. Every multi-leaf match changes
  term and hash (D2303: that cost doesn't count; the lost computation does).
- A hybrid (try once, fall back to per leaf) keeps the power but makes the
  term depend on whether the generic check happened to succeed, and still
  needs A's display for the fallback.

**C. Leave it.** Goals keep naming cells, hiding the user's binder, and
showing one case of several as if it were the only one (the `Some False`
probe). Text patterns (SW-3284) make these goals common.

## 5. Recommendation

**A.** It fixes every probe above, including the misleading one-case goals
that have nothing to do with literals, keeps the per-leaf computation that
makes proof catch-alls useful, and changes no term, hash or kernel rule.
B's speed gain for programs stays text-patterns.md stage 4, where the goal
doesn't depend on the scrutinee; a proof's catch-all should keep checking
per leaf. Since A only changes what goals display, it is the orchestrator's
call; no question for Matt.

Suggested ticket: "Goals at an arm show the arm as written: undo the splits
the arm's own patterns didn't need, by position; scrutinee by the arm's
binder, its variable or its expression; examples/goals snapshot for the
`Option Bool`, text, char, `other` and `match e:` probes" (Sonnet, est.
4 h; Opus review, since it is in the match compiler). Follow-up, minor
wording: "checked in N cases" on goals and errors at multi-leaf arms.
