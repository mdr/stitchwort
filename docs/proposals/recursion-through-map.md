# Proposal: recursion through `map`, and on a text's rest

**Status:** draft 2, 15 November 2026 (SW-3359, SW-3365). Rule 3 built (SW-3376, D3612, with
guard G1 per D3613); rules 1 and 2 parked: D3611 deferred (Matt, 15 Nov 2026: "So we could just
put the spec on the backlog for a while"). D3611 to D3613 at the end. Draft 2 answers Fable's soundness review of draft 1
([SW-3359-recursion-through-map-soundness.md](../reviews/SW-3359-recursion-through-map-soundness.md),
findings F1-F3, R1-R7; §8 maps them). Related: [mutual-recursion.md](mutual-recursion.md) §6,
[nested-data-types.md](nested-data-types.md) (draft 1's deferred option C; stage 3),
[well-founded-recursion.md](well-founded-recursion.md) (stages 3a, 3b), [SW-3288
review](../reviews/SW-3288-text-prefix.md) finding 6. **[checked]**: source at `ae7a3b341`;
**[run]**: probed on scratch files with the release CLI (the SW-3288 lane's for text prefixes);
**[argued]**: reasoned, not runnable until a checker accepts the program.

## 0. Summary

**The problem.** The kernel's termination check refuses `arguments.map (item =>
item.value.layout)`, so the toy formatter (`tools/toyfmt`) has a hand-written helper per list in
its tree (`itemDocs`, `statementLines`, `dumpItems`); the real formatter, with 94 node kinds,
would repeat this everywhere. Separately, `| "ab" ++ rest => 1 + count rest` on `Text` is refused,
though the `List Char` version passes.

**The change (recommended).** Three widenings of the kernel's termination check, and one guard
that keeps the kernel's evaluator stopping on open terms:

1. **A field read with a dot counts as a part**: the kernel recognises a record's accessor from
   its checked body, so `Item.value item` is smaller than `item` (§2.1).
2. **A function that only calls its argument on parts of a list passes that on.** The kernel works
   out once per checked definition (`List.map`) which function parameters it only applies to
   parts of which list; a lambda passed there gets its variable marked smaller (§2.2).
3. **A one-field wrapper around a strict part is smaller**: `MkText r`, with `r` reached from the
   matched text's characters through matched fields (§3).
4. **The guard (G1)**: evidence from rules 1 and 2 counts only for a call to a function that
   starts by matching on that parameter. Today every accepted cycle crosses a stuck `case`, which
   is what stops the kernel unfolding a recursive call on an unknown value for ever; rules 1 and 2
   would break that without it (§2.3).

**What it should do.** The toy formatter's three helpers go, and its rules read as the spec does
(§1). `count` on `Text` checks as written. The kernel term is the program as written, so `rfl`,
`test`, arm equations and every `List.map` lemma apply unchanged; no fuel, no generated copies.
Estimated cost: about 22-24 Opus lane hours in the kernel and its tests, a Fable review of the
implementation, and small Sonnet stages (§5).

## 1. The running example

`tools/toyfmt/src/Toy/Syntax/Tree.sw` defines Sprig's tree as five types defined together:
`Expr` (with `Call (callee: Expr) (arguments: List Item)`), the record `Item = { comments, value:
Expr, trailing }`, `Statement`, `Body = { statements: List (Spaced Statement) }` and
`Declaration`. The rules (`Fmt/Rules.sw`) are one recursive group. Today **[checked]**:

```
def itemDocs: List Item → List Doc
  | [] => []
  | [{ comments, value, trailing }] => [itemDoc comments value.layout Empty trailing]
  | [{ comments, value, trailing }, ..rest] => [itemDoc comments value.layout (Doc.text ",") trailing, ..itemDocs rest]
```

and `statementLines` threads an index by hand for the same reason. What the author wanted, and
what this proposal accepts:

```
def itemDocs (items: List Item): List Doc :=
  items.mapWithIndex (index item =>
    let comma := if index + 1 == items.length then Empty else Doc.text ","
    itemDoc item.comments item.value.layout comma item.trailing)

def Body.block (body: Body): Doc :=
  body.statements.mapWithIndex (index spaced => Doc.concat [lineStart index spaced.blankBefore, spaced.line.layout])
    |> Doc.concat
```

(`mapWithIndex` gets its signature in stage 4.) Each call here passes G1: `Expr.layout` and
`Statement.layout` start with a `case` on their argument, of types without eta. Two separate
things refuse this today, each **[run]** on a smaller probe:

- `item.value` is a call of the generated accessor `Item.value` (`crates/elab/src/records.rs:6`;
  `docs/core.md`, Terms: "The elaborator writes field access as a call of the record's
  accessor"), and the checker relates nothing to another definition's result. Even inside a
  pattern helper, `| [item, ..rest] => item.value.width + …` is refused; only the record
  *pattern* works, which is why the helpers spell out every field.
- `item` is bound by a lambda, and lambda-bound variables are "unknown" (`termination.rs:35`).

**What exists already.** `decreasing T.size p` with `items.attach.map (e => f e.value)`, `auto`
proving each call smaller (nested-data-types.md stage 3), works for a type alone in its group
**[run]**. But nothing is generated for types defined together (the formatter's tree); it compiles
to proof-carrying fuel, so equations are `f.unfold` and `test`/`rfl` run the fuel; and the
program must say `attach` and `.value`. It is for real well-founded recursion, not a tree walk.

## 2. Recursion through `map`

### 2.1 Rule 1: accessors

Field access is not `Term::Proj` in checked terms, and `Proj` is only well formed on a type with
record eta, which `Item` (one of five types defined together) hasn't got. So draft 1's "a `Proj`
whose target relates gives `<`" would never fire. Two ways: (a) the kernel recognises an
**accessor** by the shape of its checked body (after its parameters, one `case` on the last, one
branch, whose body is one of the branch's field variables) and treats a saturated call of it as a
part of its argument; (b) the elaborator emits `Proj`, allowed on types without eta, which
changes `infer_proj` and the eta rules. **Recommended: (a).** It is a small derived fact read from
the body (never from a flag the elaborator sets), cached like the eta flag, and sound because in a
closed run the call returns that field **[argued]**. A function field read by accessor and applied
(`x.rest y`) is a part only when the field's *declared* type returns a member of the matched
type's group, as `is_recursive_fn` already demands (compare [Agda #6654](https://github.com/agda/agda/issues/6654):
a proof of `⊥` by recursion through a large function-typed constructor field, via the forcing analysis;
the rule itself is Stitchwort's, not claimed to be Agda's). Accessor evidence is subject to
G1 (§2.3): `type R = { child: R, n: Nat }` with `def f (x: R) := f x.child` has no `case` and
would unfold for ever on an unknown `x` (review R6). About 80 lines plus the spec.

### 2.2 Rule 2: callback signatures

**The idea.** `List.map` is

```
def List.map: (xs: List a) → (f: a → {e} b) → {e} List b
  | [], f => []
  | [x, ..xs], f => [f x, ..List.map xs f]
```

Every use of `f` is either applied to a part of `xs`, or passed on unchanged to a recursive call
whose list is a part of `xs`. So in any run, `f` is only called on parts of the list `map` was
given. Rocq's guard checker handles this since 8.20 ([PR #17986](https://github.com/coq/coq/pull/17986), "Extrude
uniform parameters of inner fixpoints in guard condition check", milestone 8.20+rc1): it finds the
parameters of an inner fixpoint that stay the same across its recursive calls and carries their
recursive specification into the fixpoint's body. Stitchwort's check works on summaries, so it
summarises each definition once.

**The signature.** For a final definition `G`, a *callback position* is a parameter `j` of
function type with a *carrier* parameter `k`, and for each argument index `a` of the callback a
mark: `<` or `≤` the carrier (read as rank, §4), or unknown. `(j, k)` qualifies when every
occurrence of `j` in `G`'s body is one of:

1. applied, `j u₀ … uₙ`, each `uₐ`'s relation to `k` read by the ordinary walker. **An index's
   mark is the weakest over all occurrences, and an index not supplied at some occurrence is
   unknown** (F3: with `f rest rest + apply (f rest) big`, index 1 is fed `big` through `apply`);
2. passed as the variable itself, as argument `j` of a recursive call of `G` whose argument `k`
   relates to `k` (`≤` or `<`);
3. inside a lambda passed at a callback position of an earlier signed definition `H`, where rule 1
   or 2 holds with the lambda's binders marked as `H`'s signature says (so `List.sumBy`, a
   `foldLeft` with `acc x => acc + f x`, gets one).

Every other occurrence, in any term form, means no signature: in a type, under `J`, as a `let`'s
value, as an accessor's or `Proj`'s target, in a constructor, quotient form or any other call;
including `j` passed bare to a signed `H` (`map (map xs f) f`) (R2). Further restrictions:

- **Alone in its group** (R3): no signature for a definition whose group has more than one
  member, inlined lifted matches included. An inner `match` holding the recursive call makes a
  group of two, and checking rule 2 only on calls written in `G`'s own body is the mistake behind
  [Rocq issue #21682](https://github.com/rocq-prover/rocq/issues/21682) ("cross-calls in nested mutual
fixpoints": a proof of `False`, introduced by #17986 in 8.20, still present in 9.1.0); `termination.rs` already cites that lesson.
- **Only bodies the kernel checked and runs** (R4): none for a definition with a native, an axiom,
  a primitive (`Effect.pfix`), a body without termination checking, or from a run body; a
  `decreasing` definition gets none anyway (its callback goes to `f.%go`).
- **`≤` means "at most"**, not "equal" as `param: Some(i)` means today (`termination.rs:33`);
  every reader of `param` is rechecked.

**At a call.** When the walker meets `G … c … t …` with `c` at callback position `j` a lambda
`x₀ … xₙ => body`, and `t` at the carrier position related to the caller's parameter `i`, it walks
`body` with each marked `xₐ` related to `i`: `<` if either step is `<`, else `≤`. Unknown entries
(`foldLeft`'s accumulator) stay unknown. The evidence then counts only under G1.

**Why it is sound for closed runs.** Claim: in every run of `G`, every call of the callback gets,
at each marked index, a value of rank at most (or below) the carrier's. By induction on `G`'s run
(it was checked, so it terminates): rule 1 by the walker's invariant in `G`, rule 2 by induction
and transitivity, rule 3 by `H`'s claim. The review tried escaping closures, effects, swapped
carriers, higher-rank callbacks, proofs as carriers, index equations and dictionaries, and found
no break once F3 and R2-R4 are in the rule.

**Which std functions qualify** **[checked: bodies read in `List/Toolkit.sw`, `core/Helpers.sw`;
no natives bound for them in `registry.rs`]**. Clause bodies with no inner `match`, where `if` is
a call of `Bool.ifThenElse` with lambda branches (`docs/core.md`:426), so no lifted helper:
`map`, `filter` (`let keep := p x`, then the earlier `filterStep`), `foldLeft` (element index
only), `any`, `all`, `find`, `filterMap` (through `consSome`), `concatMap`, `forEach`; and by rule
3, `sumBy` and `count` (both `foldLeft` with a lambda). That each is alone in its group after
elaboration (effect rows, `@[tailrec]`) is to confirm in stage 2 **[inferred]**. **Not:**
`foldRight` (folds `reverseOnto xs []`), `mapWithIndex` (maps `withIndex`'s new pairs), anything
over `zip`, `sort` or `reverse`. `Def::run_body` exists (`List.length` runs as a loop,
`registry.rs:423`), so stage 4 can give `foldRight` a structural body and keep its loop.

**What the kernel sees.** The definition as written. No new term form or generated declaration;
evaluation, conversion, hashing and erasure unchanged; no existing hash moves. Signatures and
accessor facts are derived from final bodies, like the record eta flag (`docs/core.md`:288):
recomputed on cache replay, not hashed. Cost: one walk per definition with a function parameter
[inferred: negligible].

**Proofs about such functions.** `rfl` and `test` compute directly; arm equations come out as
for any definition; `List.map` lemmas apply with no bridge. A theorem can recurse through a
callback too: LFST's `allOf (x => motive x) items` (nested-data-types.md §9, refused today) would
pass, so `T.induct` for types defined together (stage 7) can be proved structurally.

**Errors.** A refused call under a lambda gets a note: `G` has no signature (and why: not alone
in its group, a native, an occurrence of the callback elsewhere), its list isn't a part, the
variable isn't marked, or G1's "match on `t` first".

### 2.3 G1: keeping the evaluator stopping (D3613)

**The problem (F2).** The kernel unfolds a definition with all its arguments unless a `case` in
its tree is stuck (`value.rs`, "Unfolding policy" in `docs/core.md`: "That makes conversion
terminate"). Today every accepted cycle crosses a `case` stuck on an unknown, since `<` only comes
from a `case` on a type without eta **[argued, review §1]**. Rules 1 and 2 put the `case` inside
another definition:

```
def Tree.forChildren: (t: Tree) → (f: Tree → Nat) → Nat
  | Leaf, f => 0
  | Node l r, f => f l + f r

def size (t: Tree): Nat := 1 + t.forChildren (c => size c)     -- c < t under rule 2
```

Closed runs stop. But `size t` on a variable unfolds (no `case`) to `1 + forChildren t (c => size
c)`, and reading it back goes under the lambda, where `size c` unfolds again, for ever
**[argued]**. Goals shown to the user and comparisons the names don't settle end in `E-RESOURCE`
after the whole budget. `type Rose = { label: Nat, kids: List Rose }` with `size r := 1 +
r.kids.sumBy (k => size k)` is the natural next program with this shape. The oracle can't see it:
the generated copy has the `case`.

**G1, checker side (recommended).** Evidence from a signed lambda's variable, or from an accessor,
counts for a call only if the member called has, at the root of its case tree, a `case` on the
parameter receiving it, on a type without eta, and the argument is that variable or accessors of
it (not a constructor around it). Otherwise: "match on `t` first". `size` becomes `| Leaf => 1 | t
=> 1 + t.forChildren (c => size c)`. The toy formatter passes unchanged (§1). Argument to write in
stage 1b: an infinite unfolding would need infinitely many fresh lambda (or accessor) values,
each the scrutinee of a root `case` that is stuck because it is unknown. Refuses some honest
programs; changes nothing in the evaluator.

**G2, evaluator side.** Mark a member accepted through such evidence as folded (`Def::fold`, as a
`decreasing` definition is), so `size c` stays folded under a binder. Read-back stops, but a
comparison that unfolds both sides still may not, and the flag becomes something the kernel
computes from a body and the evaluator obeys. More programs pass; more to trust.

## 3. Rule 3: recursion on a text's rest

**Why it fails.** `Text` is `| MkText (chars: List Char)` (`std/core/Text.sw:14`) **[checked]**.
A prefix arm compiles to a case on `MkText cs`, cases on `cs`'s characters, and `let rest :=
MkText r`, so `count rest` is `count (MkText r)`. `r` is a part of `t`; `MkText r` is a new value,
and `rebuilt` accepts only a constructor rebuilt from *exactly* its matched fields. `| MkText [_,
..cs] => 1 + drop1 (MkText cs)` is refused too **[run]**. Today's workaround, `decreasing
t.length` with `auto` proving each call, works **[run]**.

**The rule (R7 wording).** If an enclosing match took `s` (related to parameter `i`) apart as
`C v`, and

1. `C` has **exactly one field, counting every field**: implicit, proof and erased ones
   (`MkChar code valid` has two; beside a proof, the data field doesn't determine rank);
2. `u` is **strictly inside `v`, that match's field**: reached from `v` by at least one step (`u =
   v` is `rebuilt`, `≤`; "smaller than the same parameter" isn't enough: `| Wrap (Two a (Wrap v))
   => f (Wrap (Two a (Wrap v)))` would pass as `<` though it is the parameter);
3. every step is a matched field or a recursive function field applied, **not** a signed
   lambda's variable or an accessor (otherwise F2 returns in a form G1's root test misses:
   `| MkW v => tails v (u => f (MkW u))`),

then `C u < i`, whether `s` is `≤` or `<` `i`. Soundness by rank, the height of a value's constructor tree (it exists because values are
well founded, the assumption the check already makes): rank(`C u`) = rank(`u`) + 1 < rank(`v`) + 1
= rank(`s`) ≤ rank(`i`). Every existing rule is rank-monotone. On open terms the match from `v` to
`u` is stuck on an unknown `v` (on `List`, also once `Text` gets eta, SW-1644), so evaluation
stops. Records like `type Name = { text: Text }` get it too. The walker needs each matched field to
remember the variable it came from (a `parent` on `Info`): about 60 lines. The review found it
sound as stated.

**Alternatives.** (T2) a worker on `List Char` plus a wrapper made by the elaborator: nothing
trusted, but only for prefix patterns, and equations show the worker; it is the referee for rule 3
in stage 6. (T3) retry with `decreasing t.length` automatically: fuel in a program that didn't
ask. (T4) special-case `Text`: the same rule, narrower.

## 4. Invariants, stated once

The checker's header and `docs/core.md` would say: *`<` relates two values only when the first's
rank is below the second's in every run, `≤` when at most; evidence comes only from terms (a
match's fields, a recursive function field applied, a matched constructor rebuilt, a one-field
constructor around a strict part, an accessor applied, a callback's variable at a signed
position).* And a second, stated for the first time: *every accepted cycle of calls crosses a
`case`, at the root of a member, on a type without eta, whose scrutinee is the evidence's
variable*, which the unfolding policy relies on. G1 is what keeps it for the two new kinds of
evidence.

## 5. Stages

| # | What | Where | Model | Est. |
|---|---|---|---|---|
| 1a | Rule 3 with R7's three conditions; invariant as rank; `docs/core.md`; accept `count` and `drop1`; must-reject R7's `Wrap (Two a (Wrap v))` and a two-field (`MkChar`-like) rebuild | kernel | Opus | 3 h |
| 1b | Rule 1 (accessor recognition from bodies, declared type for function fields) with G1 and the second invariant; must-reject R6's `f x.child` and `| t => …` without a root case | kernel | Opus | 5 h |
| 2 | Rule 2 with F3, R2-R4, G1 on lambda evidence; errors; `docs/core.md`, `docs/syntax.md`, the guide's recursion page. Must-reject: a callback stored in data, applied to the accumulator, to a reversed list, passed on wrapped, a recursive call with a different function; F3's `apply (f rest) big`; R2's `map (map xs f) f` and each other term form; R3's growing carrier under an inner `match`; R4's native-bodied `G`; F2's `size` and `tails` loops (refused by G1); R7.3's `MkW u` | kernel | Opus | 8-10 h |
| 6 | Tests: oracle "rule 2 accepts ⇒ the separately written copy passes today's check" (failure to build the copy fails the property); a rule 1 referee (copy rewritten to record patterns) and a rule 3 referee (T2's worker); P1, every accepted generated program run on random closed inputs under a step budget; P2, read-back of `x => f x` and comparison with a renamed copy finish within budget. The generator writes partial applications, inner matches, growing carriers, callbacks passed on, bigger arguments | tests | Opus | 6 h |
| R | Review of 1b and 2's implementation before merge (D2364) | paper | Fable | 2 h |
| 3 | Eta-expand a bare or partial occurrence of a group member (`items.map Declaration.layout`) | elaborator | Sonnet | 1-2 h |
| 4 | `mapWithIndex` structural; `foldRight` structural with its loop as run body; a test each that callback recursion passes | std | Sonnet | 2 h |
| 5 | Dogfood: drop `itemDocs`, `statementLines`, `dumpItems`; `NOTES.md` | toyfmt | Sonnet | 1 h |
| 7 | Later: `T.size`/`T.induct` for types defined together, via `allOf`-style recursion | elaborator | Opus | own ticket |

1a and 3 can start at once (1a needs only D3612). 1b needs D3613; 2 follows 1b; 6 is written
beside 1b and 2 and passes before 2 merges; R before 1b and 2 merge; 4 and 5 follow 2.

## 6. Not covered, and later

- **Callbacks over a list built inside** (`zip`, `withIndex`): a "same elements" signature. **A
  helper that returns parts** (friction 2's `Body.single`): a result summary, which rule 1's
  accessor recognition is the smallest case of. Both wait for a program that needs them.
- **Mutual library functions**: no signatures (R3); revisit only with every member walked by
  rules 1-3, as Rocq's fix ([#21684](https://github.com/rocq-prover/rocq/pull/21684), "Detect cross-calls in computation for
  uniform arguments of nested mutual fixpoints") looks at calls between the members.
- **G2**, if G1 proves too strict in practice.

## 7. Options weighed (unchanged from draft 1, short)

**A** (rules 1-3, recommended) trusts new kernel code, Rocq's side, with Rocq's history; hence the
restrictions above, the referees and the review. **B** (the elaborator copies `G` per call site
into the group) trusts nothing new but shows `%layout.%map1` in every unfolding and needs a bridge
lemma for each `map` fact; it is stage 6's oracle. **C** (`decreasing` with `attach` inserted, Lean
4's route since 4.18: [v4.18.0 notes](https://lean-lang.org/doc/reference/latest/releases/v4.18.0/), PR #6744, the `wf.preprocess`
option, [reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)) compiles structural recursion to fuel and needs `T.size` for groups first.
**D** (per-list helpers) is today, and Lean's answer for structural nested recursion too (its [v4.12.0 notes](https://raw.githubusercontent.com/leanprover/lean4/v4.12.0/RELEASES.md)
define `Tree.size` together with a helper `Tree.list_size : List Tree → Nat`).

## 8. Changes from draft 1

F1: rule 1 is accessor recognition, not `Proj` (§2.1). F2: G1 and the second invariant (§2.3, §4),
D3613. F3/R1: unsupplied indices are unknown. R2: every other term form. R3: alone in its group,
std list checked. R4: kernel-run bodies only. R6: under G1, declared types for function fields.
R7: rule 3's three conditions. Stage 6 gains P1, P2 and the two referees; stage 2 the review's
must-reject programs; a Fable review before merge. Estimates up from ~10 to ~24 Opus hours.

## 9. Decisions for Matt

**D3611. Recursion through `map` and friends: widen the kernel's termination check with
accessors (rule 1) and callback signatures (rule 2), under the guard D3613 chooses?** *The
problem:* tree code needs a hand-written helper per list in the tree, since the check can't see
that `items.map (item => item.value.layout)` only recurses on parts of `items`. *The change:* the
kernel recognises record accessors from their bodies, and learns once per definition which
function arguments it only calls on parts of which list (alone in its group, kernel-run bodies
only); a lambda passed there may recurse on its variable. About 400 new trusted lines, two
invariants stated, the review's must-reject programs, referees and run-under-budget properties,
and a Fable review before merging. *What it should do:* the toy formatter loses its three helpers
[estimated]; `map` lemmas, `rfl` and equations apply directly. [rec: yes, option A with G1]

**D3612. Recursion on a text's rest: treat a one-field constructor around a strict part as
smaller?** *The problem:* `| "ab" ++ rest => 1 + count rest` is refused on `Text`, the first thing
a lexer author writes. *The change:* the kernel accepts `MkText r` as smaller than the text when
`C` has exactly one field (counting implicit, proof and erased ones) and `r` is reached from the
matched field through matched fields only; "smaller" read as rank. *What it should do:* `count`
checks as written, with no `decreasing` and no `List Char` detour; one-field record wrappers
behave the same. [rec: yes, stage 1a]

**D3613. When recursion's evidence comes from inside another function, where does the kernel
keep unfolding finite?** *The problem:* with rules 1 and 2, `def size (t: Tree) := 1 +
t.forChildren (c => size c)` terminates on real trees, but on an unknown `t` the kernel unfolds it
for ever when showing a goal or comparing terms (each time ending in `E-RESOURCE`). *The change:*
G1, the checker accepts such evidence only for a call to a function whose first step is a match on
that argument, so `size` must be written `| Leaf => 1 | t => 1 + t.forChildren …` ("match on `t`
first"); or G2, the evaluator keeps such functions folded, so more programs pass but the kernel
gains an evaluation rule and comparisons may still not stop. *What it should do:* with G1 the
toy formatter and every tree walk that starts with a match pass unchanged, and nothing in the
evaluator changes. [rec: G1]
