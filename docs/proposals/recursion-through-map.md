# Proposal: recursion through `map`, and on a text's rest

**Status:** draft 1, 15 November 2026 (SW-3359, SW-3365). Nothing built; D3611, D3612 at the end.
Related: [mutual-recursion.md](mutual-recursion.md) §6, [nested-data-types.md](nested-data-types.md)
(draft 1's deferred option C, "termination looks inside `map`"; stage 3),
[well-founded-recursion.md](well-founded-recursion.md) (stages 3a, 3b), [SW-3288
review](../reviews/SW-3288-text-prefix.md) finding 6. **[checked]**: source at `ae7a3b341`;
**[run]**: probed on scratch files with the release CLI (the SW-3288 lane's for text prefixes).

## 0. Summary

**The problem.** The kernel's termination check refuses `arguments.map (item =>
item.value.layout)`, so the toy formatter (`tools/toyfmt`) has a hand-written helper per list in
its tree (`itemDocs`, `statementLines`, `dumpItems`); the real formatter, with 94 node kinds,
would repeat this everywhere. Separately, `| "ab" ++ rest => 1 + count rest` on `Text` is refused,
though the `List Char` version passes.

**The change (recommended).** Three small widenings of the kernel's termination check, argued
against one stated invariant, plus small library and elaborator stages:

1. **A record field counts as a part**: `item.value` is smaller than `item` (§2.1).
2. **A function that only calls its argument on parts of a list passes that on.** The kernel works
   out once per checked definition (`List.map`) which function parameters it only applies to
   parts of which list; a lambda passed there gets its variable marked smaller, as if matched out
   of the list (§2.2).
3. **A one-field wrapper around a smaller part is smaller**: `MkText r`, with `r` strictly inside
   the matched text's characters (§3).

**What it should do.** The toy formatter's three helpers go, and its rules read as the spec does
(§1). `count` on `Text` checks as written. The kernel term is the program as written, so `rfl`,
`test`, arm equations and every `List.map` lemma apply unchanged; no fuel, no generated copies.
Estimated cost: about 10 Opus lane hours in the kernel, plus small Sonnet stages (§5).

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

(`mapWithIndex` gets its signature in stage 4.) Two separate things refuse this today, each
**[run]** on a smaller probe:

- `item.value` is a projection, and "a projection gives no evidence of descent"
  (`crates/core/src/termination.rs:516`, `docs/core.md`:313). Even inside the pattern helper,
  `| [item, ..rest] => item.value.width + …` is refused; only the record *pattern* `{ comments,
  value, trailing }` works. That is why the helpers spell out every field.
- `item` is bound by a lambda, and lambda-bound variables are "unknown" (`termination.rs:35`):
  nothing says `List.map` only calls its function on elements of `items`.

**What exists already.** `decreasing T.size p` with `items.attach.map (e => f e.value)`, `auto`
proving each call smaller (nested-data-types.md stage 3), works for a type alone in its group
**[run]**. But nothing is generated for types defined together (the formatter's tree); it compiles
to proof-carrying fuel, so equations are `f.unfold` and `test`/`rfl` run the fuel; and the
program must say `attach` and `.value`. It is for real well-founded recursion, not a tree walk.

## 2. Recursion through `map`

### 2.1 Projections

The rule the checker keeps (`termination.rs` header, `docs/core.md`:253): "smaller than" relates
two variables only when, in every run, the first's value is a proper constructor subvalue of the
second's. A projection `x.f` of a record value *is* a field of it. So: **if `x` is related to
parameter `i` (equal or smaller), `x.f` is smaller than `i`**. In `relate`, a `Term::Proj` whose
target relates gives `Lt`. The exclusion was conservative ("conservative, never unsound", says
the comment). A projection is the record pattern's field by another route **[inferred]**, so this
adds nothing the pattern form doesn't allow. About 20 lines, plus docs and two tests.

### 2.2 Callback signatures

**The idea.** `List.map` is

```
def List.map: (xs: List a) → (f: a → {e} b) → {e} List b
  | [], f => []
  | [x, ..xs], f => [f x, ..List.map xs f]
```

Every use of `f` in its body is either applied to a part of `xs`, or passed on unchanged to a
recursive call whose list is a part of `xs`. So in any run, `f` is only ever called on parts of the
list `map` was given. If a caller's list is smaller than its parameter `e`, every value `f` sees is
too. Rocq's guard checker does this since 2024 by looking inside inner fixpoints (PR #17986,
nested-data-types.md draft 1 §4.2). Stitchwort's check works on summaries, so it can summarise
each definition once and use the summary at each call.

**The signature.** For a final definition `G`, a *callback position* is a parameter `j` of
function type together with a *carrier* parameter `k`, and for each argument index `a` of the
callback, whether that argument is smaller than (`<`) or at most (`≤`) the carrier, or unknown.
`(j, k)` qualifies when every occurrence of `j` in `G`'s body is one of:

1. applied, `j u₀ … uₙ`; each `uₐ`'s relation to `k` is read by the ordinary walker (and recorded
   in the signature as the weakest seen over all occurrences);
2. passed unchanged (the variable itself) as argument `j` of a recursive call of `G`, whose argument
   `k` relates to `k` (`≤` or `<`);
3. inside a lambda passed at a callback position of an *earlier* definition `H` that has a
   signature, where rule 1 or 2 then holds with the lambda's binders related as `H`'s signature
   says (this is how `List.sumBy`, a `foldLeft` with `acc x => acc + f x`, gets one).

Any other occurrence (stored in data, returned, passed anywhere else, applied to something
unrelated) means no signature for that pair. This is the checker's existing discipline for
members ("every occurrence is a call") applied to a parameter.

**At a call.** When the walker meets `G … c … t …` with `c` at callback position `j` a lambda
`x₀ … xₙ => body`, and `t` at the carrier position related to the caller's parameter `i` (`≤` or
`<`), it walks `body` with each `xₐ` whose entry is `<` or `≤` related to `i`: `<` if either step
is `<`, else `≤`. Unknown entries (`foldLeft`'s accumulator) stay unknown. So in
`items.mapWithIndex (index item => … item.value.layout …)`, `item < e`, `item.value < e` by 2.1,
and the call is smaller. A lifted `match` inside the lambda (a clause lambda) is inlined as now,
its parameter related to its argument.

**Why it is sound.** Claim: in every run of `G` applied to arguments, every call of the callback
at `j` gets, at each index marked `<`/`≤`, a value that is a part of (or equal to) the carrier
argument's value. By induction on `G`'s run (it terminates; it was checked): rule 1 holds by the
walker's invariant inside `G`; rule 2 by the induction hypothesis and transitivity; rule 3 by
`H`'s claim. The caller's lambda variable is then a part of `t`'s value, which is related to `i`,
so the invariant ("a proper constructor subvalue, in every run") holds for it. A callback that
escapes and is called later is still called on such values, and the checker already accepts calls
under lambdas that escape. Signatures are only read from definitions checked earlier, never from
the group being checked, so there is no circularity.

**What gets one (std as it is, [inferred] from `List/Toolkit.sw`):** `map`, `filter` (through
`let keep := p x`), `foldLeft` (index 1 only), `sumBy`, `any`, `all`, `forEach`, and any user
function of the same shape. **What doesn't:** `foldRight` (it folds `reverseOnto xs []`),
`mapWithIndex` (it maps `withIndex`'s new pairs), anything over `zip`, `sort` or `reverse`: their
callbacks see a list built inside. Stage 4 makes `mapWithIndex` and the like structural;
`foldRight` keeps its stack-safe loop, so it waits for a run-body attribute or §6.

**What the kernel sees.** The definition as written: `List.map items (item => Expr.layout
item.value)`. No new term form or generated declaration; evaluation, conversion, hashing and
erasure are unchanged, and no existing hash moves. The signature is derived from a final
definition's body, like the record eta flag (`docs/core.md`:288): recomputed on cache replay,
not hashed. Cost: one walk per definition with a function parameter [inferred: negligible].

**Proofs about such functions.** Because the term is the program:

- `rfl` and `test` compute directly (no fuel); arm equations (`equations.rs`) come out as for any
  definition, `layout (ListLiteral items) = … items.map (item => item.value.layout) …`;
- `List.map` lemmas (`lengthMap`, `mapMap`, `memMap`) apply with no bridge lemma;
- induction "for every element" comes from `T.induct`/`T.inductMem` where generated. A theorem can
  also recurse through a callback: LFST's `allOf (x => motive x) items` (not in std yet), refused
  today (nested-data-types.md §9), would get a signature. So a mutual group's induction principle
  can be proved structurally, and generating `T.induct` for types defined together (the
  formatter's case, not covered today) becomes a short follow-up.

**Errors.** A refused call under a lambda gets a note: `G` has no signature, its list isn't a
part (`items.reverse`), or the variable isn't marked (`foldLeft`'s accumulator).

### 2.3 Options weighed

| | A: callback signatures (rec.) | B: generated copies | C: `decreasing` + auto `attach` | D: per-list helpers (today) |
|---|---|---|---|---|
| What the user writes | `items.map (i => i.value.f)` | same | same, if inserted automatically | a helper per list |
| What the kernel sees | the program | a copy of `map` per call site, in the group | fuel, `%go`, respects proofs | the helpers |
| Kernel change | yes, ~300 lines in `termination.rs` | none | none | none |
| Equations, `rfl` | definitional | definitional over the copy; bridge lemma to `map` | `f.unfold`; fuel computes | definitional over helpers |
| Types defined together | yes | yes | needs `T.size` for groups first | yes |
| Effort [estimated] | 1-1.5 Opus days | ~2 days | ~3 days | n/a |

**B** (the elaborator specialises `G` to the lambda as a new group member, so today's check
accepts it) trusts nothing new, but leaks: unfolding `layout` shows `%layout.%map1 items`, every
std `map` lemma needs a generated bridge first, and each call site adds a declaration. It is the
right *test oracle* for A (every program A accepts, B's copy must pass the unchanged check), as
nested-data used Lean's translation. **C** is Lean 4's route for `map` (well-founded recursion,
`attach` inserted by `wf_preprocess`, Lean 4.18 #6744; well-founded-recursion.md 3a.3): heavy and
indirect for recursion that is structural. A widens what the kernel trusts; the argument is short
and local, and Rocq's history of guard-checker bugs (nested-data draft 1 §4.2) is why it comes
with the oracle and must-reject cases.

## 3. Recursion on a text's rest

**Why it fails.** `Text` is `| MkText (chars: List Char)` (`std/core/Text.sw:14`)
**[checked]**. A prefix arm compiles to a case on `MkText cs`, cases on `cs`'s characters, and
`let rest := MkText r`, so `count rest` is `count (MkText r)`. `r` is a part of `t`; `MkText r` is a
new value, and `rebuilt` accepts only a constructor rebuilt from *exactly* its matched fields.
`| MkText [_, ..cs] => 1 + drop1 (MkText cs)` is refused too **[run]**. Today's workaround,
`decreasing t.length` with `auto` proving each call, works **[run]**.

**The fix (recommended): a one-field constructor around a smaller part is smaller.** If an
enclosing match took `s` (related to parameter `i`) apart as `C v`, `C` has exactly one field, and
`u` is strictly inside `v` (a field of a field of `v`, …), then `C u < i`. It isn't a part of
`s`, so the invariant must be read through *rank*: the height of a value's constructor tree, an
ordinal, which exists because every value is well founded (the assumption the check already
makes). Every existing rule respects rank (a part has smaller rank; a rebuilt value has equal
rank), so SCT's argument goes through unchanged with rank as its order. For the new rule:
rank(`C u`) = rank(`u`) + 1 < rank(`v`) + 1 = rank(`C v`) ≤ rank(`i`). **Exactly one field**
matters: with two, rank is the larger field's plus one, and shrinking the smaller one need not
lower it. Records like `type Name = { text: Text }` get it too. The walker needs each matched
field to remember which variable it came from (a `parent` on `Info`), about 60 lines.

**Alternatives.** (T2) A worker on `List Char` plus a wrapper, made by the elaborator: nothing
trusted, but only for prefix patterns, and every equation and goal shows the worker. (T3) Retry
with `decreasing t.length` automatically: fuel and `unfold` in a program that didn't ask. (T4)
Special-case `Text` in the checker: the same rule, narrower. The one-field rule is general.

**Run time.** Unchanged; the review's slice change (`Text.drop` in the runtimes) is independent.

## 4. Invariant, stated once

The checker's header and `docs/core.md` would say: *`<` relates two values only when the first's
rank is below the second's in every run, `≤` when at most; evidence comes only from terms (a
match's fields, a projection, a recursive function field applied, a matched constructor rebuilt,
a one-field constructor around a strict part, a callback's variable at a signed position).* For
nested types, the existing assumption (values are well founded) is all rank needs.

## 5. Stages

| # | What | Where | Model | Est. |
|---|---|---|---|---|
| 1 | Projections give descent (2.1); the one-field rule (3); invariant restated; `docs/core.md`; accept and soundness examples (`count`, the P4 helper with `item.value`, a two-field rebuild refused) | kernel | Opus | 3 h |
| 2 | Callback signatures (2.2): derivation, use at calls, cache replay, the notes in errors; `docs/core.md`, `docs/syntax.md` and the guide's recursion page; must-reject cases (callback stored in data, applied to the accumulator, to a reversed list, passed on wrapped, a recursive call with a different function) | kernel | Opus | 6-8 h |
| 3 | Eta-expand a bare or partial occurrence of a group member (`items.map Declaration.layout`) before the kernel sees it, replacing that error | elaborator | Sonnet | 1-2 h |
| 4 | Structural definitions for std's callback functions that go through a built list (`mapWithIndex` **[checked]**; survey the rest); a test per function that a callback recursion passes | std | Sonnet | 2 h |
| 5 | Dogfood: drop `itemDocs`, `statementLines`, `dumpItems`; note in `NOTES.md` | toyfmt | Sonnet | 1 h |
| 6 | Oracle: a fuzzer property "A accepts ⇒ B's copy is accepted by the unchanged check", seeded with stage 2's examples; Overmind runs it | tests | Opus | 3 h |
| 7 | Later: `T.size`/`T.induct` for types defined together, via `allOf`-style recursion | elaborator | Opus | separate ticket |

Stages 1 and 3 are independent and can start at once; 4 and 5 follow 2; 6 can be written beside
2 and must pass before 2 merges.

## 6. Not covered, and later

- **Callbacks over a list built inside** (`foldRight`, `zip`, `withIndex`): a second signature
  kind, "the result's elements are parts of the carrier". And **a helper that returns parts**
  (friction 2's `Body.single`): a "result relation" summary. Both wait for a program that needs
  them; matching inline works meanwhile.
- **Function fields reached by projection** (`x.rest y`): rare; add with 2.1 if cheap.
- **Mutual library functions**: v1 signs only a definition alone in its group (rule 2 is
  self-recursion).

## 7. Decisions for Matt

**D3611. Recursion through `map` and friends: widen the kernel's termination check (2.1, 2.2)?**
*The problem:* tree code needs a hand-written helper per list in the tree, since the check can't
see that `items.map (item => item.value.layout)` only recurses on parts of `items`. *The change:*
the kernel learns, once per definition, which function arguments it only calls on parts of which
list, and lets a lambda passed there recurse on its variable; record fields count as parts. About
300 trusted lines, argued against the existing invariant, tested against a generated-copy oracle
(the alternative that trusts nothing new shows those copies in every proof). *What it should do:*
the toy formatter loses its three helpers [estimated]; `map` lemmas, `rfl` and equations apply
directly. [rec: yes, option A, stages 1-6]

**D3612. Recursion on a text's rest: treat a one-field wrapper around a strict part as smaller
(§3)?** *The problem:* `| "ab" ++ rest => 1 + count rest` is refused on `Text`, the first thing a
lexer author writes. *The change:* the kernel accepts `MkText r` (any one-field constructor) as
smaller when `r` is strictly inside the matched value's field, reading "smaller" as rank. *What it
should do:* `count` checks as written, with no `decreasing` and no `List Char` detour; any
one-field record wrapper behaves the same. [rec: yes, in stage 1]
