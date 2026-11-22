# Proposal: tools/fmt's list twins written with `List.all` and `List.map`

**Status:** note, 22 November 2026 (SW-4563, from SW-4559's row 4). No decision asked yet; see
§6. Marks: **[run]** probed with the main checkout's release CLI on scratch files (reproduced
below); **[measured]** counted by script over `tools/fmt/src` at `17c3f8dbc` (Tests/ and
MustAccept* left out, proof lines by `docs/reviews/SW-4519/count.py`); **[read]** from source;
**[estimated]** judgement.

## 0. Summary

The formatter's tree functions (`Expr.within1`, `Expr.calm`, `Expr.shaped`, `Expr.words`, ...)
each have a hand-written list twin (`allWithin1`, `calmAll`, `allShaped`, `itemsWords`), so
std's `List.all`/`List.map` lemmas don't apply to them. Writing the twins as `items.all (e =>
e.within1)` needs **recursion through a std function's callback**, which the kernel's
termination check refuses today. That is exactly rule 2 of
[recursion-through-map.md](recursion-through-map.md) (D3611, deferred by Matt on 15 Nov 2026),
which is kernel work. With it, I estimate **about 200 proof lines saved** on the four named
twins (of 1,723 in the theorems that mention them), not "most of it": most of those lines are
inductions over the printer's own list functions, which aren't maps, and use the twin only as a
hypothesis split with `Bool.andLeft`/`Bool.andRight`. No top theorem would be restated and no
program would compute anything different.

## 1. What the checker accepts today

The check is the kernel's, `crates/core/src/termination.rs`, specified under "Termination" in
`docs/core.md` (Data groups section): a recursive call is smaller when its argument is a field
matched out of the parameter (whatever its type, so `x` from `[x, ..rest]` matched out of a
`List Expr` field counts), a recursive function field applied, a matched constructor rebuilt
(`≤`), or a one-field wrapper around a strict part (rule 3 of recursion-through-map.md,
SW-3376). A lambda-bound variable is unknown. Probes, on `type E = | Leaf (n: Nat) | Node
(items: List E)` [run]:

| File (scratch) | Shape | Result |
|---|---|---|
| `e1-twin.sw` | `Node items => allOk items`, `allOk` hand-written | checked |
| `e2-all-lambda.sw` | `Node items => items.all (e => e.ok)` | `E-TERMINATION`: "the 1st argument, `e`, isn't seen as smaller" |
| `e3-all-bare.sw` | `items.all E.ok` | `E-TERMINATION`: "`E.ok` is used here without all its arguments" |
| `e4-map.sw` | `Node (items.map (e => e.calm))` | `E-TERMINATION`, as e2 |
| `e5-concatmap.sw` | `items.concatMap (e => e.words)` | `E-TERMINATION`, as e2 |
| `e7-alone-attach.sw` | `decreasing E.size x`, `items.attach.all (e => E.ok e.value)` | checked |
| `e6-group-attach.sw` | the same, `E` defined together with `S = Say (e: E)` | `E-UNKNOWN-NAME`: no `E.size` |
| `e8-thm-callback.sw` | a **theorem** `calmOk` proving its `Node` arm with `List.allTrue items _ (x => calmOk x)` | `E-TERMINATION` on `calmOk x` |
| `e9-bridge-only.sw` | bridge lemmas `allOk xs = xs.all (e => e.ok)`, `calmAll xs = xs.map (e => e.calm)` (3 lines each), then `List.allMapBool` and `List.allTrue` for one arm, the pointwise fact given as a hypothesis | checked |

So:

- **Nested recursion through `List.all`/`map`/`concatMap` is refused**, in definitions and in
  theorems alike (e8: a proof by recursion through a std lemma's callback is the same check).
- **The `decreasing … attach` route** (nested-data-types.md stage 3) works only for a type alone
  in its group. The formatter's `Expr` is defined together with `Statement`, `Let`, `Arm`,
  `Pattern`, `Param`, `HandlerClause`, ... (`Syntax/Expr.sw`, `Block (first: Statement)`), so it
  has no generated size [run, e6; `Fmt/Rules.sw:309`'s `Expr.size` is a word count, not a
  measure]. It would also put fuel into the programs (equations through `f.unfold`), which the
  formatter's `byComputing` proofs would feel.
- **Bridges work today** (e9), but only where the pointwise fact is not itself the recursive
  theorem, i.e. not for twins of recursive tree functions (§3).

## 2. Which definitions could change

The four named twins, each a fold of its tree function [read]:

| Twin | Today | Would be | Called from |
|---|---|---|---|
| `allWithin1` (`Fmt/Slice1.sw:97`) | `[] => True`, `expr.within1 && allWithin1 rest` | `items.all (e => e.within1)` | `Expr.within1` (Tuple, ListOf, App arms) |
| `allShaped` (`Fmt/Predicates.sw:205`) | the same with `shaped` | `items.all (e => e.shaped)` | `Expr.shaped` |
| `calmAll` (`Fmt/Predicates.sw:111`) | `[expr.calm item, ..calmAll item rest]` | `items.map (e => e.calm item)` | `Expr.calm`, `calmLead`, `pickItems` |
| `itemsWords` (`Fmt/Rules.sw:269`) | `item.words ++ itemsWords rest` | `items.concatMap (e => e.words)` | `Expr.words` and the printer |

Beyond these, a scan finds **75 such twins over the tree's types** in `tools/fmt/src` (`all…`,
`…Within3`/`4a`/`…`, `armsWords`, `patternsWords`, `statementsWords`, `blankArms`, `mapAll`,
`spineAll`, `argsKinds`, ...), named in the statements of **224 theorems, 2,708 proof lines**
[measured]. All the ones I spot-checked are mutual with their tree function (`Expr.closed`/
`allClosed`, `Expr.sound`/`allSound`, `Expr.kinds`/`argsKinds`, ...), so they need the same
change. Twins over non-recursive element types (`lineAll`, `plainAll`, `exprAll` over `Item`,
`notesSound` over `Note`) could be `List.all` today; they are few and their proofs short.

Not maps, so out of scope however the checker changes: the printer's list functions that thread
state (`argumentDocs`, `cells`, `brokenItems`, `commaSlots`, `commaSpacing`, `calmLead`'s first
item), and the Prop-valued twins (`AllElKept`, `EachPasses`, ...), which would be `List.All`, a
separate question.

## 3. What it would save

Theorems whose statement names one of the four: **128 theorems, 1,723 proof lines**
[measured; SW-4559 counted 138 and 1,983 with a wider match]. By what their statements are about:

- **48 theorems, 266 lines, about twins only** [measured, by which fmt functions the statement
  names]: `calmAllWithin`, `withinAllCalm`, `calmAllLength`, `takeWithin`, `allGoodWithin`,
  `shapedAllCalm`, `itemsWordsAll`, ... Most are a list induction whose step calls the tree
  lemma (`calmAllWithin`'s step is `rewrite exprCalmWithin first item, calmAllWithin rest
  item`), and the tree lemma calls them back. With rule 2 the twin theorem goes and the tree
  lemma's arm uses std directly: `rewrite List.allMapBool items …` then `List.allCong items …
  (x => exprCalmWithin x item)` (`List.allImpliesBool` for the `within → within` ones,
  `List.lengthMap` for `calmAllLength`). Each such theorem is 2 to 9 lines today and costs about
  one line in its tree lemma after: **~200 proof lines saved**, plus ~100 lines of statements
  [estimated]. Today, without a kernel change, bridges (e9) would help only the few whose
  pointwise fact isn't recursive (`calmAllLength`, `takeWithin`, `calmAllEmpty`,
  `calmAllPlain` through the non-recursive `plainItemCalm`): about 20 lines, against 12 lines of
  bridges [estimated]. Not worth a lane.
- **80 theorems, 1,457 lines, about printer functions** (`argumentsFinish`, `speltCommas`,
  `bracketContentShape`, `cellsShape`, ...) [measured]. Their induction is over `argumentDocs`
  or `cells`, and `allWithin1` appears as a hypothesis split each step by `Bool.andLeft within`
  and `Bool.andRight within`. `List.all` is `if p x then List.all xs p else False`
  (`std/List/Toolkit.sw:207`), on which `Bool.andLeft` already works (`List.allImpliesBool`
  uses it, `std/List/Zip.sw:840`) [read], so these proofs stay as they are: **~0 saved**.

Across all 75 twins the same ratio (about 12% of the lines in theorems naming them) would give
**~300 proof lines** [estimated, untested beyond the four], plus the twins' own definitions
(~3 lines each).

## 4. What it would cost

**A kernel change.** Rule 2 of recursion-through-map.md (§2.2 there): the kernel derives, once
per checked definition, which function parameters it only calls on parts of which list
(`List.map`, `all`, `any`, `concatMap`, `filter`, `foldLeft`'s element, ... qualify by its
reading), and a lambda passed there may recurse on its variable; with **G1** (D3613: such
evidence counts only for a call to a member whose root `case` is on the receiving parameter,
which every formatter tree function and tree theorem satisfies, `match expr with` first). Rule 1
(accessors) is **not** needed here: the twins' lists are matched out by constructor patterns
(`Tuple _ items _ _`), not read with a dot. Cost from that note's table: stage 2 (8-10 Opus h),
the G1 part of 1b, stage 6's tests (6 h), a Fable review (2 h), `docs/core.md`; about **16 Opus
lane hours as estimated there**, which at the measured 0.28 actual/estimate ratio is perhaps 5
hours of agent time, plus new trusted kernel code (the bulk of D3611's ~400 lines).

**Open points for that work, from this question:**

- **Theorems need it too** (e8): a tree lemma that uses `List.allCong` with a recursive callback
  is checked by the same rule, so the std lemmas used must earn signatures. The rule refuses a
  callback occurrence "under `J`"; `List.allCong` and `List.allTrue` are proved with `rewrite ep
  x`, whose elaborated term may put `ep x` under a transport. If so they get no signature and
  need re-proving by `Eq.cong`/`Eq.trans` (a small std lane). `List.allImpliesBool` (plain
  `Bool.andIntro (implied first …)`) should qualify [read; to confirm in stage 2].
- `List.all` and `List.map` carry `@[tailrec]` and an effect row; that each is alone in its group
  after elaboration is still the note's open "[inferred]".
- A bare `items.all Expr.within1` is refused with its own message (e3); stage 3 of that note
  (eta-expanding a bare group member) makes it pass; until then the twins are written with a
  lambda.

**Then the formatter lane** (Sonnet, a few hours [estimated]): rewrite the 75 twins, delete the
twin theorems, re-prove their uses in the tree lemmas through std. Every definition's hash in
tools/fmt changes (migration cost doesn't count, D2303). Worth keeping the twin names as
one-line wrappers (`def allWithin1 (items: List Expr): Bool := items.all (e => e.within1)`) so
the 80 printer-function theorems keep their statements; `rewrite` looks for occurrences by outer
function, so std lemmas then need an unfold of the wrapper first, or the statements say
`items.all …` directly. That choice is the lane's.

## 5. Programs and proved statements (scope)

- **The programs compute the same values.** `items.all (e => e.within1)` and `allWithin1 items`
  agree on every list; `calmAll` is `map`; `itemsWords` is `concatMap`. The formatter's output,
  the grammar of each slice and what each driver accepts are unchanged. Nothing is refused that
  is accepted today.
- **No top theorem is restated.** `formatAccepts1`, `formatKeepsProgram1`, `formatIdempotent1`,
  `slice1Formats` and `slice1KeepsComments` don't name the twins [read: `Fmt/TopStatements.sw`,
  `Fmt/Accepts1.sw`]; they reach them only through `within1` and friends, whose meaning is the
  same. Intermediate statements that name a deleted twin theorem go with it; the rest keep
  their text if the names stay as wrappers.
- The Rust formatter is untouched, so the formatters stay in sync.

## 6. Recommendation

**The problem.** The formatter re-proves list induction for each tree function's list twin
(about 48 small theorems, 266 lines, for the four named), because the twins are hand-written,
and they are hand-written because the kernel refuses recursion through `List.all` or `List.map`.

**The change.** None in tools/fmt now. Record the formatter as a second user of D3611's rule 2
(recursion through a std function's callback, under G1, without rule 1), with these numbers, so
that if D3611 is taken up the formatter migration is its first dogfood after the toy formatter.
Don't add bridge lemmas meanwhile (about 20 lines saved for 12 written).

**What it should do.** If D3611 rule 2 lands (about 16 Opus hours estimated, kernel code and a
Fable review), the four twins and their 48 theorems collapse into std lemma calls: about 200
proof lines saved [estimated], about 300 across all 75 twins, out of 2,708 in theorems naming
them. The other ~85% of those lines are inductions over the printer's own functions and stay. On
its own that saving doesn't justify new trusted kernel code; together with D3611's other users
(the toy formatter's helpers, tree code in AoC, structural `T.induct` for groups) it is a
reasonable extra.
