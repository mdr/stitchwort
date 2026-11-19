# Slice 1's kinds of theorems in Lean 4 and Rocq, against Stitchwort (SW-4222)

Fable, 19 Nov 2026, for Matt's question of the same day. Read against
`main` at 909e34ccc. The ported samples are in
[`SW-4222-samples/`](SW-4222-samples/): `Sample.lean` (Lean 4.35.0, core
and `Std` only, no Mathlib) and `Sample.v` (Rocq 9.1.1 with its Stdlib
9.0.0), both from nixpkgs. Both check with no `sorry`, no `Admitted` and
no axioms (`Print Assumptions`: "Closed under the global context").

How claims are marked: **[measured]** run or counted by me today;
**[read]** taken from the file or page named; **[estimated]** my
judgement.

## In plain words (two minutes)

**What I did.** Not a port. I took 21 slice 1 theorems of the seven kinds
that make up most of the 6,031, cut their definitions down to what each
theorem touches, and proved the same statements in Lean and in Rocq,
each in the style its users would write. It took about five minutes of
clock time per system.

**The answer.** The same theorems are about **half the proof text** in
Lean and Rocq (302 lines in Stitchwort, 159 in Lean, 125 in Rocq
[measured]), and I would expect **somewhat fewer theorems**, two thirds to nine tenths
as many [estimated, low confidence]. They are not a different order of
difficulty: every statement carried over unchanged in shape, each
function still gets its lemma, and each system had its own snags (Lean's
verification tool is mid-rename and failed three ways before it worked;
Rocq needed a hand-written induction for the document type). For two of
the seven kinds Stitchwort is already as short or shorter: the case-split
"dispatchers" (`cases` is one word) and the printer's triples.

**Where the difference is.** Nearly all of it is in the parser walks, and
it has one cause. In Lean and Rocq a tool *walks the program for you*:
you state what a parser function gives, and the tool steps through its
body, applies the lemma already proved for each function it calls,
splits each `if` and `match`, and leaves only the facts that need
thought. Slice 1's longest walk in the sample, the comma list, is 46
lines in Stitchwort and a 3-line proof in Lean. And because the tool can
split a `match` inside a function, the parser need not be cut into one
named function per step: the sample's ten Stitchwort parser functions
are five in Lean, and the small lemmas about the leaves go (30 lemmas
to 23 for the sample).

**What to take on board,** in order of evidence:

1. **A walk step for proofs about effectful code**: follows a function's
   body, uses registered lemmas for the calls, steps through inner
   `if`s and `match`es. This is the retrospective's idea D, and it also
   removes the hand-written `[p := …] [j := …]` arguments (SW-4220).
2. **Induction that follows a function's own cases** ("functional
   induction"): the rule N proof falls from 29 lines to 15 and 12, and
   the guard-refinement trouble (SW-4047) does not arise.
3. **A closer for the leftovers** that uses the facts in scope and a
   standard set of list and Bool lemmas, so that helper lemmas such as
   `commaEnd`, `andOf` and `orOfFalse` need not exist (SW-3631's rule
   sets, taken further).

**What not to take.** Their way of writing effects (monads): Stitchwort's
direct style is not what costs the lines. Their finite-case tools: core
Lean has nothing as good as `cases` and `Finite.check`.

**The one decision** (section 7): write the design note for the walk step
now, before slice 2's parser lanes. I recommend yes.

## 1. Method, and how far to trust it

**The comparison without a port.** A full port is about 13,000 lines of
program before the first theorem. Instead:

- one theorem or small group from each kind that dominates the count
  (SW-4195: walk lemmas 23%, dispatchers 26%, list helpers 12%, the rest
  substantive [read]), plus one two-run lemma, one rule N lemma and the
  printer's triples;
- the definitions each needs, cut down but kept in kind: the `Expr` tree
  nests lists of itself, the parser is effectful and loops on fuel, the
  document type nests lists, rule N recurses two items at a time behind a
  guard;
- each system used as its users would: Lean's `simp`, `grind`,
  `fun_induction` and the `Std.Do` verification-condition tool
  (`mvcgen`); Rocq's `auto`, `intuition`, `lia`, `Function` with
  `functional induction`, a hint database and a ten-line `Ltac` walk.

**What was cut,** so what the numbers do not show:

- The parser's `Modes` (which tokens stop an expression), its failure
  state (furthest point, notes for the message) and honest marks. The
  ports' parser state is the list of items left.
- `Parse.Gives` in Stitchwort is `Parse.ReadsIn` with a spec over the
  items read; the ports state only the value's property and the
  invariant.
- `Doc` has 8 forms in the ports and 26 in std; `Tok` 18 kinds and 83.
- The `Follows` relations are simplified (`SameCode` compares kinds).

**Trust.** 21 theorems out of 6,031, chosen by me, ported with the
Stitchwort proof open beside me. The line ratios are good to perhaps a
factor of 1.5 either way; the *reasons* for them (section 4) I hold
more firmly, because each showed up as a concrete proof step that was or
was not needed. The count and hours extrapolations in section 5 are
estimates on top of that and should be read as direction, not size.

## 2. The sample

| # | Kind | Stitchwort theorems | From |
|---|---|---|---|
| 1 | Dispatcher | `signSymbolic`, `closerNotComma`, `endedWeaker` | `Syntax/ParseWalk.sw`, `Syntax/SettleOnceProofs.sw`, `Fmt/JoinProofs.sw` |
| 2 | List helper | `allAppendB`, `itemsParsed` | `Syntax/SettleOnceProofs.sw`, `Syntax/ParseWalk.sw` |
| 3 | Parser walk (`Parse.Gives`) | `givesExpect`, `givesTupleClose`, `givesParenClose`, `givesTupleEnd`, with `parenParsed`, `tupleParsed` | `Syntax/ParseProofs.sw`, `Syntax/ParseWalk.sw` |
| 4 | Longer proof | `givesCommaListFrom` (and `commaEnd`): a fuel loop | `Syntax/ParseWalk.sw` |
| 5 | Two-run (`Parse.Follows`) | `followsPeek`, `followsBump`, `followsExpect` (and `followsExpectOn`), `followsParenClose` (and `alikeParen`) | `Syntax/FollowsBase.sw` |
| 6 | Rule N | `allTokensWithout` | `Syntax/SettleOnceProofs.sw` |
| 7 | Printer | `joinsWeaker` (with `writeWeaker`, `sepWeaker`), `passesCons`, `joinsAllAppend`, `passesAppend` | `std/Doc/Joins.sw`, `Fmt/JoinProofs.sw` |

## 3. Results

Lines are statement plus proof, as laid out in each file (Stitchwort
and Lean at the repo's width; Rocq lines carry several tactics each and
29 of its 449 lines are over 100 characters, so Rocq's counts flatter
it) [all measured].

### 3.1 Dispatchers and list helpers

| Theorem | Stitchwort | Lean | Rocq | What closed it |
|---|---|---|---|---|
| `signSymbolic` | 3 | 2 | 2 | split the `∨`, compute |
| `closerNotComma` | 1 (`cases`) | 2 | 2 | Lean: `cases kind <;> first \| rfl \| contradiction`; Rocq: `destruct k; simpl; congruence` |
| `endedWeaker` | 9 | 3 | 2 | Lean: `rcases … <;> simp_all`; Rocq: `destruct …; simpl; intuition` |
| `allAppendB` | 6 | 2 | 2 | already in both libraries: Lean `List.all_append`, a `simp` lemma [read: `Init/Data/List/Lemmas.lean:3349`]; Rocq `forallb_app` |
| `itemsParsed` | 10 | 9 | 8 | induction on the list in all three; no saving |

- **Dispatchers: no advantage to take.** Stitchwort's `cases` is the
  shortest of the three where it applies. Core Lean cannot decide "for
  every token kind" by computation without Mathlib's `Fintype`; I split
  by hand. `Finite.check` is ahead of core Lean here (SW-4221 needs
  nothing from this study).
- `endedWeaker` shows what SW-4219 ("remaining cases likewise") is
  after: four arms, one proof text. Lean's `<;>` and `all_goals` appear 8
  times in the 21 proofs, and a case alternative can name two
  constructors (`| nest _ inner | group inner => …`).
- **List helpers: a library effect, not a language one.** The lemma
  exists; `simp` finds it without being told its name.

### 3.2 Parser walks

| Theorem | Stitchwort | Lean | Rocq | Notes |
|---|---|---|---|---|
| `givesExpect` | 13 | 4 | 7 | a leaf: uses the lexer's guarantee |
| `givesTupleClose` | 9 | 3 | 2 | proof is `mvcgen [tupleClose, at_, peek, fail]` / `unfold tupleClose. walk.` |
| `parenParsed` | 8 | 5 | 2 | plain fact about the tree |
| `tupleParsed` | 13 | 6 | 7 | |
| `givesParenClose` | 10 | 5 | 2 | |
| `givesTupleEnd` | 12 | 6 | 4 | |
| `givesCommaListFrom` + `commaEnd` | 53 | 16 | 22 | Lean's proof body: induction on the fuel, `mvcgen`, `grind` (7 lines). Rocq's is by hand, 13 lines; I did not try `walk` on it |
| **Total** | **118** | **45** | **46** | |

What made the difference, in order:

1. **The tool finds the sequencing.** Stitchwort's `givesCommaListFrom`
   applies `Parse.givesThen` four times, each with `[p := …]` and
   `[j := …]` written out. In Lean, `mvcgen` "will use `foo_spec` as a
   specification for calls to `foo`" for theorems tagged `@[spec]`
   [read: `Std/Tactic/Do/Syntax.lean:78`, in the installed source], and
   the `do` block already *is* `bind p j`, so nothing is given by hand.
   The same held for my hand-rolled Rocq walk and for both two-run
   proofs: `eapply followsBind` needs no arguments.
2. **The tool steps through an inner `if` or `match`.** So
   `commaListFrom` is one function in the ports and four in Stitchwort
   (`commaListFrom`, `commaListOn`, `commaListComma`,
   `commaListAfter`), `expect` one and two, `tupleClose` one and two:
   **ten functions against five** for the same code [measured]. The
   formatter's notes say why the four exist: "a `match` written inside a
   rule is a function the proofs can't name" [read:
   `tools/fmt/NOTES.md:1213`].
3. **Small non-recursive helpers need no lemma of their own.** `mvcgen
   [expect, at_, peek, bump, fail]` unfolds them in place.
   Stitchwort's `reads0At`, `reads0Peek`, `givesBump` and `givesAfter0`
   have no counterpart in the Lean file.
4. **The leftovers close themselves.** After the walk, six goals were
   left for the comma list (the invariant after `bump`, the list facts
   of `commaEnd` twice, the induction hypothesis's two conditions, the
   length inequality); `all_goals grind [GoodItems]` closed all six. In
   Stitchwort `commaEnd` is its own lemma, applied at five leaves.

A control: asked to prove a false postcondition, `mvcgen` and `grind`
fail [measured].

### 3.3 Two runs

| Theorem | Stitchwort | Lean | Rocq | Notes |
|---|---|---|---|---|
| `followsPeek` | 2 | 11 | 5 | Stitchwort's leans on std's `followsMark` and `followsMap` |
| `followsBump` | 7 | 11 | 5 | |
| `followsExpect` + `followsExpectOn` | 8 | 8 | 6 | one function in the ports |
| `followsParenClose` + `alikeParen` | 18 | 3 | 6 | the constructor of the relation is the `alikeParen` fact |
| **Total** | **35** | **33** | **22** | |

- **About even.** Neither system has a tool for a relation between two
  runs; the proofs are the same combinator lemmas, applied by hand, as
  in Stitchwort. Only the hand-given arguments go.
- The combinator lemmas themselves are much shorter (`followsBind` is 16
  lines in Lean and 6 in Rocq; `Parse.followsThen` is 23 and rests on
  `runFromThenOk2` and `runFromThenBack2` in the 2,311 and 3,431 lines of
  `Parse/Reads.sw` and `Parse/Runs.sw` [read]). That is the price of
  effects by handler: a monad's sequencing is a definition that
  unfolds, where a handler's has to be proved. It is a one-off cost and
  std has paid it; it is not a reason to change how effects are
  written.
- Core Lean has no `List.Forall₂`; I wrote the 4-line inductive
  [measured: "Unknown constant"]. Rocq's Stdlib has `Forall2`.

### 3.4 Rule N

| Theorem | Stitchwort | Lean | Rocq |
|---|---|---|---|
| `allTokensWithout` | 29 | 15 | 12 |

- `withoutR` drops a comma before a closer: it looks two leaves ahead
  behind a three-part guard. The Stitchwort proof re-does the function's
  case split by hand (`match pair: fwdPair … with`), and rewrites with
  `withoutRNop` and `withoutRPair`, two lemmas that say what the function
  does in each case.
- Lean's `fun_induction withoutR behind rest` "is a convenience wrapper
  around the `induction` tactic" using the principle Lean generates for
  each recursive function, and "will try to automatically unfold the
  call" in the goal [read: `Init/Tactics.lean:1092`]. Each case arrives
  with the guard's truth as a hypothesis and the call already unfolded.
  Rocq's `Function … {measure …}` with `functional induction` does the
  same [read: refman, "Functional induction", which also says "For new
  code and new projects, we recommend Equations"].
- The two "what the function does here" lemmas, and the guard that a
  `match` arm does not refine (SW-4047), have no counterpart.
- Termination: Lean proved the two-ahead recursion decreasing on its
  own; Rocq needed the measure stated and `simpl; lia`.

### 3.5 Printer

| Theorem | Stitchwort | Lean | Rocq | Notes |
|---|---|---|---|---|
| `joinsWeaker` and its list twin | 60 (26 forms, with `writeWeaker`, `sepWeaker`) | 30 (8 forms) | 17 (8 forms) | not comparable by lines: per form, Stitchwort is the shortest |
| `passesCons` | 7 | 4 | 3 | the same term in all three |
| `joinsAllAppend` | 11 | 8 | 6 | |
| `passesAppend` | 13 | 6 | 3 | |

- **No advantage worth having.** The triples are already
  continuation-style predicates composed by terms; a tactic adds nothing.
  Stitchwort's explicit arguments (`kinds`, `pre`, `middle`, `post`
  passed by name at each use) are most of its extra lines; implicit
  arguments in the lemma statements would remove them today.
- Nested types: Lean took a mutual recursive theorem over `Doc` and
  `List Doc` as written. Rocq's generated `Doc_ind` has no hypothesis for
  the documents inside `Concat` [measured: `Check Doc_ind`], so the proof
  is its own `Fixpoint` with an inner induction. Stitchwort's generated
  `T.induct` and `T.inductMem` are level with Lean and ahead of Rocq.

### 3.6 Totals and time

| | Stitchwort | Lean | Rocq |
|---|---|---|---|
| Proof text, the theorems of section 2 (leaf lemmas of the walk aside) | 302 lines | 159 (0.53) | 125 (0.41) |
| Theorems for the same content, leaf and helper lemmas included | 30 (the 26 of section 2, and `givesBump`, `reads0At`, `reads0Peek`, `givesAfter0`) | 23 | 26 |
| Framework lemmas written for the sample | in std (`Parse/Gives.sw` 225 lines, `Parse/Follows.sw` 454) | 25 lines (two-run only; `Std.Do` supplies the rest) | 23 lines |
| Parser functions | 10 | 5 | 5 |
| Check time for the file | 0.064 s a theorem over the project [read: SW-4195, 396 s for 6,232] | 1.3 s for the file | 0.8 s for the file |
| Writing, by the machine's clock | (the slice ran at 87 theorems an hour [read]) | about 5 min, 15 check runs, 5 real failures and 4 probes of the tool | about 4 min, 8 check runs, 5 failures, all in the first half |

- The writing times are **not** comparable with a proof lane's: I was
  translating proofs I could read, on cut-down definitions, in one file.
  The count of failed checks is the fairer figure, and it says the three
  are alike: something breaks every forty or fifty lines.
- Check times are all the same order. A two-second file says nothing
  about a 7,000-line one; `grind` and `simp` are the expensive steps in
  Lean and I did not measure them at size.

## 4. What each does better and worse

### Better in Lean and Rocq

| What | Evidence here | Stitchwort today |
|---|---|---|
| Walking an effectful program with registered lemmas | 3.2: 118 lines to 45 and 46; no `[p := …]` | `Parse.givesThen` by hand, arguments given (SW-4220) |
| Splitting an inner `if`/`match` in a proof | 3.2: 10 functions to 5 | the match is lifted into a named function first |
| Induction along a function's cases | 3.4: 29 to 15 and 12; no "nop" lemmas | recursion in the theorem, the split repeated by hand |
| Closing leftovers from facts in scope plus a lemma set | `grind`, `simp_all`, `intuition`, `auto` in most proofs (35 lines of the Lean file call `simp` or `grind`) | `cases`, `arithmetic`, `rewrite repeatedly [rules]`, each narrower |
| One proof text for several cases | `<;>`, `all_goals`, `;` | none (SW-4219) |
| A library that already has the list lemma | `List.all_append`, `forallb_app` | being lifted to std (retrospective §5 item 4) |

### Worse in Lean and Rocq

- **Lean's walk tool is unsettled** [all measured, Lean 4.35.0]:
  `mvcgen` warns that it is deprecated in favour of `vcgen`; `vcgen`
  warns that it is experimental and then fails with "Unknown constant
  `Std.WP.Triple.intro`"; a plain `throw` in the parser left `mvcgen`
  with unsolved instance goals until I wrote the failure another way;
  and a `match` on the fuel placed after a bind made Lean fail to
  generate the function's equations, so I restated the function (the
  same family of trouble as Stitchwort's hidden matches, met once).
- **Automation's proofs are brittle.** After `mvcgen` the hypotheses
  have machine-made names (`h✝`), reached with `rename_i`; a `simp` or
  `grind` proof depends on the library's current lemma set. Stitchwort's
  proofs say what they use.
- **Rocq's rough edges** [measured]: its unifier unfolded `expect` to
  find a `bind`, so my walk tactic walked *into* a callee instead of
  using its lemma until I reordered it; opening the string scope
  silently changed what `length` and `2` meant; the bind notation needed
  a second design; `Function` is the older of two tools and the newer
  (`Equations`) is a separate plugin.
- **Effects.** Neither has abilities. The parser must be written in a
  monad, with the plumbing visible in every type. And only in Stitchwort
  and Lean is the proved program the one that runs; Rocq runs an
  extraction.
- **Finite kinds.** Core Lean has no decision by enumeration over a
  type; Stitchwort's `cases` and `Finite.check` are better than what
  either offered without extra libraries.
- **Nested types in Rocq**, as in 3.5.

### The same in all three

- One lemma per parser function per property. No system makes the walk
  lemmas disappear; they make each one short, and let there be fewer
  functions.
- The two-run proofs and the printer's triples.
- Induction over lists with a fact about each item (`itemsParsed`).

## 5. Extrapolation

All **[estimated]**, from 21 theorems; read the ranges as wide.

**Slice 1 as a whole, had it been done in Lean** (Rocq is within the
noise of Lean on this sample):

| Kind (share of 6,031, SW-4195) | Count would be | Lines would be | Why |
|---|---|---|---|
| Parser walk lemmas, 23% | 0.7 to 0.9 | a third | no lemma for small helpers; 1 to 3 line proofs. Fewer functions (10 to 5) helps less than it looks, since one Stitchwort lemma often covers a split function already (`givesCommaListFrom` covers four) |
| Dispatchers, 26% (an upper bound) | 0.5 to 1 | 0.5 to 1 | `cases` is as good; perhaps half are Bool trivia (`andOf`, `orOfFalse`, `textIs`) that a closer absorbs |
| List helpers, 12% | a quarter to a half | a quarter to a half | in the library, or one `simp` |
| Slice bookkeeping, 9% | the same | the same | not sampled |
| The rest, 30% (two-run, rule N, printer, read-back) | 0.8 to 1 | 0.5 to 0.9 | 3.3 and 3.5 even; 3.4 half; read-back not sampled |
| **All** | **0.65 to 0.9** | **0.45 to 0.75** | weighted by the shares; the sample itself measured 0.77 and 0.87 for count, 0.53 and 0.41 for lines |

So about 3,900 to 5,400 theorems and 52,000 to 87,000 proof lines where
slice 1 has 6,031 and 115,777. In agent hours I would not claim more
than the lines ratio, 31 to 52 against 69: the slice's rate was set by
waiting for checks (retrospective §2, item 1), which this study does not
measure.

**The full formatter.** The same ratios on SW-4217's 12,000 to 30,000
more theorems give 7,800 to 27,000. But the port itself would cost the
13,000 lines of program again, std's `Doc` and `Parse` and their proofs,
and the 6,031 theorems already done. **Moving is not on the table and
this study is no argument for it.** The argument is the other way: the
gap is three proof tools, not the logic, the kernel or the effect
system, and each can be built in Stitchwort as `cases` and `arithmetic`
were, in the elaborator, the kernel checking what they produce.

**What I could not sample:** read-back (667 theorems), the hang proofs
(the longest in the tree), and anything at the size where check time
matters.

## 6. Features worth taking into Stitchwort

Costs are estimates in agent hours, from the retrospective's figures for
like work.

### 6.1 A walk step (first)

- **Evidence.** 3.2: the walk lemmas at about a third of the lines; the
  hand-given arguments gone; half the functions.
- **What it is.** A proof term, say `walk [lemmas]`, for a goal of the
  form "relation of `() => body`". It follows `body` in evaluation
  order: at a call with a registered lemma it applies the family's
  sequencing lemma (`Parse.givesThen`), reading `p` and `j` off the
  body; at an `if` or `match` it splits and carries the condition as a
  hypothesis; at a finished value it applies the family's done-lemma and
  tries `cases`, `arithmetic` and the hypotheses on what is left; what
  it cannot close it reports as named goals for the proof to fill.
- **Fit.** The elaborator writes the same `givesThen` chain a lane
  writes now, so the kernel is unchanged and checks all of it, as with
  `cases`. A family is declared once by naming its then, done and weaken
  lemmas, so one tool serves `Parse.Gives`, the `Kept` walk,
  `Parse.Follows` (pairs of bodies) and perhaps the printer's `Passes`.
  Lemmas register with an attribute, as Lean's `@[spec]`.
- **Two parts, separable.** (a) Finding `p` and `j`: in direct style the
  first effectful call in evaluation order is fixed by the syntax, so
  this needs no general higher-order unification. That alone is SW-4220
  done properly. (b) Stepping through a definition's inner `match`: this
  is what lets the parser stop being split, and it is the deeper change,
  touching how a `match` inside a definition is named and unfolded.
- **Cost.** A design note (Opus or Fable, 1 to 2 h); (a) 3 to 5 h; (b) 5
  to 10 h. The retrospective's idea D put the whole at 8 to 15 h
  [read].
- **Overlaps.** Retrospective idea D ("design note now, build after A
  shows the lemma form is stable": SW-4210 has since shown the form is
  uniform, 414 of `ParseWalk.sw`'s 548 theorems); **SW-4220** (subsumed
  by part a); **SW-4047** (part b needs the same refinement of a
  guard).
- **Risk.** Lean's own tool is still changing after a year, which says
  the design is not easy. Mitigation: a walk that only chains registered
  lemmas and stops at anything else is small, and useful at once.

### 6.2 Induction along a function (second)

- **Evidence.** 3.4. Also the pattern is everywhere in rule N and the
  passes: SW-4205 counts "a `match` arm doesn't refine a guard" among
  the frictions that cost about two hours.
- **What it is.** For each recursive `def f`, a generated `f.induct`:
  one case per branch of `f`, each with the branch's conditions (guards
  included) as hypotheses, the recursive calls' induction hypotheses,
  and `f`'s call in the goal already unfolded.
- **Fit.** The compiler already generates `T.induct` and `T.inductMem`
  for nested types [read: proving guide §3], and already analyses each
  `def`'s recursion for termination. The principle is an ordinary
  theorem the kernel checks.
- **Cost.** One Opus lane, 4 to 8 h, with a guide section.
- **Overlaps.** **SW-4047** (it removes the need in the commonest case,
  without fixing the refinement itself).

### 6.3 A closer with a default lemma set (third)

- **Evidence.** `commaEnd` and its five uses against one `grind`;
  `allAppendB`; `endedWeaker`; the Bool one-liners (`andOf`, `orOfFalse`,
  `notOrFalse`, `orTrueB`, `textIs`) that exist only to be named.
- **What it is.** Two steps, the first cheap: (a) std lemmas tagged
  into named default sets (`List`, `Bool`) that `rewrite repeatedly`
  uses without their being listed, and that it applies to the
  hypotheses as well as the goal; (b) later, if (a) pays, a closer that
  also chains hypotheses (what `grind` adds).
- **Fit.** (a) is SW-3631's rule sets with an attribute. (b) is a
  design note of its own; `simp-revisited.md` has the constraints.
- **Cost.** (a) 2 to 4 h on top of SW-3631; (b) not sized.
- **Overlaps.** **SW-3631**; **SW-4219** (several arms closed by one
  text is the same wish seen from the `match` side; this study's
  evidence for it is in 3.1).

### Not worth taking

- **Monadic effects.** The lines are not there (3.3).
- **Anything for finite kinds** (**SW-4221**): Stitchwort is ahead.
- **A tactic language users program** (`Ltac`). My ten-line `walk` was
  quick to write and wrong the first time in a way that passed silently
  into a harder goal. A built walk step is the better form of the same
  thing.

## 7. One decision for Matt

**Write the design note for the walk step (6.1) now, so that part (a)
can be built before slice 2's parser-walk lanes start? [rec: yes]**

- **The problem.** A parser function's lemma is written by hand as a
  chain of "then" steps with the pieces spelled out, and the parser is
  split into one small function per step so that the proofs can name
  them. That is where Lean and Rocq were clearly shorter: a third of the
  lines, half the functions.
- **The change.** A proof step that follows a function's body and
  applies the registered lemma for each call, leaving only the facts
  that need thought. First a note (1 to 2 hours), then the small part
  (3 to 5 hours).
- **What it should do.** Slice 2 to 7's parser walks are about 2,100 to
  2,500 theorems on the present form (SW-4210) [read]. With part (a)
  each is a line or two instead of ten [estimated from 3.2]; with part
  (b) the parser need not be split for the proofs and the leaf lemmas
  go (30 lemmas to 23 in the sample). It changes no
  statement and no theorem's strength.

Functional induction (6.2) and the lemma sets (6.3a) are ordinary
tickets and need no decision.

## Sources

- Lean 4.35.0, installed source under the Nix store path of
  `nixpkgs#lean4`: `src/lean/Std/Tactic/Do/Syntax.lean` (the `spec`
  attribute, lines 76 to 84; `mvcgen`'s deprecation, line 440),
  `src/lean/Init/Tactics.lean` (`fun_induction`, from line 1092),
  `src/lean/Init/Data/List/Lemmas.lean:3349` (`List.all_append`),
  `src/lean/Lean/Elab/Tactic/VCGen/Frontend.lean` (`experimental.vcgen`).
- Lean language reference, "Tactic Reference"
  (lean-lang.org/doc/reference/latest), for `grind`: "a tactic inspired
  by modern SMT solvers".
- Rocq 9.1 reference manual, "Functional induction"
  (rocq-prover.org/doc/V9.1.0/refman/using/libraries/funind.html).
- Stitchwort: `docs/reviews/SW-4195-slice1-checkpoint-numbers.md`,
  `docs/reviews/SW-4205-slice1-retrospective.md` (as corrected),
  `docs/proposals/fmt-consolidation-statements.md`, `tools/fmt/NOTES.md`,
  `docs/proving-guide.md` §3.
