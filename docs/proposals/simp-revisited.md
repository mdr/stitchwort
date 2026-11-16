# `simp` revisited: a rewriter that leaves computing alone

**Status:** design note, nothing built. Ticket SW-3522, from D3637 (Matt,
16 Nov 2026: "Yes, let's revisit SIMP with a new Fable Design note").
Whether and how `simp` is built comes back to Matt: three questions in
[§9](#9-decisions-for-matt).

**What it reconsiders.** D2541's clause "no `simp`"
([bounded-readback.md](bounded-readback.md), "Decided"), and, at Matt's
word on 16 Nov ("I'm absolutely not hard on no propext ... these
decisions aren't chisels in stone"), D3481's "no `propext`"
([bool-and-prop.md](bool-and-prop.md) §7.4). Both are treated here as
today's defaults and judged by the end state.

**Earlier notes.** [proof-automation.md](proof-automation.md) stage 3
(`simp [rules]`, deferred by D1168 "until a proof needs it");
[simp.md](simp.md) (SW-592: the proofs of the day needed case
splitting, so `cases` was built and `simp` stayed deferred);
[toy-proof-complexity.md](toy-proof-complexity.md) §3, §4.3, §5.1 (the
new evidence); [after-the-toy-proof.md](after-the-toy-proof.md) §2.3.

Labels:

- **[measured]**: counted or run for this note on 16 Nov 2026, with the
  release CLI of the main checkout at `e60d25140` on scratch copies of
  `tools/toyfmt/src/Toy/Doc`, or by the script described in §6;
- **[checked]**: read in this repo at the place given;
- **[cited]**: from a source in [Sources](#sources). The web sources
  were read by a research sub-agent through a summarising fetch, so
  wording is paraphrased; what it could not confirm is marked *not
  verified*;
- **[inferred]**, **[estimated]**: my reasoning, my estimate.

## In plain words

**The problem.** A Stitchwort proof says every rewriting step: which
lemma, on which arguments, in which order. In the toy formatter that is
777 `rewrite`s and a family of helper lemmas whose only job is to carry
a rewrite to the right place **[measured]**. The same proofs in Lean,
with `simp` and `grind`, are 30% of the size **[measured, SW-3513]**.

**The change.** A proof term `simp [rules]`: it rewrites the goal *as
it is written* with the listed equations, each left to right, wherever
they fit, until none fits, and then closes what is left the way `byComputing`
and `cases` already close things. Rules can be collected under a name
declared in one place (`rules words := [...]`). There is no global rule
set, no attribute, no new axiom and no kernel change. What `simp` wrote
can be printed as the `rewrite` chain it stands for.

**What it should do.** On nine real proofs rewritten by hand (six from the toy, three from
std, §6), 6,783 characters of proof become
3,376, about half, and four helper lemmas disappear **[measured on the
hand-written text; that the rewriting goes through was checked with
today's `rewrite` for most of it, §6]**. On the engine slice that the
Lean port measured I estimate a quarter of the proof text goes (22 to
29%) **[estimated]**. That is about a third of the gap to idiomatic
Lean, not all of it: the rest is `grind`'s reasoning from "or" and
"there is" hypotheses, one script for many cases, and angle brackets,
which are other tickets.

**What stays.** Computing is still how Stitchwort decides. `simp` never
unfolds a definition to look for a match, has no transparency settings,
and doesn't split cases. It is `rewrite`, repeated, with the bookkeeping
done for you.

## 1. What the evidence says

### 1.1 What `simp` and `grind` did in the Lean port

Read from `experiments/lean-engine/idiomatic/Toy/Proofs/Words.lean`
**[checked]**. Its 91 `simp`/`grind` lines do five different jobs:

| Job | Lean | Stitchwort today | Needs a `simp`? |
|---|---|---|---|
| Unfold definitions so the goal computes | `simp [Printer.put, wordsOf, …]`, the definition names in every list | Conversion does it: `byComputing` and `arithmetic` compute through definitions (the plain Lean port needed `show` 12 times where Stitchwort needs nothing, toy-proof-complexity.md §5.1) | No. This is the part of Lean's `simp` Stitchwort already has |
| Rewrite with lemmas about the printer's operations | 29 `@[simp]` lemmas: `put_written`, `newline_words`, `stackWords_append`, … | `rewrite lemma args then …`, one per step, or helper lemmas (`keepsWords`, `addsWords`, `eitherWords`) | **Yes: this is the gap** |
| Use the hypotheses as rules | `simp_all`, `simp [*]`, `simp [ih]` | `rewrite steps then …` by name | Yes, by name |
| The same script in every case | `<;>`, `all_goals`, `first \| done \| … ` | One arm written per case | No: a separate feature (§4.3 rank 4 of toy-proof-complexity.md) |
| Reason from "or" and "there is" hypotheses, with arithmetic | `grind` (17 uses) | Patterns (`Inl (Both _ flat)`), `arithmetic` | No: not rewriting |

Of the 29 `@[simp]` lemmas, 26 are equations and 3 are `↔`
(`stackUniform_append`, `stackUniform_prints`, `stackUniform_fillSeps`)
**[checked]**. Every use of those three is at the top of a goal or
hypothesis, or directly under `∧` **[checked by reading]**. None needs a
proposition rewritten inside anything else.

### 1.2 Two things today's tools can't do, found by probing

I rewrote `stepWords` (the 26-arm proof, 65 lines) as one `rewrite`
chain per arm, the chain a `simp` would produce, and checked it with
the release CLI **[measured]**:

- **23 of the 26 arms check** as `rewrite steps in rewrite <rules> in
  byComputing`, with the rules' arguments left open, for example

  ```
  | Chunk text width, steps, _ => rewrite steps then rewrite writeWords, List.appendAssoc then byComputing
  | Concat docs, steps, _ => rewrite steps then rewrite stackWordsAppend, printsWords then byComputing
  | Fill [first, ..others], Inl (Both _ flat), _ =>
    rewrite flat then rewrite stackWordsAppend, printsWords, joinLinesWords then byComputing
  ```

  So the helper lemmas `keepsWords` and `addsWords` are not needed even
  today. The rules that do the work are a fixed set of 12.
- **A visible call that could compute further is not found.** With the
  goal printed as `Printer.words (printer.write indent " " 1) ++ … = …`,
  `rewrite writeWords` (arguments open) answers `E-REWRITE-NOTHING`: it
  "compares what terms compute to", and because `" "` is known the call
  has computed into an `if`. Giving every argument
  (`writeWords printer indent " " 1`) works. This is friction group 1 of
  after-the-toy-proof.md §2.3 ("`rewrite` can't find a term the goal
  has already computed past"), and it looks like a gap against D2542,
  which says the as-written occurrence is used when there is one.
- **The three arms with an `if` fail under `cases then (rewrite …)`.**
  `cases` hands its term the goal *computed*, in which
  `(printer.newline indent).words` is no longer visible, and then keeps
  splitting what the computed goal is stuck on: 15 cases, down to
  `printer.owed = None`, where one split on the visible `if` was meant.
  The toy works round it with `eitherWords`, a lemma that says "prove
  it for both branches".

Both failures are the same thing: the search tools still compute before
they look. D2542 decided they shouldn't. A `simp` that matched only what
is visible would not have either problem, and it needs `cases` to pass
the folded goal to the term after `then` (§3.5).

### 1.3 What D1168 was waiting for

simp.md §7 said to build `simp` "when a proof needs rewriting with
lemmas *and* `rewrite p, q then …` is too long or can't do it". The toy
is that proof: 777 `rewrite`s in `tools/toyfmt/src`, and std has 1,551
with 2,244 uses of `Eq.cong`, `Eq.trans` and `Eq.flipped` **[measured, by
`grep`]**.

## 2. The design

### 2.1 What `simp` is

`simp` is a keyword and a proof term, like `rewrite`, `arithmetic` and
`cases`:

| Form | Meaning |
|---|---|
| `simp [r1, r2]` | rewrite the goal with the rules until none applies, then close it (§2.4) |
| `simp [r1, r2] then t` | the same, then `t` proves what is left |
| `simp [r1, r2] at h` | the fact `h` (or any term) with its type rewritten, as `rewrite … at` |
| `simp [r1, r2] at h then t` | `h` rebound for `t` |
| `simp [r1, r2] then ?` | shows what is left, as a goal |

A **rule** is one of:

- a proof of an equation `a = b`, with arguments left open as in
  `rewrite` (`List.appendAssoc`), used left to right; `<- p` turns it
  round;
- a hypothesis that is an equation (`steps: result = (…)`), by name;
- a `Bool` fact: `h: isLayout piece` is the equation `isLayout piece =
  True` (D3482), so it rewrites that test to `True`; an equation between
  tests (`(a && b) = (b && a)`) is an ordinary equation;
- a definition's name, `f`: one step of `f`, by its generated equations
  `f.eqK`, exactly as `rewrite f` (D1433);
- the name of a rule set (§2.3);
- from stage 3, a proof of `P ↔ Q`, and any other fact `h: P`, read as
  `P ↔ True` (§2.2).

A conditional rule's premises are found as `rewrite`'s are: by
unification, a hypothesis of exactly that type, or `arithmetic` **[checked:
`docs/syntax.md`, "Premises"]**. A premise that isn't found means the
rule doesn't apply there; it isn't an error.

**The proof it writes** is the chain of `J` steps and congruence-lemma
applications that the same `rewrite`s would write, then the closer's
term. The kernel checks it; nothing new is trusted and the kernel is
unchanged.

### 2.2 How it rewrites

- **Only what is visible.** `simp` matches a rule's left side against
  the goal as written (calls kept, the form `stitchwort goal` prints),
  by the function at its head and then by filling the rule's open
  arguments. It never computes the goal to find a match and never looks
  inside a definition. This is D2542 without its fallback ("look inside
  definitions only when nothing is visible"): a search that tries many
  rules must be cheap and must mean the same thing every time. To
  rewrite inside `f`, put `f` in the list.
- **Order.** Innermost subterms first, left to right; at each subterm
  the rules are tried in the order listed (a set's rules in the order it
  declares them); after a rewrite the result is visited again. It stops
  when no rule applies anywhere. This is Lean's default order
  (`simp.md` §4.2 [L7]) and Rocq's `rewrite_strat (bottomup (hints
  db))` **[cited: R1]**.
- **Under a function argument**, through the congruence lemma beside
  the function (`List.mapCong`), as `rewrite` does today **[checked:
  `docs/syntax.md`, "Inside a function argument"]**.
- **With `↔`, no axiom (stage 3).** To rewrite `P` to `Q` by `e: P ↔ Q`
  where `P` sits inside a goal built from `∧`, `∨`, `¬`, `→`, `∀`, `∃`
  and `↔`, the proof is built from one congruence lemma per connective
  (`(P ↔ Q) → (P ∧ R ↔ Q ∧ R)` and so on), and the goal is proved from
  the rewritten one by the `↔`'s backward direction. Beside the seven
  fixed connectives, a predicate that takes a proposition or a predicate
  gets a registered lemma in the same style as `mapCong`:
  `List.allIff: (∀ x => p x ↔ q x) → (List.All p xs ↔ List.All q xs)`,
  found by name. Where `P` is under something with no such lemma, the
  rule doesn't fire, and if the goal stays open the message says so
  (`E-SIMP`, note "`stackUniformAppend` could apply inside `Reads …`,
  but `Reads` has no `readsIff` lemma"). This is Rocq's generalized
  rewriting **[cited: R1, R2]** cut down to one relation, `↔`, and a
  by-name lookup in place of its typeclass search.

### 2.3 Rule sets

```
rules words :=
  [writeWords, newlineWords, lineStartWords, blankWords, suffixWords, stackWordsAppend, printsWords,
   fillSepsWords, joinLinesWords, headOrWords, List.appendAssoc, List.appendNil]
```

A `rules` declaration names a list of rules. It is declared once,
exported and imported like any name, may include other sets, and is used
as `simp [words]` or `simp [steps, words]`. There is **no attribute, no
default set and no bare `simp`**: every `simp` names what it uses, and
"what does `simp [words]` do" is answered by jumping to one
declaration. §4 gives the reasons.

### 2.4 Closing, and what `simp` doesn't do

After rewriting, `simp [..]` closes the goal by the first of: both
sides compute to the same value (`byComputing`, so **computing still decides**);
two hypotheses contradict each other; a hypothesis, or a side of one
that is a conjunction, is the goal; from stage 3, a goal that is a
conjunction whose parts each close this way. These are `cases`' closers
**[checked: `docs/syntax.md`, "Closing a case"]** without `arithmetic` and
without the decision closer; for those write `simp [..] then arithmetic`.

It does **not**:

- unfold definitions on its own, or have reducibility settings (D2541's
  "no Lean-style transparency system" stands);
- split cases. `cases then simp [..]` and `simp [..] then cases` give either
  order, as simp.md §7 recommended; Lean's `simp` doesn't split either
  **[cited: simp.md §4.2]**, Isabelle's does, in its looper **[cited:
  I1]**;
- sort sums or products (no ordered rewriting: that is `algebra`'s and
  `arithmetic`'s job; a commutativity rule is refused, §3.1);
- chain through lemmas by the goal's shape, or reason from "or" and
  "there is": that is the rule-set-and-walker design
  (toy-proof-complexity.md §4.3 rank 3), which should reuse `rules`.

### 2.5 How it fits what exists

| Tool | Is for | With `simp` |
|---|---|---|
| conversion, `byComputing` | what computes | `simp`'s closer; `simp` is for what doesn't compute: facts about stuck terms |
| `rewrite` | one chosen step; fails if the term isn't there | `simp` is many steps to a fixed point; a rule that doesn't fit is skipped. Every `simp` can be printed as a `rewrite` chain |
| `cases` | splitting on what is stuck | composes: `cases then simp [..]` |
| `arithmetic`, `algebra` | arithmetic | compose: `simp [..] then arithmetic`; `arithmetic` already discharges rules' premises |
| `byDecision`, `Finite.check` | closed decidable facts | unchanged; `simp` doesn't decide |

**D2541, exactly.** Stays: "Computing stays the way to decide:
conversion, `byComputing`, `decide`, `byDecision`, `cases`, tests and the
counterexample search. No Lean-style transparency system." Goes: "and
no `simp`". Added: "`simp` rewrites with named rules on the goal as
written and closes by computing; it never unfolds to search."
**D2542** stays and is applied more strictly (no fallback inside
definitions for `simp`); §1.2's two gaps are places where `rewrite` and
`cases` don't yet follow it.

## 3. Termination, budgets, messages, and what you see

### 3.1 Termination

- **Budget.** At most 500 rule applications in one `simp` (the toy's
  arms use 1 to 5 **[measured, §1.2]**). Past that it is
  `E-SIMP-BUDGET`, with the last rules applied and, when they repeat,
  the cycle ("`a`, `b`, `a`, `b` …"). A limit fails with a message and
  never returns a half-simplified goal as if finished (D2543). Lean's
  limit is 100,000 visited subterms **[cited: L5]**; Isabelle has no
  step limit and only "notices certain simple forms of nontermination"
  **[cited: I1]**; Rocq's `autorewrite` "may loop" **[cited: R3]**.
- **Rules that loop on their own** are refused where they are listed
  (`E-SIMP-RULE`): one whose right side contains an instance of its own
  left side (`a + b = b + a`). Lean has a lint for this (`simpComm`)
  **[cited: L8]**; here it is an error, since there is no ordered
  rewriting to make such a rule useful.
- **Premises** are not proved by a recursive `simp`, so there is no
  depth to limit (Lean: depth 2 **[cited: L5]**; Isabelle: 100 **[cited:
  I1]**).

### 3.2 When it doesn't close

`E-SIMP` shows, in this order:

1. the goal that is left, as written, and (as `E-REFL` does) where its
   two sides first differ;
2. the rules that applied, in order, with how many times each;
3. the rules that never applied, and for each the cheapest true reason
   found: its left side's head function doesn't appear; it appears only
   inside a definition's body (name the definition: "add `Printer.words`
   to the rules, or state the lemma about what is written"); a premise
   wasn't proved (which one, and the facts there were); or, for `↔`, the
   context has no congruence lemma;
4. when a counterexample to the *left-over* goal is found by the
   existing search, it is shown, so a wrong rule set and a false lemma
   look different.

`simp [..] then ?` shows the same left-over goal as an ordinary goal.

### 3.3 How a reader learns why a step holds

- `stitchwort goal --at` on a `simp` prints its steps: each rule with
  the arguments it found, the subterm before and after.
- **Expand**: a CLI flag and code action that replaces a `simp [..]` by
  the `rewrite` chain it wrote, as source that checks. This is Lean's
  `simp?` **[cited: L2]** and Aesop's `aesop?` **[cited: L9]**, with one
  difference: the output is not a narrower call to the same search but
  a search-free proof, since `simp`'s term *is* a `rewrite` chain. Use
  it where a proof must not change when a rule set does, and to read a
  proof someone else compressed.
- A rule listed by itself (not through a set) that never applies is a
  warning, so lists stay honest. Set members aren't warned about.

### 3.4 Performance

- Matching is by head function on the written term, so the cost of a
  pass is the size of the goal as written, times the rules that share a
  head. No computing happens until the closer runs. This is cheaper per
  step than today's `rewrite`, whose comparisons compute and share an
  evaluation budget **[checked: `docs/syntax.md`, "Cost"]**.
- The kernel re-checks one `J` per step. Lean's version of the engine
  slice checked 60% slower with `simp` than without (2.1 s against
  1.3 s) **[measured, SW-3513]**; `simp` was 15% of Mathlib's build
  time in one 2024 profile **[cited: L10]**. Explicit rule sets keep
  the candidate rules few; stage 1's acceptance measures it (§8).

### 3.5 What `simp` needs from `cases` and `rewrite`

- `cases then t` must give `t` each case's goal as written, with the
  split value put in, not the computed goal (§1.2). Without that,
  `cases then simp [..]` can't see the calls its rules are about.
- `cases` should split a visible `if`'s condition before going inside
  definitions for something stuck.
- `rewrite` with open arguments should find a visible call even when
  the call can compute (§1.2). `simp` gets this by construction;
  `rewrite` should match it so that an expanded `simp` checks.

## 4. Rules: listed, named sets, or an attribute

| | Listed only (`simp [a, b]`) | Named sets, declared once (**recommended**) | Attribute and a default set (Lean `@[simp]`, Isabelle `[simp]`) |
|---|---|---|---|
| Predictability | A proof's meaning is on its line | A proof changes only when a set it names changes; the set is one declaration to read | Any `@[simp]` added anywhere can change or break any bare `simp`. Lean's reference: "avoid using simp without only unless it closes the goal" **[cited: L3]**; "the default simp set is as much a part of a library's interface as the type signatures" **[cited: simp.md L4]** |
| Maintenance | The same 10 names in every arm (`stepWords` would list up to 12 rules in each of 17 arms) | One list; arms say `simp [steps, words]` | Shortest proofs. Needs normal-form discipline and lints (`simpNF`) **[cited: L8]**; Mathlib tells authors not to pin terminal `simp`s because pinned lists break on renames **[cited: L4]** |
| Performance | Few rules | Few rules per call | Thousands of candidate rules; needs an index; the measured costs in §3.4 are of this design |
| Where membership lives | — | In the set (one place, ordered; the order is the priority) | On each lemma (scattered; priorities as numbers) |
| Language cost | none | one declaration form, `rules` | the first attribute with a meaning inside the language **[checked: `docs/syntax.md`, "Attributes": today's are for JavaScript export]** |

Named sets give most of the brevity of a default set (the Lean port's
own lists repeat `stackWords, Cmd.words` six times, so even Lean's
default set didn't remove lists) and keep the property Stitchwort's
proofs have today: a proof means the same thing until something it
names changes. A default set can be added later without breaking
anything; it can't be taken away. Std would ship a few small sets beside
their lemmas (`List.appendLaws`, `List.lengthLaws`, `Option.laws`),
chosen in stage 4 from what the conversions used.

## 5. `propext` or congruence

Lean's `simp` turns every `P ↔ Q` rule into `P = Q` with `propext` and
rewrites with it like any equation **[cited: L1, L6]**. The two ways to
give Stitchwort's `simp` its `↔` rules:

| | With a `propext` axiom | Without: congruence lemmas (SW-2706's approach, §2.2) |
|---|---|---|
| Proof size | An `↔` rule fires anywhere a proposition appears | The same wherever the context is one of seven connectives or has a registered lemma. On the toy slice: all 3 `↔` lemmas of 29, every use, are covered with no registered lemma **[checked, §1.1]**. Elsewhere a rule doesn't fire and the proof says the step by hand |
| How much is in reach at all | Everything | Tests are already equations: two `Bool`s that imply each other are equal by a theorem (`Bool.eqOf`), and D3479 puts decidable facts in `Bool`. So only propositions that *can't* be tested (`∃`, `∀`, relations like `Reads`) need `↔` rewriting **[checked: bool-and-prop.md §7.4]** |
| Predictability | One mechanism; still fails where the motive isn't well typed (dependent positions), as Lean's does | Fails also where a congruence lemma is missing, with a message naming the lemma to write |
| `byComputing`, `decide`, tests | `J` computes only on `byComputing`; "with any other proof it's stuck" **[checked: `docs/core.md:143`]**. Today that can happen only through `Quot.sound`. With `propext`, any equation whose proof took an `↔` step no longer computes to `byComputing`, so a value carried along it (a `rewrite … at` on data, a `Vec n` moved to `Vec m`, a `Decidable P` moved to `Decidable Q`) is stuck, and a `byComputing`, `byDecision` or test that runs through it fails. This is how Lean's `decide` gets stuck **[cited: bool-and-prop.md L3]**. How often Stitchwort computes through such a value: not measured. A kernel rule "`J` along any proof computes when its two ends are the same" would narrow it to values indexed by the proposition itself; that is a second kernel change with its own soundness review | Nothing changes. Where Lean would move a decision along `propext`, the congruence route builds it from the two directions, which computes |
| `stitchwort axioms` | Lists `propext` for every theorem with an `↔` step in a `simp` or `rewrite`, and everything built on them. The Lean port's top theorems report `propext` and `Quot.sound` in the *plain* version already **[measured, SW-3513]**. "No axioms" stops being the usual answer; the audit's allowed list grows | Unchanged |
| Kernel and consistency | One more axiom constant, as `Quot.sound` is: a small kernel and spec change. Consistent with these rules **[inferred: the usual set model, where a proposition is empty or has one element, satisfies it together with K and quotients; Lean has the same combination; not verified against a source for this note]** | No kernel change; the engine is elaborator code and its terms are checked |
| Build | Simplest engine: `↔` rules become equations on the existing path | A second relation in the engine, seven lemmas, and a by-name lookup: about 3 agent-hours more **[estimated]** |
| Later | Can't be removed once proofs depend on it | Adding `propext` later is purely additive: rules that said "no congruence lemma here" start to fire, and no proof breaks |

**Recommendation: without, for now, and measure.** Not because D3481
said so, but for three reasons from the end state. First, the benefit
is small here: tests-first has already made most facts equations, and
the only measured sample needs `propext` nowhere. Second, its cost
lands on the thing Stitchwort is built around: that a closed proof
computes. Third, the choice is one-way in one direction only. The
`E-SIMP` note for a missing congruence lemma (§3.2) is the measure: if
stage 4's conversions hit it often in places a registered lemma can't
reasonably cover, the best end state is `propext` as a *fallback* used
only there, so that `stitchwort axioms` still says "none" for every
proof that didn't need it. That is a later, smaller decision with data.

**SW-2706 is a part of this plan, not a separate feature.** Its
congruence engine is what stage 3 builds, once, for both tools:
`rewrite` learns `↔` (the ticket as written) and `simp` takes `↔`
rules. It is not a prerequisite for stages 1 and 2: 26 of the 29 rules
in the sample are equations.

## 6. Evaluation: nine proofs by hand

Each proof's body (after `:=`) was rewritten under the proposal and
counted in non-blank characters by a script, before and after
**[measured]**. "Goes through" says how I know the rewriting works.

| Proof | Before: lines, chars | After: lines, chars | After/before | Goes through |
|---|---|---|---|---|
| `suffixWords` (toy) | 5, 305 | 1, 40 | 13% | **[measured]**: `rewrite List.filterAppend, List.appendAssoc then byComputing` checks today |
| `writeLayoutWords` (toy) | 1, 91 | 1, 54 | 59% | **[measured]**: the open-argument chain checks |
| `stackWordsAppend` (toy) | 4, 135 | 3, 84 | 62% | **[measured]** |
| `flushEachWritten` (toy) | 10, 435 | 6, 298 | 68% | **[inferred]**: the toy's own chain with arguments dropped |
| `stepWords` (toy) | 65, 2,628 | 28, 1,181 | 44% | **[measured]** for 23 of 26 arms (§1.2); the 3 `if` arms need §3.5 |
| `stepUniform` (toy) | 53, 2,238 | 30, 1,275 | 56% | **[inferred]**: needs stage 3 (`↔` rules, closing a conjunction) |
| `List.reverseSnoc` (std) | 4, 125 | 3, 76 | 60% | **[measured]**: `rewrite List.reverseCons, reverseSnoc rest x, List.reverseCons then byComputing` checks |
| `List.sumTakeMono` (std) | 11, 396 | 6, 179 | 45% | **[measured]** for the chains; `simp … at` is new |
| `List.sumDropTakeLe` (std) | 12, 430 | 7, 189 | 43% | **[inferred]**, same shape |
| **Total** | **165, 6,783** | **85, 3,376** | **50%** | |

Two examples of the "after" text:

```
theorem suffixWords ∀ (printer: Printer) (comment: Text):
    ({ printer | suffixes = printer.suffixes ++ [comment] }).words = printer.words ++ wordsOf [comment] :=
  simp [List.filterAppend, List.appendAssoc]

-- in stepWords, with `rules words` as in §2.3:
        | Chunk text width, steps, _ => simp [steps, words]
        | Line, steps, _ => cases then simp [steps, words]
        | Concat docs, steps, _ => simp [steps, words]
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), _ => simp [broken, words]
```

Also gone: `keepsWords`, `addsWords`, `eitherWords` and `eitherUniform`
(22 lines, 865 characters), which exist only to steer rewrites
**[measured]**. A tenth, `multiplierSucc` (AoC day 2), was put at 9
lines to 1 by proof-automation.md §1.4 **[cited; not rechecked]**.

**What this sample is.** These proofs were picked because they rewrite;
half the toy's proofs are three lines or fewer and many are a `match`
with `byComputing` arms, which `simp` doesn't shorten. So:

- **The engine slice** (17,184 characters of proof **[measured,
  SW-3513]**): the sample's toy proofs save about 2,900 and the helpers
  865; with the slice's other rewriting proofs (`newlineWritten`,
  `putClearWords`, `writeWords`, `readingLighter`'s `arithmetic` arms) I put
  the saving at 3,800 to 5,000 characters, **22 to 29%**
  **[estimated]**. Stitchwort would be at about 75% of today's text;
  idiomatic Lean is at 30%.
- **The whole toy**: 2,500 to 4,000 of its 17,302 proof-body lines
  **[estimated]**, below toy-proof-complexity.md §4.3's 4,000 to 6,000,
  which assumed hypotheses used automatically and one script for many
  cases.
- **Why not 30%.** `stepWords` is 17 lines in Lean and 28 here because
  Lean writes `all_goals` once where Stitchwort writes an arm per case;
  with "the remaining cases by `t`" it would be about 10 lines. The
  `Fill` and `Choice` arms are `grind` in Lean. Those are ranks 2 to 4
  of §4.3 there, and `simp` makes each of them worth more: a script
  shared by 14 cases has to be one that skips rules that don't fit.

## 7. Prior art

- **Lean 4.** `simp` is bottom-up rewriting with a default `@[simp]`
  set, `simp only [..]` for listed rules, `simp at h`, `simp [*]`,
  `simp_all`, and `simp?`, which reports the rules used as a `simp
  only` **[cited: L2]**. It fails when it makes no progress
  (`failIfUnchanged`) **[cited: L5]**. `↔` rules go through `propext`
  **[cited: L1, L6]**. Congruence under binders is by `@[congr]` lemmas
  and function extensionality **[cited: L7; proof-automation.md
  §4.2]**. Limits: 100,000 steps, discharge depth 2 **[cited: L5]**.
  The guidance against non-terminal `simp` **[cited: L3, L4]** is the
  experience this design starts from: listed rules are Lean's cure, so
  Stitchwort starts with the cure. `grind` (released in v4.22, August
  2025) combines congruence closure, E-matching, case analysis and
  arithmetic solvers, proving by contradiction **[cited: L11]**; it is
  not a rewriter, and what it did in the port is outside this note.
  Mathlib's `grw` (June 2025) rewrites with relations other than `=`
  through `@[gcongr]` lemmas **[cited: L12]**: the congruence route,
  inside Lean.
- **Rocq.** Generalized rewriting: `Proper` instances say a function
  respects a relation; `setoid_rewrite` and `rewrite_strat` build the
  proof from them, with `iff` under `all` and `ex` declared in
  `Morphisms_Prop` **[cited: R1, R2]**. No axiom is involved in the
  construction **[inferred; R1 doesn't say so in one sentence]**. Its
  cost is the typeclass search, a depth-first search taking the first
  solution **[cited: R1]**, with a reputation for slowness **[cited:
  R4, a forum remark]**. §2.2 keeps the idea and replaces the search by
  seven fixed lemmas and a by-name lookup. `rewrite_strat` has a
  strategy language (`bottomup`, `topdown`, `innermost`, `repeat`,
  `hints db`, …) **[cited: R1]**; `autorewrite with db` uses `Hint
  Rewrite` databases, which are named sets **[cited: R3]**.
- **Isabelle.** `simp add: del: only:`, the `[simp]` attribute,
  conditional rules, a subgoaler, solvers and loopers (splitting is a
  looper), `cong:` rules, ordered rewriting for commutative rules,
  `simp_trace` **[cited: I1]**. Every result is a theorem made by the
  kernel **[cited: I2]**, as every `simp` here is a checked term.
- **Agda.** No simplifier in the distribution **[not verified]**.
  `{-# REWRITE #-}` makes an equation a computation rule: not checked
  for termination, confluence checking optional, incompatible with
  `--safe` **[cited: A1, A2]**. That changes what the kernel computes,
  which proof-automation.md already ruled out. `rewrite` in a clause is
  one step **[cited: A3]**.
- **Idris 2.** `rewrite … in`, one step; elaborator reflection for
  writing tactics as programs **[cited: D1, D2]**. No built-in
  simplifier **[not verified]**.

**What to take.** From Lean: `simp only` as the only form, `simp?`
turned into a real expansion, fail on no progress. From Rocq: `↔`
without an axiom, and named databases. From Isabelle: the residue is a
goal you can read, and a trace. Not taken: default sets, ordered
rewriting, splitting inside the simplifier, rewrite rules in the
kernel.

## 8. Stages

Agent time, from the 0.3 factor on human-style estimates (CLAUDE.md).
Kernel unchanged throughout, so reviews are Opus's (term-generating
changes, D2364).

| Stage | What | Lane | Time | Acceptance |
|---|---|---|---|---|
| 0 | The two gaps of §1.2, as bug fixes with tests: open-argument `rewrite` finds a visible call that can compute; `cases then t` gives `t` the folded goal and splits a visible `if` first | Opus (tactics: D2506) | 1.5 h | §1.2's failing arms check as written there |
| 1 | `simp [rules]`, `… in t`, `… in ?`: equations, hypotheses, `Bool` facts, `f`; visible matching; closers; budget; `E-SIMP`, `E-SIMP-BUDGET`, `E-SIMP-RULE`; steps in `stitchwort goal --at`. `docs/syntax.md`, guide, a tour page | Opus, then Opus review | 4 h + 1 h | The five small equation proofs of §6 (`suffixWords`, `writeLayoutWords`, `stackWordsAppend`, `flushEachWritten`, `List.reverseSnoc`) check as written there. `Words.sw` converted on a branch: proof characters down 15% or more, check time within 1.5 times today's. One reject example per message |
| 2 | `rules` declarations; `simp … at h`; expand (CLI flag and code action) | Sonnet | 2.5 h | `stepWords` and `List.sumTakeMono` as in §6. Expanding every `simp` in `Words.sw` gives a file that checks |
| 3 | `↔` under the connectives, for `rewrite` and `simp` (SW-2706); registered `…Iff` lemmas; conjunction closer | Opus (short as-built design first), then Opus review | 4 h + 1 h | `stepUniform` as in §6. `stitchwort axioms` on it: none. The missing-lemma note fires in a reject example |
| 4 | Convert the engine slice (`Readings.sw`, `Words.sw`, the 11 theorems of `Proofs.sw`) and re-run SW-3513's script; choose std's first sets; count missing-congruence notes | Sonnet | 2 h | Target: proof characters at 80% of today's or less (§6 estimates 71 to 78%). The table of toy-proof-complexity.md §5.1 gains a fourth column |

About 16 agent-hours **[estimated]**. Stages 0 to 2 are useful alone.
After stage 4, with numbers: std sets and sweeps of std and AoC; the
`propext` fallback question, if the count calls for it; and whether the
"rule sets by goal shape" design builds on `rules`.

**Risks.**

- *Visible matching is too strict.* A lemma stated about `f x` won't
  fire on a goal where `f x` has already computed. That is the intent
  (D2542), but it may mean lemmas restated about the computed form.
  Stage 1's conversion of `Words.sw` will show it; the `E-SIMP` note
  for "appears only inside a definition" is the mitigation.
- *Sets grow into a default set by habit* (`simp [everything]`). Keep
  std's sets small and named for what they normalise.
- *Proofs that pass for the wrong reason.* A `simp` that closes a goal
  no longer says which rule mattered. Expand (§3.3) is the answer; the
  kernel check means it is never a soundness question.
- *Agents over-use it.* The Lean port's `simp` version failed six times
  before passing, the plain one never **[measured, SW-3513]**. The
  proving guide should say: `byComputing` first, then one `rewrite`, then
  `simp` with a set.

## 9. Decisions for Matt

For the orchestrator to number. Everything else here (budget figures,
message wording, the order of stages) is the orchestrator's.

**Q1. Reverse D2541's "no `simp`" and build the `simp` of §2?**
*The problem:* every rewriting step in a proof is written out, 777
times in the toy, with helper lemmas to steer them; the same proofs in
Lean with its automation are 30% of the size.
*The change:* a proof term `simp [rules]` that rewrites the goal as
written with named rules until none fits, then closes by computing. No
kernel change, no axiom; it never unfolds definitions to search and
never splits cases. The rest of D2541 ("computing decides", no
transparency system) and D2542 stay.
*What it should do:* about half the text of rewriting-heavy proofs
(nine by hand: 6,783 characters to 3,376 **[measured]**), about a
quarter of the engine slice's proof text **[estimated]**, and four
helper lemmas gone. About 16 agent-hours over five stages, the first
three useful alone. **[rec: yes]**

**Q2. Rules: named sets declared in one place, with no attribute, no
default set and no bare `simp`?**
*The problem:* listing every rule in every proof is long (up to 12 rules in
17 arms of one proof), but Lean's default set makes proofs break when
anyone adds a lemma to it, which is why Lean's own advice is to avoid
relying on it.
*The change:* a `rules words := [...]` declaration; proofs say `simp
[steps, words]`.
*What it should do:* a proof changes only when a set it names changes,
and that set is one declaration to read. A default set could still be
added later; it couldn't be removed. **[rec: yes]**

**Q3. `propext`: keep it out for now, and build `↔` rewriting on
congruence lemmas (SW-2706, as stage 3)?**
*The problem:* Lean's `simp` rewrites with "if and only if" facts by an
axiom, `propext`. Stitchwort has no such axiom, and Matt has said that
is open.
*The change:* none to the kernel. `rewrite` and `simp` take `↔` rules
under `∧ ∨ ¬ → ∀ ∃ ↔` and under predicates that register a lemma, and
say so when a context has none.
*What it should do:* covers every `↔` use in the measured sample;
`stitchwort axioms` keeps saying "none"; closed proofs keep computing
(with `propext`, a value carried along a proof that used it gets
stuck, the known cause of Lean's `decide` failures). Costs about 3
agent-hours more than the axiom would. If stage 4 counts many places
the lemmas can't reach, come back with `propext` as a fallback used
only there: adding it later breaks nothing, removing it would. **[rec:
yes, no axiom now; revisit with stage 4's count]**

## Findings worth tickets

- `rewrite` with open arguments doesn't find a visible call that can
  compute further (§1.2), against D2542. Reproducer: in `stepWords`'
  `FillSep` arm, `rewrite flat in rewrite writeWords, List.appendAssoc
  in byComputing` fails; `writeWords printer indent " " 1` works.
- `cases then t` gives `t` the computed goal and over-splits (15 cases
  for one `if`) (§1.2).
- `keepsWords`, `addsWords` aren't needed today: the arms check with
  plain open-argument `rewrite` chains (§1.2). The proving guide could
  show that form.
- "The remaining cases by `t`" in a proof `match` (already rank 4 of
  toy-proof-complexity.md §4.3) is worth more once `simp` exists (§6).

## Sources

Repo, read at `e60d25140`: the notes named at the top;
`docs/syntax.md` (`rewrite`, `cases`, `arithmetic`, "Attributes", "Generated
equations"); `docs/core.md` lines 143-146, 270, 577-589;
`tools/toyfmt/src/Toy/Doc/Words.sw`, `Readings.sw`;
`experiments/lean-engine/` (README and `idiomatic/Toy/Proofs/`);
`crates/elab/src/std/List/Lemmas.sw`.

Web, fetched 16 Nov 2026 by a research sub-agent:

- **[L1]** Lean reference, "Rewrite Rules": https://lean-lang.org/doc/reference/latest/The-Simplifier/Rewrite-Rules/
- **[L2]** Lean reference, "Invoking the Simplifier": https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/
- **[L3]** Lean reference, "Terminal vs Non-Terminal Positions": https://lean-lang.org/doc/reference/latest/The-Simplifier/Terminal-vs-Non-Terminal-Positions/
- **[L4]** Mathlib style guide: https://mathlib.org/contribute/style.html ; community `simp` page: https://leanprover-community.github.io/extras/simp.html
- **[L5]** `Init/MetaTypes.lean` (`Simp.Config`): https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/MetaTypes.lean
- **[L6]** Zulip, "propext contamination" (2021; may concern Lean 3): https://leanprover-community.github.io/archive/stream/113489-new-members/topic/propext.20contamination.html
- **[L7]** Lean API, `SimpCongrTheorems`: https://lean-lang.org/doc/api/Lean/Meta/Tactic/Simp/SimpCongrTheorems.html
- **[L8]** Batteries `simpNF` and `simpComm` linters: https://raw.githubusercontent.com/leanprover-community/batteries/main/Batteries/Tactic/Lint/Simp.lean ; Lean reference, "Simp Normal Forms": https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-Normal-Forms/
- **[L9]** Aesop README (`aesop?`): https://raw.githubusercontent.com/leanprover-community/aesop/master/README.md
- **[L10]** Zulip, "Ways to speed up Mathlib" (April 2024 profile): https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Ways.20to.20speed.20up.20Mathlib.html
- **[L11]** Lean reference, "The grind tactic": https://lean-lang.org/doc/reference/latest/The--grind--tactic/ ; release notes v4.22.0: https://lean-lang.org/doc/reference/latest/releases/v4.22.0/
- **[L12]** Mathlib `grw`: https://florisvandoorn.com/carleson/docs/Mathlib/Tactic/GRewrite/Core.html ; announcement: https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Announcement.3A.20New.20.60grw.60.20tactic.html
- **[R1]** Rocq reference manual, "Generalized rewriting": https://rocq-prover.org/doc/V9.0.0/refman/addendum/generalized-rewriting.html
- **[R2]** M. Sozeau, "A New Look at Generalized Rewriting in Type Theory", JFR 2(1), 2009: https://jfr.unibo.it/article/view/1574
- **[R3]** Rocq reference manual, `autorewrite`, `Hint Rewrite`: https://rocq-prover.org/doc/V9.0.0/refman/proofs/automatic-tactics/auto.html
- **[R4]** Rocq Discourse (search snippet only): https://discourse.rocq-prover.org/t/extensional-setoids-on-functions-and-rewriting/250/9
- **[I1]** Isabelle/Isar reference, `Generic.thy`: https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/master/src/Doc/Isar_Ref/Generic.thy
- **[I2]** LCF kernel, from a survey rather than the Isar manual: https://ar5iv.labs.arxiv.org/html/1907.02836
- **[A1]** Agda, rewriting: https://agda.readthedocs.io/en/latest/language/rewriting.html ; J. Cockx, "Type Theory Unchained", TYPES 2019: https://drops.dagstuhl.de/opus/volltexte/2020/13066/
- **[A2]** Agda, safe Agda: https://agda.readthedocs.io/en/latest/language/safe-agda.html
- **[A3]** Agda, with-abstraction (`rewrite`): https://agda.readthedocs.io/en/latest/language/with-abstraction.html
- **[D1]** Idris 2 tutorial, theorem proving: https://idris2.readthedocs.io/en/latest/tutorial/theorems.html
- **[D2]** Idris 2 `Language.Reflection`: https://idris2docs.sinyax.net/data/base/docs/Language.Reflection.html
