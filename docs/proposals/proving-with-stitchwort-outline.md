# Proposal: *Proving with Stitchwort*, an outline

**Status:** draft 1, 11 November 2026 (SW-2891, from D3520). An outline for
Matt to review before any chapter is written. Decisions for Matt are in
[§7](#7-decisions-for-matt), each with a recommendation; candidate tickets
are in [§6](#6-gaps-candidate-tickets).

**The request (D3520, Matt, 11 Nov 2026).** A new, native Stitchwort book
that teaches the same general ideas as *Software Foundations* (SF), in
Stitchwort's own way and voice, and that teaches the editor as part of the
method: the reader works in VS Code or in the web playground, and uses case
splits, goals, search and the rest as they go. `sf/` stays the faithful
port. This book is written fresh: no SF prose, and its own examples and
exercises (SF's authors ask that solutions to theirs not be posted, and we
want our own voice anyway). The complaint about the port: Basics.sw "doesn't
read like a very good tutorial. It's constantly referring to Rocq."

## 1. Audience and promise

**Who.** A programmer who knows a typed language (TypeScript, Scala, Rust,
Kotlin) and has never proved anything about a program. No logic or type
theory is assumed. The reader of `docs/guide/` is the same person; this book is the hands-on companion for
the proving half of the language.

**The promise, at the end of Part I (chapters 1 to 6, about 6 hours).** The
reader can:

- write a small functional program with its own data types, and test it;
- state a fact about it as a theorem, and see quickly whether it is false
  (a counterexample) before trying to prove it;
- prove it by computing, by cases, and by induction, building the proof
  from `?` with the editor's help (goals, splits, missing arms, search);
- know when to hand a step to `omega`, `cases` or `ring`, and what each
  can't do;
- write a spec separate from the code, and prove the code meets it,
  generalising an induction when the first try fails.

**At the end of Part II (chapters 7 to 12, about 7 hours more).** The
reader can use the logic (`∧ ∨ ¬ → ↔ ∃ ∀`), tell a `Bool` from a statement
and move between them with decisions, define rules as inductive
propositions and prove things by their evidence, and read a proof as the
program it is.

**At the end of Part III (chapters 13 to 15, about 5 hours more).** The
reader has defined a small language, an evaluator, an optimiser and a
compiler to a stack machine, and proved the optimiser and the compiler
correct.

**Time per chapter.** 45 to 90 minutes each, stated at the top of each
chapter, measured on a first reader once written (an agent run is not a
measure of a human reader). Each chapter is one sitting: it ends with the
file checking, give or take the exercises.

**Tone.** Second person, present tense, short sentences, everyday words.
Rocq is never mentioned in the chapters themselves; one appendix,
"Coming from Rocq, Lean or SF", maps the vocabulary (§3, appendix A).

## 2. Form

### 2.1 Where it lives

A Stitchwort project at the repo root, beside `sf/`, `aoc/` and `games/`:

```
book/
  stitchwort.yaml          sources: [src]
                           check:
                             open-goals: warn
  README.md                how to open it, chapter list, time per chapter
  src/Book/Computing/Computing.sw        namespace Book.Computing
  src/Book/Cases/Cases.sw                namespace Book.Cases
  ...
solutions/                 (decision 4) a second project with every exercise done
```

One namespace per chapter, one file per chapter where possible (a long
chapter may have a second file for its exercises, `Exercises.sw` in the same
namespace, so the reading flow and the to-do list are separate). Files are
read top to bottom in the editor: prose as `--` comments, code as code, the
same form as `docs/tutorial/` and `web/guide/`. A chapter imports only `Std`
and, where it builds on an earlier chapter's definitions, that chapter's
namespace (open theorems are usable since SW-2805, so a reader who skipped
an exercise can still go on). Most chapters stand alone, so a reader can
start at chapter 7 and the playground checks one chapter quickly.

**Exercises are `?`.** A theorem to prove ends `:= ?`; a function to write
has `?` as its body. With `open-goals: warn`, `stitchwort check` passes and
reports each `?` as a goal; `audit` fails what rests on one. This is exactly
how SF's port works (sf/README.md), and the reader meets it in chapter 1.
Each exercise is introduced in prose with a one-line label in a fixed form
so it reads well and can be found:

```
-- Exercise 3.2 (two stars). `double` always gives an even number.
theorem doubleEven (n: Nat): isEven (double n) := ?
```

Stars (one to three) say how hard; "(by hand)" marks an exercise where
automation would skip the point (§4).

### 2.2 Opening it in VS Code

From a checkout: `nix develop -c task vscode:install` (as the tutorial's
step 1 says today), then *File > Open Folder* on `book/`. The project is
found from `book/stitchwort.yaml`; every chapter checks as you type. The
Testing panel lists the chapters' tests, and the Problems panel lists every
open `?` (the reader's to-do list). Chapter 0 walks through this with
screenshots-in-words, as the tutorial's step 1 does, and says what to do
when hover shows nothing (the Output panel's "Stitchwort" channel).

Not every reader will build from source. Decision 5 asks whether the book
waits on a packaged install (a release binary and a Marketplace or `.vsix`
extension); until then, the book's front page leads with the playground.

### 2.3 Opening it in the playground

The playground already opens multi-file projects (AoC, the roguelike) from
its Example dropdown, keeps each file's edits in the browser
(`stitchwort.project.NAME.file.PATH` in localStorage), resets a project to
its bundled text, lists open goals with a button that jumps to each, and
shows "N goals open" in the status line (web/index.html, `goalsView` and
the status at its line ~2281; verified by reading). The book would be one
more bundled project, with one dropdown entry per chapter, and a link per
chapter (`…/#book/3`) so the book's web page and README can say "open
chapter 3 in your browser" as one click.

Two things stand in the way today (verified by reading
`web/bundle-projects.sh`): it bundles only `aoc/` and `games/rogue/`, and it
refuses a project whose `stitchwort.yaml` is anything but `sources: [src]`
(D112), so the book's `check: open-goals: warn` line would be refused.
SW-2723 (sf/ in the playground) has the same problem; §6 gap G1 covers both.

### 2.4 How progress is shown

- **In the file:** each `?` is underlined as a goal, not an error.
- **VS Code:** the Problems panel lists the open goals; `stitchwort goal`
  in a terminal lists every open goal with what relies on it.
- **Playground:** the status line says "N goals open", and the check
  panel's "Goals (N open)" list jumps to each.
- **Per chapter:** nothing today says "chapter 3: 4 of 11 exercises left".
  Gap G6 proposes a one-line summary per namespace from `stitchwort goal`,
  which the book's README can tell readers to run, and which the
  playground's status line could show for the open file.

## 3. Chapters

Same general arc as SF's *Logical Foundations* (Basics, Induction, Lists,
Poly, Tactics, Logic, IndProp, Rel, ProofObjects, Maps, Imp), reordered
and regrouped where Stitchwort's strengths change the best order: proofs
are terms from the first page (so "proof objects" is not a late surprise),
`match` on a value and `match` in a proof are the same thing, decisions
(Bool against statements) are a chapter of their own, and specs come early
because they are what makes proving about programs worth it.

The editor column says where each action works. **VS Code** and
**Playground** are marked *yes* only where I verified it by reading the
code (`editors/vscode/`, `crates/lsp/src/lib.rs`,
`web/editor/src/editor-entry.js`, `web/index.html`); *expected* means the
same server code runs but I didn't confirm the playground's UI shows it.
The summary table is §3.16.

Example names below are placeholders for the chapter author; all are new
(none is SF's: no days of the week, no `nandb`, no grades, no `natlist`,
no `bin`).

### Chapter 0. Setting up (15 min)

- **Ideas:** what the book is for; how a chapter file is read; what `?`
  means; how to see your progress.
- **Features:** none new; a five-line program to confirm the editor works.
- **Editor:** hover; the Problems panel and the playground's goal list;
  run a test (VS Code "▶ Run test"; playground Tests tab); open the Goals
  panel (VS Code "Stitchwort: Show Goals"; the playground's panel under the
  editor appears by itself at the first answer, as VS Code's does).
- **Exercises:** none; one "put a `?` here and hover it" step.

### Part I. Programs and their proofs

### Chapter 1. Computing (45 min) — SF Basics, first half

- **Ideas:** a program is a set of definitions that compute; a test checks
  one input; a theorem checks every input; `rfl` means "both sides compute
  to the same thing"; a false theorem has a counterexample.
- **Features:** `type` with constructors (an enumeration), `def` with
  arms, `match`, `Bool` and `if`, `test`, `theorem … := rfl`, `?` as a
  hole in a definition.
- **Editor:** hover for types and docs; F12 into the library (`Bool` is
  ordinary data); semantic colours (constructors against functions); run a
  test; break a theorem on purpose and read the counterexample note
  (VS Code yes, from the tutorial's step 7; playground expected).
- **Example:** rock, paper, scissors: `type Move`, `beats`, `counter`.
- **Exercises:**
  1. Write `Move.counter` (the move that beats a given move) and prove
     `beats (counter m) m` for `m := Rock` with `rfl`.
  2. Traffic lights: write `next: Light → Light` so that four steps from
     any light come back to it, and state it for `Amber` as a theorem.
  3. Write `Bool.implies` and its four tests; then state, as a theorem,
     that `implies True b` is `b` for one `b`.

### Chapter 2. Cases (60 min) — SF Basics, second half

- **Ideas:** a theorem about every move is proved one move at a time; the
  proof has the same shape as the function; a theorem's parameters are
  its "for every"; hypotheses; `rfl` works under variables only when the
  function can compute.
- **Features:** theorem parameters, `match` in a proof, nested and
  multi-column `match`, `_`, hypotheses `(h: a = b)`, `rewrite h`,
  `cases` (introduced at the end, §4).
- **Editor:** *split from a `?`* ("Split on `m`", SW-2885: VS Code yes;
  playground applies only the first code action, gap G2); *Add the missing
  arms* on `E-NONEXHAUSTIVE` (VS Code yes; playground first action only);
  split a pattern variable in an arm ("Split `x` into its cases"); the
  Goals panel following the cursor between arms (VS Code and the playground, G3).
- **Exercises:**
  1. No move beats itself: `¬ beats m m`, by splitting `m` (one star).
  2. `beats a b → ¬ beats b a`, by splitting `a` and then `b` in the same
     `match` (the split adds a column, SW-2885) (two stars).
  3. A three-valued logic (`Yes | No | Unknown`) with `and3`: prove it
     commutative and that `No` absorbs, then compare the work with `cases`.

### Chapter 3. Numbers and induction (75 min) — SF Basics' numbers, Induction

- **Ideas:** `Nat` is data (`Zero`, `Succ`), printed as digits; a function
  computes on the argument it matches on, so `n + 0 = n` is `rfl` and
  `0 + n = n` isn't (std's `+` recurses on its second argument; the
  chapter turns this into the lesson rather than hiding it); induction is a
  proof that calls itself on a smaller value; the induction hypothesis;
  `rewrite` with it; lemmas, and using one proof in another.
- **Features:** `Nat` and its literals, recursion on `Succ m`, a theorem
  with arms (`∀ (n: Nat) => …` and `| 0 => … | Succ m => …`), the
  termination check on proofs, `rewrite a, b`, `omega` and `ring` (end of
  chapter, §4), the generated equations (`double.eq2`, shown on hover).
- **Editor:** hover on a use of a function to see its equations; the
  Goals panel at each step of a `rewrite` chain (VS Code yes, goal at any
  point stages 1 to 3; the playground too, G3); the `E-REWRITE-NOTHING` and
  `E-REFL` notes, which show the goal after rewriting; rename a lemma (F2;
  both, in a project).
- **Exercises (all on the reader's own functions, which `omega` treats as
  unknowns, so they stay induction exercises):**
  1. `double` by recursion; prove `double n = n + n` (two stars).
  2. `sumTo n` (0 + 1 + … + n); prove `2 * sumTo n = n * (n + 1)` by
     induction, first by hand and then with `ring` as the step (two stars).
  3. `isEven` by recursion on two steps; prove `isEven (double n)` (two
     stars, by hand).

### Chapter 4. Lists and options (75 min) — SF Lists

- **Ideas:** lists are data; proofs about them follow the list; the
  library has lemmas, and finding them is a skill; `Option` for "might not
  be there"; a lemma you need to finish a proof (proving a helper first).
- **Features:** `[x, ..xs]` patterns and literals, `++`, `List` methods,
  dot calls (`xs.length`), `Option` with `Some`/`None`, `match some |`
  clause lambdas, std lemmas by name (`List.appendNil`), `omega [facts]`.
- **Editor:** *search for a proof* on a `?` (SW-2890's "Search for a
  proof" action: VS Code yes once merged; playground first action only,
  G2); `stitchwort search` and `search --at` in a terminal (VS Code only);
  completion after `xs.`; F12 and Shift-F12 into std's `List`; go back
  (Cmd-[ in the playground).
- **Example:** a playlist (`List Song`), with `skip`, `shuffleBack`,
  `lookup` by title returning `Option Song`.
- **Exercises:**
  1. `Playlist.duration (a ++ b) = a.duration + b.duration` (two stars).
  2. `lastSong: List Song → Option Song`, and prove
     `lastSong (xs ++ [s]) = Some s` (two stars; needs a helper).
  3. Reversing twice: prove it for the reader's own `reverseSongs` written
     with `++`, then find the std lemma that proves it for `List.reverse`
     with search (one star, the point is the search).

### Chapter 5. Generic and higher-order functions (75 min) — SF Poly

- **Ideas:** type parameters; functions as values; proving things about
  `map` and `filter` once, for every function passed in; induction that
  follows a function with an `if` (`match induct`).
- **Features:** `[a]` type parameters and implicit arguments, lambdas,
  clause lambdas (`match |`, `matches |`), dots and pipes, `List.map`,
  `filter`, `foldRight`, own `Tree a`, `match induct (f x)` and the named
  equations (`eq2IfTrue`), `f.induct`.
- **Editor:** hover shows a generic function's instantiated type at a
  call; signature help in calls; inlay hints for `let` types (both); the
  goal of each `match induct` alternative (both, at `?`).
- **Example:** a generic binary tree, `Tree a`, with `map`, `size`,
  `toList`, `mirror`.
- **Exercises:**
  1. `(t.map f).size = t.size` (one star).
  2. `t.mirror.mirror = t` and `t.mirror.toList = t.toList.reverse` (two
     stars; the second needs a list lemma, found by search).
  3. `countWhere p xs ≤ xs.length` for the reader's own `countWhere`
     with an `if`, by `match induct` (two stars).

### Chapter 6. Specs (75 min) — no SF counterpart; absorbs docs/tutorial

- **Ideas:** a spec says what a correct answer is, separately from how the
  code gets it; test a statement before proving it; the first induction
  fails; generalise the statement ("what does the loop do from anywhere");
  a proof breaks when the program does.
- **Features:** accumulator loops, `∀` in statements, records and their
  methods, `check --counterexamples`, `[auto …]` parameters (first
  meeting).
- **Editor:** the counterexample note on a `?` whose statement is false
  (VS Code yes; playground expected); `stitchwort check --counterexamples`
  (VS Code terminal only); goal at each arm of a finished proof (VS Code
  yes; playground G3).
- **Example:** the tutorial's basket and till (moved here, rewritten in the
  book's voice; decision 3), or a new one: a bank account's statement
  replayed from its transactions.
- **Exercises:**
  1. A tail-recursive `sumWith acc xs`; prove it meets `xs.sum` (two
     stars; the first try fails, as the chapter shows).
  2. A run-length encoder and decoder; state round-trip and check it for
     counterexamples first, then prove it (three stars).
  3. Break the encoder on purpose and read the counterexample (one star).

### Part II. Logic

### Chapter 7. Equations in depth (60 min) — SF Tactics

SF's Tactics chapter is about Rocq's commands. Here the same skills are
about equations as values: turning them round, applying a function to
both sides, chaining them.

- **Ideas:** an equation is a value you can pass, flip, and chain;
  rewriting in a hypothesis; injectivity of constructors and why
  `Succ a = Succ b` gives `a = b`; distinct constructors are never equal.
- **Features:** `rewrite … at h`, `rewrite <- p` (right to left), `Eq.symm`, `Eq.cong`, `calc` chains, `(proof: …)` to state
  an intermediate step, `cases` for constructor clashes.
- **Editor:** the Goals panel's before/after for each rule of a `rewrite`
  and each line of a `calc` (VS Code yes, SW-2780; playground G3); reading
  `E-TYPE-MISMATCH` side by side.
- **Exercises:**
  1. `Some a = Some b → a = b` (one star).
  2. A `calc` proof that `double (n + m) = double n + double m` from
     chapter 3's lemmas (two stars).
  3. `[x, ..xs] ≠ []` and a list version of injectivity (two stars).

### Chapter 8. Logic (90 min) — SF Logic

- **Ideas:** statements are types and proofs are values of them; `∧` is a
  pair, `∨` a choice, `→` a function, `¬ P` is `P → Void`; `∃` is a value
  with a proof; `↔` is two functions; what "for all" means for a proof.
- **Features:** `Both`, `Inl`/`Inr`, `Witness`, `{ forward, backward }`,
  `Void` and `| ()` for an impossible case, `∈` on lists, `Prop`.
- **Editor:** the expected type in the Goals panel away from `?` (VS Code
  yes, `stitchwort/contextAt`; the playground too); split on a hypothesis of
  type `a ∨ b` (not offered today: G4).
- **Note for the author:** `False` in a statement is the `Bool` `False`,
  read as `False = True` (measured: `cases` reports "goal: False = True").
  It is just as unprovable, but the chapter should teach `Void` as the
  empty statement and show what a goal of `False` displays as.
- **Exercises:**
  1. `p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)` (one star).
  2. `(∃ x => P x ∧ Q x) → (∃ x => P x) ∧ (∃ x => Q x)`, and why the
     converse fails, with a counterexample in words (two stars).
  3. `x ∈ xs ++ ys ↔ x ∈ xs ∨ x ∈ ys`, by induction (three stars).

### Chapter 9. Decisions (60 min) — SF Logic's "Prop vs bool", Stitchwort's own

- **Ideas:** a `Bool` is computed at run time; a statement is proved; a
  `Bool` where a statement is expected means `b = True`; a decision gives
  both the answer and the evidence; `if h:` hands a branch the fact;
  `auto` parameters find proofs a caller doesn't write.
- **Features:** `if h: P then … else …`, `match fits: e with`,
  `Decidable`, `[auto ok: …]`, `Vec.getLt` and other functions that take
  proofs, `byDecision`.
- **Editor:** `E-AUTO-FALSE` at a call; hover on an `auto` argument to
  see what it found; the goal inside each branch of `if h:` (VS Code yes,
  stage 3 covers `if h:`; playground G3).
- **Exercises:**
  1. `safeDiv (a b: Nat) [auto ok: b ≠ 0]`, and a caller that only calls it
     under `if h: b ≠ 0` (one star).
  2. A `Bool` `isSorted` and a statement `Sorted`; prove they agree
     (three stars).
  3. `clamp low high x` with an `auto` precondition `low ≤ high`, and its
     two bounds (two stars).

### Chapter 10. Rules as data (90 min) — SF IndProp

- **Ideas:** a property defined by rules (an inductive proposition); a
  proof is a derivation built from the rules; taking evidence apart
  (inversion) by `match`; induction on the evidence rather than the number;
  when a property is better as a function and when as rules.
- **Features:** `type Even: Nat → Prop = | EvenZero: … | EvenPlusTwo …`
  (measured: such a type, a proof of it, inversion by `match h with
  | EvenPlusTwo e => e`, and an arm-style `| ()` for an impossible case
  all check), indexed families.
- **Editor:** Add the missing arms on a `match` of evidence (VS Code yes;
  the split actions are for "data types without indices", so they don't
  split evidence: G4).
- **Gaps that bite here:** `match h with | ()` with no right side is a
  parse error (measured; SW-2717), and `cases` doesn't invert an
  inductive-family hypothesis (G5). The chapter can be written around the
  arm-style form, but readers will reach for the other.
- **Example:** a game's legal moves as rules (a knight's reachability on a
  small board), or balanced brackets as rules against a counting function.
- **Exercises:**
  1. `¬ Even 3` (one star).
  2. Balanced brackets: the rules and the counter agree, one direction
     (three stars).
  3. `Even n → Even m → Even (n + m)` by induction on the first evidence
     (two stars).

### Chapter 11. Relations (60 min) — SF Rel

- **Ideas:** a relation is a two-argument proposition; reflexive,
  symmetric, transitive; orders; the reflexive-transitive closure as rules;
  a relation decided by a function.
- **Features:** relations as `a → a → Prop`, implicit arguments in rules,
  instances of `Decidable` for a relation.
- **Editor:** rename a relation across the project (F2, both); find
  references to see which proofs use a rule (Shift-F12; both).
- **Exercises:**
  1. "Divides" is reflexive and transitive (one star each).
  2. The closure of "one step on a board" contains every multi-step path
     (two stars).
  3. A decision procedure for a small relation, with its soundness proof
     (three stars).

### Chapter 12. Proofs are programs (45 min) — SF ProofObjects, IndPrinciples

Short, because the reader has written proofs as terms all along: this
chapter names what they've been doing.

- **Ideas:** every proof so far was a program; `∀` is a function type; an
  induction proof is a recursive function, and the termination check is
  what makes it valid; `f.induct` is a theorem with a type you can read;
  axioms, and `stitchwort axioms`.
- **Features:** `f.induct` and its statement, proofs written as lambdas,
  `stitchwort axioms`, `stitchwort audit`.
- **Editor:** hover on `f.induct` to read its statement; hover on a
  recursive call in a proof to see the termination measure (if shown;
  check when writing).
- **Exercises:**
  1. Write the induction principle for chapter 5's `Tree` as a theorem,
     proved by recursion (two stars).
  2. Use it to reprove `mirror (mirror t) = t` without arms (one star).

### Part III. A small language

### Chapter 13. Environments (45 min) — SF Maps

- **Ideas:** a map from names to values; maps as functions against std's
  `Map`; the lemmas a map needs (update then look up).
- **Features:** `Map`, `Text` keys, function-valued records, `Quot.funext`
  (only if needed; check when writing).
- **Exercises:** three lemmas about `update` and `lookup` on the
  chapter's own function-map, then the same through std's `Map` with
  search.

### Chapter 14. A calculator (90 min) — SF Imp, first part, rethought

- **Ideas:** a syntax tree; an evaluator; an optimiser that must not
  change the meaning (constant folding); a compiler to a stack machine and
  its correctness; generalising over the rest of the program (the stack
  that's already there), which is chapter 6's lesson again.
- **Features:** a recursive data type of expressions, `Option` for
  division by zero, a `Parse` front end (optional, for fun: `Parse` is in
  std), `match induct` over the evaluator.
- **Editor:** split from `?` across a seven-constructor type; the
  counterexample note on a wrong optimiser (a folding rule that drops a
  division by zero).
- **Exercises:**
  1. `simplify` keeps the value: `(simplify e).eval env = e.eval env`
     (two stars).
  2. Compiler correctness for the stack machine, generalised over the
     starting stack (three stars).
  3. Add `Let` to the language and repair the proofs (three stars).

### Chapter 15. Commands and loops (90 min) — SF Imp, second part

- **Ideas:** commands that change a state; why `while` can't be a plain
  total function (fuel against rules); big-step evaluation as rules;
  program equivalence; a fuel interpreter agrees with the rules.
- **Features:** chapter 10's rules for the evaluation relation, fuel
  arguments, `Partial` mentioned as the alternative.
- **Exercises:** a loop that sums `1..n`, proved correct by the rules
  (three stars); two programs equivalent (two stars); fuel monotonicity
  (two stars).

### Appendices

- **A. Coming from Rocq, Lean or SF.** The vocabulary map (tactic to term:
  `intros` to parameters, `destruct` to `match`, `induction` to
  recursion, `Admitted` to `?`, `Compute` to `test` and the Evaluate tab,
  `Check` to hover and `:t`, `inversion` to `match` on evidence). The only
  place other provers are named.
- **B. The editor, one page.** Every action the book used, its key in
  VS Code and in the playground, and what works where (the table in
  §3.16, kept current).
- **C. Effects (later, optional).** Proving about programs with abilities
  (guide chapter 10's "Proofs about effectful code"); not part of the
  first release.

### 3.16 The editor actions, where each works

| Action | Chapter | VS Code | Playground | Evidence |
|---|---|---|---|---|
| Hover: type, doc, equations | 1 | yes | yes | lsp-client `languageServerExtensions`, editor-entry.js header |
| Goal of a `?` (panel) | 0 | yes ("Show Goals") | yes, under the editor | extension.js; index.html `showGoal`, editor-entry.js `refreshGoal` |
| Goal anywhere, steps of `rewrite`/`calc`/arms | 3 | yes (SW-2778, SW-2780) | yes (SW-2894): `goalAt`, then `contextAt` after 300 ms, as VS Code | editor-entry.js `refreshGoal`; syntax.md "The editor shows the goal anywhere" (G3) |
| Add the missing arms | 2 | yes, light bulb | first code action applied, no menu | editor-entry.js `codeAction` applies `actions[0]` (G2) |
| Split on `x` from a `?` / split an arm's variable | 2 | yes (SW-2885) | first action only | as above (G2) |
| Proof offered / "Search for a proof" on a `?` | 4 | yes (SW-2890 in flight) | first action only; search in wasm runs without the kept session (SW-1807) | lib.rs `code_action`; G2 |
| Counterexample note on a false statement | 1, 6 | yes (tutorial step 7) | expected (same server; not confirmed in a browser) | crates/elab/src/counterexample |
| `check --counterexamples`, `search`, `goal` | 4, 6 | terminal | no CLI; Goals list with jump buttons instead | index.html `goalsView` |
| Rename (F2) | 3 | yes | yes, in a project (lone file: SW-2644) | editor-entry.js `rename` |
| Go to definition, references, into std | 1 | yes | yes (std read-only, Cmd-[ back) | editor-entry.js keymap |
| Completion, signature help, inlay `let` types | 4, 5 | yes | yes | editor-entry.js header |
| Run a test | 0, 1 | "▶ Run test" icons, Testing panel | Tests tab (whole file), no per-test icons | guide 01 "Settings" |
| Import quick fix | 4 | yes | first action only | lib.rs `import_fixes` |
| Format on save | 0 | yes | yes (⚙ menu) | guide 01 |
| Progress: open goals | 0 | Problems panel; `stitchwort goal` | status "N goals open", Goals list | index.html ~2281 |

## 4. When automation appears

**The rule: by hand first, then the tool as a step.** Each piece of
automation enters at the end of the chapter that does its work by hand,
once the reader has done that work at least twice, and is introduced as
"what you just did, done for you":

| Tool | By hand first in | Introduced | Stays useful for |
|---|---|---|---|
| counterexamples | — | chapter 1 (it's a check, not a proof) | every chapter: try a statement before proving it |
| `cases` | chapter 2's splits | end of chapter 2 | routine splits, constructor clashes (ch. 7) |
| `omega` | chapter 3's arithmetic lemmas | end of chapter 3 | the arithmetic left after an induction step |
| `ring` | chapter 3's `sumTo` | end of chapter 3 | polynomial steps |
| proof search (Cmd-. "Search for a proof", `search --at`) | chapter 4 | chapter 4 | finding library lemmas |
| `match induct` | chapter 5's hand split on an `if` | chapter 5 | functions with conditions |
| `auto` | chapter 9 | chapter 9 | preconditions |

**How exercises stay meaningful once the tools exist.** SF's port hid the
library (its own `Nat`, its own lists) so that the tools couldn't solve the
exercises. This book does the opposite, since the library and the tools are
what a Stitchwort programmer will use:

1. **Exercises are about the reader's own definitions.** `omega` treats a
   call of an unknown function as an opaque number, so `double n = n + n`
   for the reader's recursive `double` needs induction, and `omega` only
   helps with the arithmetic left in the step. `cases` splits the reader's
   types, but induction and generalisation are never one word. Every
   exercise is checked against the tools when written (G7 automates this):
   if `rfl`, `cases`, `omega` or `ring` alone closes it, it is either
   marked "(by hand)" or rewritten.
2. **Where an exercise is about the library itself** (`0 + n = n` in
   chapter 3), the book says plainly that `omega` proves it and asks for the
   hand proof as practice, marked "(by hand)". There's no checker for
   "by hand"; it's the reader's practice, as in any book (decision 6).
3. **After its chapter, a tool is a step, not an answer.** Later exercises
   expect `omega [ih]` inside an induction, and are written so that the
   induction, the generalisation or the choice of lemma is the work.

## 5. Relation to the existing material

- **`docs/tutorial/` (two parts, about 90 minutes, a basket and a till).**
  It teaches the same things as chapters 1 to 6 in compressed form, in VS
  Code only. Keeping both means two first-proof stories that drift.
  Recommendation (decision 3): the book replaces it. Its till and basket,
  and its "first try fails, generalise" story, move into chapter 6
  (rewritten in the book's voice); until chapter 6 is written, the
  tutorial stays and the guide links both.
- **`docs/guide/10-proofs.md`** stays the reference-style explanation, and
  each chapter ends with "More: guide chapter 10, §…". The book doesn't
  repeat the guide's full rules.
- **`web/guide/` (the feature tour)** stays a page per feature; the book
  links tour pages (23 to 27, 36, 37) where a feature first appears.
- **`sf/`** stays the faithful port, for readers who want SF itself.
  Appendix A points to it.
- **`docs/proving-guide.md`** is for agent lanes and stays separate; the
  book may borrow its "common errors and what they usually mean" list for
  appendix B.

## 6. Gaps: candidate tickets

Each is one line; the ones the first chapters need are marked **(ch. N)**.

- **G1 (playground bundling; ch. 0).** Bundle `book/` (and `sf/`, SW-2723)
  in the playground: let `web/bundle-projects.sh` accept a `check:` key in
  `stitchwort.yaml` (the playground shows open goals as goals, not
  failures, already), a manifest whose entries are chapters rather than
  days, and a link per chapter (`#book/3`).
- **G2 (playground code actions; ch. 2).** A code-action menu in the
  playground: Cmd-. lists every action at the cursor (Add the missing
  arms, Split on each variable, Search for a proof, imports) instead of
  applying the first one.
- **G3 (playground goals; ch. 3) — done, SW-2894.** Goal at any point in the playground:
  ask `stitchwort/contextAt` away from `?` and show the before/after steps,
  as VS Code's panel does since SW-2778/SW-2780; show the panel whether or
  not the file has a `?`.
- **G4 (splits; ch. 8, 10).** Split a hypothesis of an indexed family
  (evidence of `Even n`) or of `∨`/`∧`/`∃` from a `?`: today's split
  actions take "data types without indices" only.
- **G5 (inversion; ch. 10).** `cases` inverts a hypothesis whose type is an
  inductive family (`h: Even 1` closes the goal; `h: Even (n + 2)` yields
  `Even n`); today it finds "nothing to split on" (SW-2707 §7). With
  SW-2717 (`match h with | ()`), the two IndProp gaps.
- **G6 (progress; ch. 0).** `stitchwort goal --summary`: open goals per
  namespace ("Book.Induction: 3 open"), and the playground's status line
  showing the open file's count.
- **G7 (authoring; all).** A task that tries `rfl`, `cases`, `omega`, `ring`
  and proof search on every `?` of a project and lists those one word
  closes, so the book's author knows which exercises the tools give away
  (and the list is kept current as the tools get stronger).
- **G8 (release; ch. 0).** A packaged install for readers without the repo:
  a release binary and the VS Code extension as a `.vsix` or on the
  Marketplace (decision 5).
- **G9 (rendering; later).** An HTML rendering of a chapter file (comments
  as prose, code as code), for the book's own web page, and for reading it
  without an editor; the tour's `guide.html` may already do most of this
  for `web/guide/*.sw`.
- **G10 (small; ch. 8).** Hover on `False` in a statement says it reads as
  `False = True` and suggests `Void` for "no proof"; or a note on goals
  shown as `False = True`.

Already tracked and wanted by the book: SW-2717 (`match h with | ()`),
SW-2781 (Next/Previous proof step commands), SW-2782 (`cases` and `omega`
show what they did), SW-2886 to SW-2888 (split follow-ups), SW-2889 (split
picks the right type), SW-2890 (Cmd-. at once), SW-2644 (rename in a lone
file), SW-1862 (tour page on holes).

## 7. Decisions for Matt

1. **Title.** *Proving with Stitchwort*. Alternatives: *Programs and
   Proofs in Stitchwort*; *Stitchwort Foundations*. **Rec: *Proving with
   Stitchwort*** (says what the reader will do; no echo of SF's title).
2. **Location.** A project at `book/` (namespaces `Book.Computing`, …),
   beside `sf/`. Alternatives: `docs/book/` (but it's a project with a
   `stitchwort.yaml`, like `sf/`, not prose). **Rec: `book/`**, and register
   it with the tiers and `audit:touched` as `sf/` would be (SW-2707 §10).
3. **Relation to `docs/tutorial/`.** Absorb, link or replace. **Rec:
   replace**, in two steps: the tutorial stays until chapter 6 is written,
   then its examples move into chapter 6 and the tutorial is removed, with
   the guide's README pointing at the book.
4. **Solutions.** The book is ours, so solutions can be public. **Rec: a
   `book/solutions/` project with every exercise done, checked by the
   tiers** (so exercises are known to be solvable and don't rot as the
   language changes), not bundled in the playground; the chapters don't
   link it, the README does, under a "spoilers" heading.
5. **Who it's for first: VS Code from a checkout, or the playground.**
   Without a packaged install (G8), VS Code means cloning and building.
   **Rec: write for both, lead with the playground** on the book's front
   page once G1 is done, and leave G8 to a separate decision about
   releases.
6. **Automation in exercises.** Enforce "by hand" (a setting that turns
   tactics off in a namespace, which is new user-visible language) or rely
   on exercise design and labels (§4). **Rec: no enforcement**; design and
   labels, with G7 to keep it honest.
7. **First chapters to write.** **Rec: chapters 0 to 3** in the first lane
   (Opus, about 4 hours of writing; chapters are prose-heavy and set the
   voice), after G2 (playground code-action menu) so chapter 2's split
   steps work in both editors; then chapters 4 to 6 in a second lane, then
   a review by a reader who hasn't seen the drafts before Part II.
8. **Scope of the first release.** **Rec: Part I (chapters 0 to 6)**, then
   decide on Parts II and III after a reader has been through it. Parts
   II and III depend on G4 and G5 (and SW-2717) to read well.
