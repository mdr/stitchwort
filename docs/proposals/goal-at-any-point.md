# The goal at any point of a proof

**Status:** draft 1, 11 November 2026 (SW-2715, D3496), awaiting Matt's decisions
([§9](#9-decisions-for-matt)). Design only: no code changed. It extends
[lsp-goal-holes.md](lsp-goal-holes.md), whose stage 2d built the Goals panel for `?` and left
"the expected type and context at any expression" for later (its §8.4, PROVISIONAL 1).

Written against `main` at `dd55a4020`. Labels: **[checked]** read in this repository at the
place given; **[ran]** run for this note with the release CLI already built in the main
checkout (05:18 today), on scratch copies outside the repository (§10 lists them);
**[cited]** read in the linked source; **[inferred]** my reasoning, not tested.

Related: [goal-as-written.md](goal-as-written.md) and [goal-printing-gaps.md](goal-printing-gaps.md)
(how a goal is *printed*: this note only decides *where and when* one is shown, and prints
every goal with today's printer), [editor-and-playground-roadmap.md](editor-and-playground-roadmap.md)
§3 (where the probe this note builds on was built, SW-1116),
[the SW-2707 review](../reviews/SW-2707-software-foundations-port.md) §6 item 4 (the trigger).

## Contents

0. [Summary](#0-summary)
1. [How other systems let a reader follow a proof](#1-how-other-systems-let-a-reader-follow-a-proof)
2. [Where Stitchwort stands today](#2-where-stitchwort-stands-today)
3. [What "the goal at a point" means](#3-what-the-goal-at-a-point-means)
4. [How it works](#4-how-it-works)
5. [What the user sees: editor and CLI](#5-what-the-user-sees-editor-and-cli)
6. [Designs compared](#6-designs-compared)
7. [Stages](#7-stages)
8. [Calls made](#8-calls-made)
9. [Decisions for Matt](#9-decisions-for-matt)
10. [Risks, what this note didn't do, sources](#10-risks-what-this-note-didnt-do-sources)

## 0. Summary

**The problem.** A reader of a finished Stitchwort proof can't see what is being proved at
each step. In `rewrite Nat.mulZero p, Nat.mulZero q in rfl` nothing shows the goal between
the two rules; in a `match`, nothing shows the goal of an arm unless you replace its proof
with `?`; in a `calc`, nothing shows a step's statement unless you put the cursor inside its
proof. Rocq's readers step through a script and watch the goal change after every tactic,
and Software Foundations is written around that ("It is worth stepping through these proofs
to observe how the context and the goal change", Basics.v:1033). The same gap hurts anyone
fixing a broken proof, reviewing one, or, now, an agent working on one: an agent has no way
at all to ask "what has to be proved here?" without editing the file.

**The change.** For any position in a declaration, answer: the **goal** there (what the
expression at the cursor has to prove, or the type it must have in a program), the
**names in scope** with their types, and, where the cursor is on a proof **step** (a
`match` arm, a rule of a `rewrite` chain, a `calc` line, a `cases`, an `omega`, a lambda or
`let`), the goal **before and after** that step and what it added. The editor's Goals panel
follows the cursor everywhere, not only at `?`; two commands step the cursor through a
proof's steps; a new command, `stitchwort goal --at FILE:LINE[:COL]`, gives the same answer
as text or JSON, and `--steps` lists every step of the declaration with its goals, the
"proof movie" an agent or a reader can read top to bottom.

**What it should do.** Half of it already exists and is unused: a request
`stitchwort/contextAt` that the language server answers for any cursor (SW-1116), which
the VS Code client never sends. Wiring it into the panel (stage 1, about 45 minutes) shows
goals inside every arm, every `calc` proof, at every `omega` and `cases`, after every
`let`, at once [ran: §2.2 lists what it answers today]. The new parts are the steps
(before and after each `rewrite` rule, an arm's goal on its pattern, a `calc` line's
statement), the CLI, and speed: today each answer re-checks the whole namespace, 0.3 to
0.8 s in a 25-line file and 1.4 to 1.6 s in AoC 2025 day 8's proofs [ran], too slow
for a panel that follows the cursor. Checking only the declaration under the cursor, once
per edit, and keeping its answers for every point in it, makes cursor moves free and an
edit cost that one declaration's check (tens of ms for most; 330 ms for the slowest AoC
theorem measured in lsp-goal-holes.md §4.1) [inferred from those timings].

**Not known yet.** How far error recovery inside a branch (goals after a broken step,
stage 6) can go without changing what a normal check does; whether readers want the
before/after of every step in the panel or find it noisy (stage 3 ships it behind the
panel's own toggle, a call I made, §8).

## 1. How other systems let a reader follow a proof

The survey was done for this note on 11 Nov 2026 from the sources in §10. **[cited]** means
I read it in that source. **[inferred]** means my reading, and **[unconfirmed]** means I
looked and couldn't confirm it.

### 1.1 System by system

**Lean 4: the infoview.**
- *What the reader sees.* In a tactic proof, the infoview shows "the current proof state
  with all currently open proof goals". In a term, it shows "the current expected type at
  the position of the cursor". When a tactic changes a goal, the infoview highlights what
  changed: red for what is about to go, green for what was just added. There are settings
  to hide instance, inaccessible or `let`-value hypotheses, and the panel can be pinned or
  paused [cited: vscode-lean4 manual].
- *How it is built.* The server answers from the **InfoTree**, which elaboration records
  as it goes. A `TermInfo` node holds the term, `expectedType?` and the local context it was
  elaborated in. A `TacticInfo` node holds `goalsBefore` and `goalsAfter` with their
  metavariable contexts. A switch, `InfoState.enabled`, turns recording on or off
  [cited: `InfoTree/Types.lean`].
- *Where the cursor is.*
  - The term goal shows the expected type, **falling back to the inferred type**, with the
    node's context. On a binder, the binder itself is popped from the context.
  - On the head of an application, the term goal is the whole application's
    (`termGoalAt?`).
  - Among tactic nodes the innermost wins. The *after* state is shown once the cursor is
    past a tactic's start and no nested tactic follows [cited: `RequestHandling.lean`,
    `InfoTree/Util.lean`].
  - Hover shows `expr : type`, preferring the smallest span [cited: same].
- *Term-mode proofs.* Lean's term-mode support is the weaker half. Lean users ask for a
  goal "without having to change the term", and type `_` to get one [cited: Zulip,
  "Infoview in term mode"]. That is Stitchwort's situation today.
- *Memory cost.* I couldn't find any documented cost of recording the InfoTree
  [unconfirmed].
- *Widgets.* Nawrocki, Ayers and Ebner, ITP 2023: user interfaces built on "presentations"
  that keep references to the objects they show. Mathlib's calc widget builds the next
  `calc` step from subterms you shift-click [cited].
- *Paperproof* (Karunus and Kovsharov). It draws a tactic proof as a Gentzen-style tree:
  goals and hypotheses are nodes, and each tactic links a before state to its after states.
  It is built from `goalsBefore` and `goalsAfter`. It doesn't cover term-mode proofs, and
  I found no paper [cited: Kovsharov's post].
- *For Stitchwort.* Copy Lean's term-goal rules: expected type, else the type found; the
  context recorded at the node; binder and head-of-application positions. Copy the
  before/after highlighting from its tactic side.

**Rocq.**
- *CoqIDE and Proof General.* The reader steps sentence by sentence through a locked
  region and sees the goals after the last checked sentence [inferred: well known].
- *VsRocq (VsCoq 2).* Manual stepping by default. A continuous mode updates the goal panel
  "as you scroll or edit" [cited].
- *coq-lsp* (Gallego Arias).
  - Checks continuously and incrementally. It recovers from errors by admitting the
    unfinished parts, so goals after an error still show.
  - Its `proof/goals` request takes a position and a `mode` of `Prev` or `After`. At a
    blank position it answers for the previous sentence [cited: coq-lsp README and
    PROTOCOL.md].
  - `petanque` is its protocol for agents: `get_state_at_pos`, `run_at_pos`, `goals`
    [cited].
- *Proof diffs* (`Set Diffs`, Jim Fehrle). Each new goal is paired with the one it came
  from. Hypotheses are matched **by name** and compared token by token with Myers' diff
  algorithm [cited: refman].
- *jsCoq* (UITP 2016). Coq in the browser [cited].
- *Alectryon* (Pit-Claudel, SLE 2020). It compiles a proof script into a **static** web
  page with the goals after every sentence captured at build time. The reader hovers or
  taps a sentence to see them, needing only CSS and no Coq. I found no user study, and
  Lean appears only as future work [cited].
- *Term-mode proofs.* A Rocq `refine` or `exact` term is one sentence with no positions
  inside it [inferred].
- *For Stitchwort.*
  - Explicit before and after for a step, and a rule for blank positions (the previous
    one).
  - Diffs that match hypotheses by name.
  - Alectryon's static proof movie, for the CLI's `--steps` and later for the SF port's
    HTML.
  - coq-lsp's recovery from errors: stage 6.

**Isabelle/jEdit and Isar**, the closest relative of a written-out proof.
- *What the reader sees.* The Output panel shows the messages of the command at the
  cursor, which are already there. The State panel "initiates a real-time query on
  demand, with a full round trip including a fresh print". Several State panels can be
  frozen "to look at an old situation" while the text nearby changes. Printing the proof
  state takes precedence over the automatic tools that run asynchronously. Sledgehammer's
  panel offers proofs that one click inserts [cited: jedit.pdf §3; Wenzel, ITP 2014].
- *Isar's model.* Its virtual machine keeps a stack of nodes, each holding a context, a
  mode and an optional pending goal. The mode is "an instruction to the writer, telling
  what kind of operation may be performed next" [cited: isar-ref.pdf].
  - `?thesis` names the innermost pending claim.
  - `...` names the right side of the last stated fact.
  - `calculation` holds what a chain of `also` steps has proved so far, and `finally`
    concludes it.
  - `case (Suc n)` stands for the `fix` and `assume` of that case. `print_cases` shows
    each case in source notation [cited: isar-ref.pdf].
- *For Stitchwort.* A chain has a **running state** that can be shown without tactics:
  "the chain so far proves `a = c`; this line must prove `c = d`". An arm shows what it
  adds, in source notation. Isar also separates cheap output that is already there from a
  fresh print on demand: §4's split between published `?` goals and the probe.

**Agda.**
- *What the reader sees.* Goals exist only at holes.
  - `C-c C-,` shows the goal and context.
  - `C-c C-.` adds the inferred type of what is written in the hole, and `C-c C-;` that
    term checked against the goal.
  - `C-c C-?` lists all goals.
  - `C-c C-h` writes a helper lemma's type from a hole.
  - Prefix arguments choose how far the goal is normalised (simplified, as written, full
    or head normal form).
  [cited: Agda emacs-mode docs]
- *Positions.* There is no goal at an arbitrary cursor position, and `rewrite`'s
  intermediate equations "are not visible in the code" [cited: with-abstraction docs].
- *Equational reasoning.* A `≡⟨ ? ⟩` hole has the step's equation as its goal
  [inferred].
- *For Stitchwort.* Show the goal and the found type side by side when they differ (D-c).
  A choice of how far to compute a goal would answer "computed vs as written" (D639)
  per query [later].

**Idris 2.**
- Holes are named. `:t` on a hole prints the context above a dashed line and the goal
  below it.
- Case split, add clause, proof search and `makewith` act on a hole.
[cited: Idris 2 tutorial]
- *For Stitchwort.* Holes addressable by name in the CLI. Stitchwort's `?` is unnamed, and
  `search --at --goal N` numbers them instead.

**F\* and Dafny.**
- *F\*.* `assert P by tac` opens a proof state, and `dump "label"` prints the goal and
  hypotheses there. Experts probe what is known at a point with `admit`, `assume false`
  and `assert_norm` (Jain et al., 2025) [cited].
- *Dafny* has no goal display.
  - The gutter marks each line verified, failing or stale.
  - Hover lists the assertion batches.
  - The manual's method is to move an `assert` backwards until it fails.
  - Counterexamples come as assumptions that can be pasted into the code.
  [cited: Dafny reference manual]
- *For Stitchwort.* `omega` and `cases` should say what they were given (F\*'s `dump`):
  stage 5. Dafny's backwards-`assert` technique is what a Stitchwort reader does today with
  `?`, and what this note removes the need for.

**Liquid Haskell.** Proofs are unit values chained with `===` / `==.` and closed with
`*** QED`; `==!` is an unchecked step "only for proof debugging" [cited: proof-combinators
docs]. I couldn't load the course pages that describe its editor feedback
[unconfirmed]. Each step is an SMT obligation, reported as a refinement error where it
fails [inferred].

### 1.2 Research and agent tools

- **Proof by pointing** (Bertot, Kahn and Théry, TACS 1994): click a subterm of the goal to
  build the proof step that works on it [cited]. Lean's calc widget is its modern form.
- **Aitken, Gray, Melham and Thomas** (JSC 1998), a study of HOL users. As reported in a
  later survey, they found users treat proving as programming more than pointing
  [cited, secondhand].
- **Prooftree** (Tews), for Proof General: a tree of goals coloured proven, current and
  open, with sequents shown on hover [cited].
- **QED at Large** (Ringer, Palmskog, Sergey, Gligoric and Tatlock, 2019): the survey of
  proof engineering [cited; I didn't read its interface chapter].
- **QED in Context** (Shi, Torczon, Goldstein, Pierce and Head, OOPSLA 2025): 30 Rocq and
  Lean users observed. Proving is iterative and driven by feedback, so the goal display is
  the main loop [cited].
- **Explorable Proofs** (Kambhamettu, Crichton, Welleck, Goldstein and Head, 2026): links
  the steps of a written proof to Lean code and its states. In a study of 16 people,
  readers answered comprehension questions better [cited].
- **Agents.**
  - LeanDojo (NeurIPS 2023) extracts the state before and after each tactic.
  - Lean's REPL reports each `sorry` as a goal with a `proofState` id that can be
    continued from.
  - Pantograph (2024) was written because Lean's language server is built for people. It
    gives before/after states and turns every `sorry` into a goal.
  - coq-lsp has `petanque`.
  [cited]

  Each of these gives an agent the intermediate states of a proof in one machine-readable
  call. That is what `stitchwort goal --steps --json` is for.

### 1.3 What to borrow, ranked

1. **The expected type at every expression, with its context, answered from what the check
   recorded** (Lean's TermInfo). Show the expected type, else the type found, and both when
   they differ (Agda's `C-c C-.`). On a binder, show what comes after it. On a call's head,
   show the whole call. Stitchwort's probe already does the first part (§2.1). §4 records
   it per declaration rather than per file.
2. **Steps with before and after, and the change highlighted** (Lean's tactic states and
   diffs, Rocq's `Set Diffs` matching hypotheses by name, coq-lsp's `Prev`/`After`). For
   Stitchwort, the steps are the places where a term's goal changes: §3.
3. **A running state for chains** (Isar's `calculation`, `...` and `?thesis`): a `calc` line
   shows what the chain has proved so far and what the line must prove, and a `rewrite`
   rule shows the goal it rewrote and the goal it left.
4. **The whole proof's states in one call or one page** (Alectryon's static movie;
   LeanDojo, Pantograph and `petanque` for agents): `--steps`.
5. **Goals after an error** (coq-lsp and Lean recover; Rocq's IDEs and today's Stitchwort
   stop): stage 6.

Not borrowed now: proof by pointing and widgets (they generate proof text, a different
feature from reading); gutter marks per step (Dafny), which may be worth a ticket once
steps exist.

## 2. Where Stitchwort stands today

### 2.1 What is built

- **`?` goals** (lsp-goal-holes.md stages 2a–2d): a `?` is reported with its goal and
  context; hover on a `?` shows it (`hover_at`, `crates/driver/src/at.rs:313-329`); the
  Goals panel (command "Stitchwort: Show Goals") shows the goal of the `?` at or nearest the
  cursor, from the goals already published, through `stitchwort/goalAt`
  (`editors/vscode/extension.js:106-150`, `crates/lsp/src/lib.rs:4507-4520`). Away from a
  `?` the panel says "No open goal at the cursor." (`editors/vscode/client.js:110`).
  **[checked]**
- **The context at any cursor** (SW-1116, editor-and-playground-roadmap.md §3 "As built"):
  `Elaborator::probe_context(file, offset)` (`crates/elab/src/goals.rs:664`) asks, before a
  check, for the smallest expression containing a position. Every expression offers itself
  through `note_expr` (`crates/elab/src/nav.rs:469`), which calls `note_probe`
  (`goals.rs:732`): it keeps the smallest one containing the position, with its type (the
  type it was checked against, or the type found when inferred) and the names in scope,
  ordered and filtered exactly as a goal lists them. The answer is printed at the end of the
  declaration, when the unknowns are solved (`flush_probe`, `goals.rs:764`). The driver
  wraps it as `Session::context_at_text` / `context_at_project`
  (`crates/driver/src/at.rs:644`, `:663`), and the language server answers the custom
  request `stitchwort/contextAt` on a search thread (`crates/lsp/src/lib.rs:1459-1485`,
  `:4165-4232`). **The VS Code client never sends it** (no `contextAt` in
  `editors/vscode/*.js`), the playground doesn't either, and there is no CLI for it.
  **[checked]**
- **Hover over a selection** shows the type of the smallest expression covering it, from
  types the language server records for every expression on every check
  (`session_for` turns this on, `crates/lsp/src/lib.rs:2597-2601`; printed in
  `flush_navigation`, `nav.rs:725`). No names in scope. **[checked]**
- **`stitchwort search --at FILE:LINE[:COL]`** reads the goal at a `?` and lists what closes
  it (docs/syntax.md, "What closes this `?`"), with `--json`. It has the CLI shape this note
  copies. **[checked]**

### 2.2 What the existing probe answers, form by form

I drove `stitchwort lsp` from a small script (§10) on a 25-line file of SF-style proofs, and
asked `stitchwort/contextAt` at each kind of position. **[ran]**

| Cursor on | Answer today | What a reader wants |
|---|---|---|
| `rfl` in `rewrite h in rfl` | `⊢ m + m = m + m`, with `n m h` | the same: the goal after the rewrite |
| the rule `h` in `rewrite h in rfl` | `n = m`, "inferred" (the rule's own type) | goal before (`n + n = m + m`), the rule, goal after |
| the second rule of `rewrite Nat.mulZero p, Nat.mulZero q in rfl` | `q * 0 = 0` (the rule's type) | before `0 + q * 0 = 0` [inferred], after `0 = 0` |
| an arm's pattern, `\| Succ k` | **nothing** (patterns aren't expressions) | the arm's goal, and what the arm adds (`k: Nat`) |
| the arm's proof `Eq.cong Succ (…)` | `⊢ Succ k = Succ k` with `k: Nat` | the same |
| `calc a`, or a step line `_ = b` | the whole chain's goal `a < 5` | the line's statement, `a = b` |
| the proof of a `calc` step, `h1` | `⊢ a = b` | the same |
| `omega` | `⊢ a + 1 ≤ b` with `a b h` | the same, plus which facts it used (later) |
| `cases` (AoC 2025 day 8) | `⊢ True = False` | the same, plus the cases it split into and how each closed |
| a lambda's binder `pq =>` | `⊢ p ∧ q → q ∧ p` (the lambda's own goal) | the goal after introducing `pq` |
| after `let left := pq.left` | `left: p := pq.left` listed, `⊢ q ∧ p` | the same |
| `n` in a program expression | `Nat`, "inferred" | the same, labelled as a type, not a goal |

So the "in the middle of an expression" answers are already right; what is missing is
everything **between** expressions: the steps of a `rewrite` chain, an arm's entry, a `calc`
line, a binder.

### 2.3 Three more gaps the probe has

- **A failed expression has no answer.** `check` offers its expression to the probe only
  after checking it succeeded (`cx.e.note_expr(…)` follows the `?` at
  `crates/elab/src/check.rs:4202-4210`) **[checked]**. With the cursor on the step that
  fails, the probe falls back to the smallest enclosing expression that succeeded, if any.
  The error message gives the expected type, but not the context.
- **Nothing after an error in the same branch.** Checking stops at the first error of a
  branch (lsp-goal-holes.md §4 item 8, still true), so every point after it has no answer.
  This is when a reader fixing a proof most wants one.
- **It's slow.** Each request builds or rewinds a session and re-checks the file's whole
  namespace (`probe_project`, `at.rs:767-802`). Measured with the release CLI's language
  server [ran]:

  | File | Per request |
  |---|---|
  | 25-line file on its own (`steps.sw`, §10) | 330–780 ms (the library's load, not the file) |
  | AoC 2025 day 8 `Proofs/Part2.sw` (namespace: 506 ms to elaborate uncached) | 1390–1640 ms warm; 19.3 s for the first |
  | AoC 2025 day 8 `Proofs/Part1.sw` | 1390–1420 ms |

  A panel that follows the cursor at that speed lags a second behind every move. Lean's
  infoview answers from information it recorded during the check, so moving the cursor
  costs nothing [cited, §1].

## 3. What "the goal at a point" means

Stitchwort proofs are terms, not tactic scripts: there is no "state between line 3 and
line 4". But every proof form has **places where the goal changes**, and those are the
steps a reader wants to watch. The answer at a point has three parts:

1. **The goal**: what the smallest expression containing the point must be: the type it
   is checked against (for a proof, the proposition; that's the goal), else the type
   found for it. As today's probe answers.
2. **The context**: the names in scope there, as a `?` there would list them (a `let` with
   its value, a shadowed name with `✝`, a hypothesis replaced by a later one left out),
   so that "what `?` would say here" and "what the panel says here" never differ.
3. **The step**, when the point is on one: the goal **before** it, what it **adds or
   changes** in the context, and the goal **after** it. Steps are listed below.

Goals are printed by today's printer, folded as goal-as-written.md and the bounded
read-back plan arrange; nothing here changes how a goal reads.

### 3.1 Form by form

| Form | Where the cursor is | Step shown |
|---|---|---|
| **Argument position** `f a ?b` | on the argument | none: the goal is the argument's expected type (`Nat.leq b c = True`), as today |
| **`match e with`** | on `match` or the scrutinee | before: the goal; the step lists the arms, each with its pattern |
| **an arm** `\| Succ k =>` | on the pattern or `=>` | before: the `match`'s goal; adds: the pattern's variables and, for `match h: e`, `h: e = Succ k`; after: the arm's goal (`Succ k * 1 = Succ k`, refined) |
| | in the arm's body | the body's goal, as today |
| **`rewrite r1, r2 in t`** | on `rewrite` | before: the goal; after: the goal `t` gets |
| | on rule *i* | before: the goal after rules 1..*i-1*; the rule as used (its equation with its unknowns solved: `Nat.mulZero q: q * 0 = 0`, and its direction); after: the goal after rule *i* |
| | on `in` or in `t` | `t`'s goal (after every rule), as today |
| **`rewrite r at h in t`** | on a rule | before and after are `h`'s type; the goal is unchanged and shown once |
| **`calc e0`** | on `calc` | the chain's goal, and the relation the chain proves so far |
| | on a line `_ R e` | the line's statement, `e(i-1) R e`, and what the chain has proved before it, `e0 R' e(i-1)` (Isar's `calculation`); for a line with no proof, "closed by computation" |
| | in a line's proof | the line's statement, as today |
| **`omega`**, **`ring`** | on the word | the goal; with `omega [f1, f2]`, the listed facts' statements (stage 5: which hypotheses it used) |
| **`cases`**, **`cases in t`** | on the word | the goal it was given, and the cases it split into: each case's assumptions (`b = True`, `xs = []`) and what closed it (computation, a contradiction, hypothesis `h`, `omega`, `t`) (stage 5) |
| **`rfl`** | on the word | the goal; when it failed, the two sides as computed |
| **an `auto` argument** at a call (`xs.get i` finding `i < xs.length`) | on the call's head | the call's type as today, plus the proposition each `auto` argument proved and how (later; hover already lists defaults the call used) |
| **`let x := v`** / **`let h: P := p`** | on `let` or the name | adds: `x := v` (or `h: P`); after: the body's goal. In `p`, `P` is the goal |
| **a lambda** `x =>` | on a parameter | before: the function type (`(x: A) → B`); adds: `x: A`; after: `B` |
| **`if h: c then … else …`** | on `then` / `else` | adds: `h: c` (or `h: ¬c`); after: that branch's goal |

**In a program** (the expected type isn't a proposition), the same three parts apply, but
the "goal" is a type: shown as **expected `T`** (and **has type `U`** when the expression's
own type differs, or when there is no expected type). Programs have the same steps (arms,
`let`, lambdas), and `match` arms in particular benefit: the arm's refined expected type is
what dependent code needs (D-c).

**A point with no expression**: in a signature, the answer is the declaration's statement
(the goal of its body) with its parameters as the context; in a comment, a blank line or
between declarations, nothing; inside a declaration that doesn't parse, the last answer
kept for it (as goals are kept today, lsp-goal-holes.md §8.2), marked as stale.

**Where the cursor sits between two expressions** (on a space, at a line's end), the point
belongs to the expression just before it on the same line, else the one after (coq-lsp's
rule for blank positions); a line given without a column (CLI) means its first non-blank
character. On the **head of a call** (`f` in `f a b`) the goal is the whole call's, as in
Lean's `termGoalAt?`, since the head alone has a function type nobody asked about (its
type stays in the hover) [cited, §1].

### 3.2 Steps in reading order

The steps of a declaration in source order are its **proof movie**: the declaration's
statement, then each step's before, change and after. For `addZeroLeft` (§10's file):

```
addZeroLeft (n: Nat): 0 + n = n
  8:3  match n with                         ⊢ 0 + n = n
  9:7    | Zero =>                          ⊢ 0 = 0
 10:7    | Succ k =>        + k: Nat         ⊢ Succ k = Succ k
```

(Sketch: the goals are what the probe printed for these arms' bodies [ran]; `0 + Succ k`
prints as `Succ k` because std's `+` computes, SW-2707 §6 item 3.) Only the steps are
listed, not every expression: a reader moving from step to step sees the goal change
where it changes. Every expression still has its answer for the cursor.

## 4. How it works

### 4.1 One declaration's points, recorded on request

The probe today records **one** position. Instead, a request names a position, and the
probe records **every point of the declaration containing it**:

- **Expressions**: each expression's span, its expected or found type, and a reference to
  its **scope** (below). Recorded on *entry* to `check` (the expected type is known before
  checking), and on exit from `infer`; so a failing expression has its goal.
- **Scopes**: the context changes only at binders (a lambda, `let`, an arm, `rewrite … at
  h`, `if h:`), so each binder starts a scope with its entries; an expression points at its
  scope. Within an arm, the hypotheses of outer scopes are re-printed once for the arm,
  since a `match` refines their types (the arm's values are evaluated with the constructor
  put in, lsp-goal-holes.md §3.3).
- **Steps**: the places in §3.1, each with before, change and after:
  - `rewrite`: the loop in `rewrite_goal` already holds the goal before each rule and
    the goal after it (`goal` and `step.goal`, `crates/elab/src/rewrite.rs:296-318`); `rewrite
    … at h` likewise in `rewrite_at` (`:158`). The rule's instantiated equation is the
    `Equation` from `elaborate_rule` (`:480`) after the search solved its unknowns.
    **[checked]**
  - `calc`: `check_step` has each line's statement `prop` (`crates/elab/src/calc.rs:188-201`);
    a line without a proof goes through `by_computation` (`:255`) with the same `prop`.
    **[checked]**
  - arms: the arm's goal is what its body is checked against, at the leaf of the case tree
    where the right side is checked (`check(cx, rhs, goal)`, `crates/elab/src/lib.rs:4563-4586`,
    which has the arm's `span` and its aliases) **[checked]**; the step is noted there, with
    the `match`'s goal as before. One arm can be reached at several leaves (a catch-all
    arm after a split on two columns: `leaf_log.record(*span, alternatives)`, `:4562`), each
    with its own goal; the step then lists one goal per leaf, labelled by what the leaf
    knows (`n = Zero`, `n = Succ k`) [inferred from the leaf log; stage 3 confirms].
  - lambdas, `let`, `if h:`: noted at the binder with the function type (or the `let`'s
    goal) as before and the body's goal as after.
  - `cases`: a trace of `node` (`crates/elab/src/cases.rs:326-420`): each node's goal, the
    atom split on, and which closer closed it; today only counts of closers are kept
    (`run.closed`). Stage 5.
- **Printing** happens at the end of the declaration, when its unknowns are solved, as
  `flush_probe` does now, with the goal printer (`pretty::value_for_goal`) and the goal's
  context printer, so the panel, a `?` and `search --at` print alike. A step from an attempt
  that was undone (a dot call tried two ways, a lifted `match`) is dropped with it, as goals
  are (`undo::Snapshot`), and a span recorded twice keeps the last.

Nothing recorded changes what is checked: the recorder only reads values the elaborator
already has. The one exception is printing, which evaluates; it runs under its own budget,
as `flush_navigation`'s does (`nav.rs:733-741`), so a check gives the same result with or
without a probe.

### 4.2 Cost

A declaration's points cost memory for one declaration only, freed when the next request
comes for another. The largest std file, `std/List/Lemmas.sw`, is 3,578 lines, about
54,000 tokens and 618 declarations, elaborated in 400 ms [ran: `STITCHWORT_TIMINGS=1`, a
file that imports `Std (List)`, `--no-cache`]; so a declaration averages about 90 tokens,
and the largest proofs a few hundred expressions. Printing one goal is a fraction of a
millisecond [inferred: the language server already prints the type of every expression of
every file on every check, `flush_navigation`, without anyone noticing a cost]; a few
hundred types and a few dozen scopes is a few ms per declaration [inferred].

**Recording every point of every declaration on every check** (Lean's way) would cost, for
`List/Lemmas.sw`, around 30,000 expressions' types (printed already, for hover) plus a
context per scope: roughly 1,500 arms and lambdas (`=>` appears 1,491 times) times about 5
names, so 7,500 more printed hypotheses per check of that file [inferred], on every
keystroke, for answers nobody asked for. §6 compares.

**Time per request.** The answer needs the declaration checked with the probe on. Three
levels, each a stage:

| How | Cost per cursor move | Cost per edit |
|---|---|---|
| today: re-check the namespace per request | 0.3–1.6 s [ran, §2.3] | same |
| keep the declaration's points, keyed by the document's version and the declaration | ~0 (answered from the table) | one namespace check, on the first request after the edit |
| also check only that declaration: the namespace's earlier declarations from the live session, its later ones not at all | ~0 | one declaration's check: tens of ms for most, 330 ms for the slowest AoC theorem (lsp-goal-holes.md §4.1) |

The third needs the live session to keep a namespace's state up to a declaration, which
is the language server's "level 2" (language-server.md §4.2, not built). The first two
stages don't wait for it; a cheaper interim is to skip the bodies of the namespace's other
theorems (a probe never needs them: they are used by their types), which `check --only`
already does for the CLI [checked: `check --help`], though on day 8 that checked 38 of 68
theorems because the target needs them [ran], so its gain varies.

### 4.3 The check cache

The cache stores namespaces, not probes: a probe always checks the file's own namespace
afresh (as `search --at` and today's `contextAt` do, `probe_project`), and loads the
others from the cache. No cache change, and nothing about probes is written to it
[checked: the probe lives in `Goals`, which the cache doesn't save]. A namespace with an
error is never cached anyway, so probing a broken file is no different.

### 4.4 Goals after an error (stage 6)

To show goals after a failed step, the probe run (only the probe run, never a normal check)
recovers from an error inside a branch the way a `?` does: the failed expression becomes an
unfinished hole of its expected type, its error is kept, and checking carries on. The
mechanism exists: `?` is "a fresh frozen metavariable … checking carries on"
(`goals.rs:1-7`). Since a probe's results are only shown, never admitted, recovery can't
make a wrong proof pass. Lean elaborates past errors the same way, putting `sorry` in place
[cited, §1]. Its risk: a check that carries on past an error may print goals that read
oddly (an unknown left by the failure); those are marked "after an error at L:C".

## 5. What the user sees: editor and CLI

### 5.1 The Goals panel

- **Follows the cursor everywhere.** On a `?`, the hole's goal (today's `goalAt`, instant).
  Elsewhere, the answer of §3 (`contextAt`, extended). Headed with where it is: "in
  `addZeroLeft`, arm `Succ k`" / "rule 2 of 2 of `rewrite`" / "line 2 of `calc`".
- **A step shows three blocks**: the goal before, the change (`+ k: Nat`, `~ h: b = True` for
  a hypothesis rewritten), the goal after, with the part of the goal that changed
  highlighted, as Rocq's `Set Diffs` and Lean's infoview diffs do [cited, §1].
- **In a program**: `expected T` (and `has type U` if it differs) instead of `⊢`.
- **Stale answers**: while a declaration doesn't parse, its last answers are kept and the
  panel dims them.
- **Opens** as today, by "Stitchwort: Show Goals" or automatically for a file with a `?`
  (`stitchwort.goals.openAutomatically`).

### 5.2 Stepping

Two commands, **Stitchwort: Next Proof Step** and **Previous Proof Step** (suggested keys
Alt+Down and Alt+Up in `.sw` files), move the cursor to the next or previous step of §3.2
in the declaration, and the panel follows: the closest thing in a term language to Proof
General's "next" (C-c C-n) and CoqIDE's arrows [cited, §1], without a locked region,
since nothing has to be re-run to move. They read the step list from a request
`stitchwort/steps {textDocument, position}` answering the steps' ranges and kinds.

### 5.3 Hover

Hover keeps showing what it shows today (a name's type and doc, a selection's type, a `?`'s
goal). On a **step position** only (an arm's pattern, a rewrite rule, a `calc` line's `_`,
`omega`, `cases`, `rfl`), it adds the step: for a rewrite rule, the rule's type as today
and below it "goal before / after". Hover is where a reader without the panel open looks,
and these positions have little or nothing in their hover today (a pattern has none) (D-a).

### 5.4 The CLI, for agents and scripts

```
stitchwort goal --at FILE:LINE[:COL] [--steps] [--json] [--project DIR] [--full-goals]
```

- **`--at FILE:LINE:COL`**: the answer at that point; `FILE:LINE` alone, at the line's
  first non-blank character. A project's file is read in its project (as `search --at`:
  the project found from the file's folder up, the other namespaces through the check cache).
- **`--steps`**: every step of the declaration containing the point, in source order, each
  with before, change and after: the proof movie of §3.2.
- **Exit status**: 0 with an answer; 2 when there is none there (a comment, between
  declarations, a declaration that doesn't parse); errors in the file are printed after the
  answer and don't change the status, since a goal in a broken proof is the useful case.

Text output (a sketch; the layout follows `?` goals and `search --at`):

```
$ stitchwort goal --at Basics.sw:574:67
in `multN0M0`, rule 2 of 2 of `rewrite` (Basics.sw:574:67)
  p: Nat
  q: Nat
  before ⊢ 0 + q * 0 = 0
  rule     Nat.mulZero q: q * 0 = 0
  after  ⊢ 0 = 0
```

`--json` gives `version` (1), `at` (`file`, `line`, `column`), `declaration`, `range`,
`kind` (`proof` or `program`), `context` (each `name`, `type`, `value?`), `goal` (`target`,
`checked`: whether it is the expected type or a type found), `step` (`form`: `arm`, `rewriteRule`,
`calcLine`, `lambda`, `let`, `if`, `omega`, `cases`, `rfl`; `index`, `of`; `before`; `adds`
and `changes` as context entries; `after`; `rule` for a rewrite), `steps` with `--steps` (a
list of `{range, step}`), `stale`, `afterError` (the error's place, when the goal comes from
recovery, §4.4) and `diagnostics` (the declaration's errors). Line and column are 1-based,
as `search --at` writes them.

An agent's use: before editing a proof, `stitchwort goal --steps --at F:L --json` gives
every intermediate goal in one call, the term-language equivalent of the per-tactic
states LeanDojo and Pantograph extract from Lean [cited, §1]; while fixing, `--at` on the
failing line gives the goal and context the error lacks.

### 5.5 The playground

Later (stage 7): the probe compiles for wasm already (editor-and-playground-roadmap.md §3,
"As built"), so the playground's worker can answer the same request for its Goals section.
Not in this note's first stages.

## 6. Designs compared

**A. On request, one declaration at a time, kept until the next edit** (recommended). The
probe of §4.1 records every point of the declaration under the cursor; the server keeps them
per document version. *Costs*: the first request after an edit waits for a check (a
namespace's at first, a declaration's after the level-2 work); a little memory for one
declaration. *Rules out*: nothing; B can still come later if the first-request wait shows.

**B. Record every point of every declaration on every check** (Lean's InfoTree). *Gains*:
no wait at all, even after an edit; a cursor anywhere answers at once. *Costs*: about
7,500 printed hypotheses more per check of `List/Lemmas.sw`, every keystroke, almost all
thrown away; the context has to be kept per scope (and printed, or kept as values with the
unknowns' solutions, which today vanish at the end of each declaration). Lean records its
InfoTree during every elaboration, behind a switch (`InfoState.enabled`), and keeps
metavariable contexts per tactic node [cited, §1]; I found no published measure of what
that costs. For us it would be a cost added to every check (the CLI's too, unless it's
off there, which is a second code path).

**C. Probe one point per request, as today, made faster.** Smallest change, but every
cursor move is a check, and a step list (`--steps`, stepping commands) would need one check
per step. Rejected: §3.2's movie is the most useful thing for a reader and for agents.

**D. Text only: put `?` everywhere.** A reader could today replace each step with `?` to see
its goal. That's how SF readers are told to work in the port (SW-2707 §6 item 4); it edits
the proof and loses the rest of it. Not a design, the status quo.

A is B's answers with C's cost profile: the cost is paid only where someone looks.

## 7. Stages

Each stage is useful alone. Estimates as in docs/workflow.md (lanes of 30–90 min). Each
stage that changes something user-visible updates `docs/syntax.md` and the guide
(`docs/guide/`), per CLAUDE.md "Always".

| # | Stage | Model | Est. | Useful alone because | Targeted tests |
|---|---|---|---|---|---|
| 1 | **Panel follows the cursor.** The VS Code panel asks `stitchwort/goalAt`, and when that is null, `stitchwort/contextAt`; the answer gains `kind` (`proof`/`program`, from whether the type is a proposition) and the panel shows `⊢` or `expected` (D-c). Debounce raised for `contextAt` (300 ms) and superseded answers dropped (as now). Guide and README: the panel works anywhere | Sonnet | 45 min | goals inside every arm body, `calc` proof, `omega`, `cases`, after every `let`, today, with nothing new in the elaborator | `editors/vscode/test/client.test.js` (`goalHtml` for a context answer, both kinds); `crates/cli/tests/server/lsp.rs` `context_at_*` with `kind` (`task test:one -- context_at`) |
| 2 | **`stitchwort goal --at`** (text and `--json`), over `context_at_text`/`context_at_project`; exit 0/2; docs/syntax.md section beside "What closes this `?`" | Sonnet | 60 min | agents can ask for the goal and context anywhere, without editing the file | a new `crates/cli/tests/` case for a file on its own and a project's file (the `search --at` tests are the model); `task test:one -- goal_at` |
| 3 | **Steps and whole-declaration recording** (§4.1): the probe records every point of the declaration; recording on entry to `check`; steps for arms (pattern positions), `rewrite` rules (before, rule, after, also `at h`), `calc` lines, lambdas, `let`, `if h:`; `contextAt` and `goal --at` gain `step`; the panel shows before/change/after with the change highlighted | Opus | 90 min | the SF gap closes: every rule of a chain, every arm's entry, every `calc` line shows its goal | new `examples/goals/`-style probe cases in `crates/driver/tests/elaboration/at.rs` (one per form of §3.1); `task test:one -- at::` |
| 4 | **Stepping and speed**: `--steps` in the CLI; `stitchwort/steps`; Next/Previous Proof Step commands; the server keeps a declaration's points per document version (cursor moves answer from the table); hover adds the step at step positions (D-a) | Sonnet | 90 min | the proof movie for agents and readers; the panel stops lagging on cursor moves | `lsp.rs` tests: two requests in one declaration check once (count checks), stale after edit; client tests for the commands; CLI `--steps` snapshot |
| 5 | **`cases` and `omega` explained**: the split tree with each case's assumptions and closer; `omega`'s listed facts (and, if cheap, the hypotheses its certificate used) | Sonnet | 60 min | `cases` stops being a black box, the commonest complaint about automation in a teaching text | `at.rs` cases for `cases` with two splits and `omega [f]`; the `cases` examples' snapshots unchanged (`task test:lane AREA=goals`) |
| 6 | **Goals after an error** (§4.4): in a probe run only, an error inside a branch becomes an unfinished hole and checking carries on; answers after it carry `afterError` | Opus | 90 min | fixing a proof: the goals of the steps after a broken one | `at.rs`: a chain whose first rule fails still answers at its `in` body; the reject examples' snapshots unchanged (normal checks don't recover) |
| 7 | **Later, not scheduled**: probe only the declaration (needs level-2 re-checking, language-server.md stage 5); the playground's Goals section from the worker; a static proof movie in `stitchwort doc`'s HTML for the SF port (Alectryon's idea, §1) | — | — | — | — |

Order: 1 and 2 at once (no shared files beyond `at.rs`'s answer struct, which 1 extends
with a field and 2 only reads); then 3; then 4, 5 and 6 at once (5 touches `cases.rs` and
`omega.rs`, 6 `check.rs`'s error path, 4 the server and client). About 7.5 hours of lanes
in all.

No stage changes a term, a hash or a proof result, so `hash_stability` and the hash
snapshots aren't needed; stage 3 and 6 lanes check that the `goals/` and `reject/` example
snapshots don't move (they shouldn't: probes are off in normal checks).

**Tickets this absorbs or touches**: lsp-goal-holes.md §8.4 PROVISIONAL 1 (the probe at any
expression: stage 1 uses it, 3 completes it); SW-2707 §11 item 3 (this ticket). The
`goalAt` request stays for the published `?` goals.

## 8. Calls made

Implementation choices I made; each is reversible.

- **One request**: `stitchwort/contextAt` is extended (`kind`, `step`, `stale`, `afterError`),
  not replaced; `goalAt` stays as the instant answer at a published `?`. The panel asks
  `goalAt` first.
- **Record on entry to `check`** (expected type known) as well as on exit from `infer`, so a
  failing expression has its goal.
- **A step's "after" is the goal of what follows**, not a re-derived state: for an arm, the
  body's expected type; for a rule, the goal the next rule (or `t`) gets. So it is exactly
  what the elaborator used.
- **Before/after highlighting** in the panel ships on, with a panel toggle "show steps"
  (on by default) so a reader can see only the goal. Reversible, client-only.
- **Program points** answer too (D-c's form), since arms in dependent programs have the same
  need.
- **Between expressions** the point belongs to the expression before it on the line, else
  after; a CLI line without a column is its first non-blank character.
- **Signature positions** answer with the declaration's statement as the goal.
- **The steps list** includes only steps (§3.1), not every expression.
- **The JSON's lines and columns are 1-based**, as `search --at` (LSP stays 0-based).
- **Caching** is per (document version, declaration name); an edit anywhere in the file
  drops the file's tables (the namespace may have changed under the declaration).
- **Stage 3 is Opus**: it reads values inside `rewrite`, `match` and `calc` elaboration, and a
  mistake (printing a value at the wrong level, a step from an undone attempt) is silent.

## 9. Decisions for Matt

Placeholders; the orchestrator numbers them.

- **D-a: Where the goal at any point is shown in the editor.** The Goals panel follows the
  cursor everywhere (not only at `?`), with a step's goal before and after; and hover adds a
  step's goals only at step positions (an arm's pattern, a rewrite rule, a `calc` line,
  `omega`, `cases`, `rfl`), never on ordinary names or expressions. [rec: **yes**. The panel
  is where Lean and Rocq readers look, and SF's "step through" is the panel moving; hover
  everywhere would bury a name's type and doc under goals, but at step positions hover has
  little to show today, and it serves readers without the panel open.]
- **D-b: The CLI's shape.** `stitchwort goal --at FILE:LINE[:COL]`, with `--steps` for every
  step of the declaration and `--json`; exit 0 with an answer, 2 with none. [rec: **yes**.
  `goal` is the word `?` and the panel already use, and `--at FILE:LINE[:COL]` is `search
  --at`'s form, so an agent that knows one knows the other. Alternatives: `stitchwort at`
  (shorter, vaguer), `stitchwort state` (Lean's and Rocq's word for a tactic state, which
  Stitchwort doesn't have).]
- **D-c: What's shown at a point in a program.** `expected T`, and `has type U` when the
  expression's own type differs or there is no expected type, instead of `⊢ T`; the context
  as for a proof. [rec: **yes**. `⊢` reads as "prove this", wrong for `Nat`; Lean's infoview
  says "expected type" in term mode.]

Not asked now: whether the SF port's HTML (SW-2707 §9) should become a static proof movie
(stage 7); it waits for the HTML rendering itself.

## 10. Risks, what this note didn't do, sources

**Risks.**

- **First-request wait** after an edit stays at a namespace check (up to ~1.5 s in the
  heaviest AoC proof files) until level-2 re-checking; the panel shows the stale answer,
  dimmed, meanwhile.
- **Goals printed computed** where the source is folded (`0 + Succ k` as `Succ k`): the
  printer's existing behaviour (D639, goal-printing-gaps.md). Stepping will show more goals,
  so more of these; they are the printer's tickets, not this note's.
- **Undone attempts**: a step recorded during an attempt the elaborator later undoes must be
  dropped. Goals already follow this rule; steps must join it (stage 3's tests include a dot
  call tried two ways).
- **Recovery after errors** (stage 6) may show goals with unknowns in them; marked as such.

**What this note didn't do.** I didn't confirm how an arm reached at several leaves is
logged (stage 3 will); I didn't measure printing cost per goal directly (inferred from
`flush_navigation`'s unremarked cost); I measured probe latency with my own small LSP client,
not VS Code. Project-file answers were null until my client waited for the first
diagnostics, as the server's own test does (`context_at_in_a_projects_file_reads_the_editors_text`,
`crates/cli/tests/server/lsp.rs:2342`), so a request sent while the first check runs gets
null; the VS Code panel would retry on the diagnostics event [inferred], but a CLI must
not do that, which stage 2 handles by checking first.

**Probes** (scratch, not committed; [ran] 11 Nov 2026, release CLI built 05:18 from `main`):

- `steps.sw`: the 25-line file of §2.2 (SF's `plusIdExample` and `multN0M0`, an
  `addZeroLeft` by `match`, the `calc` example of docs/syntax.md, an `omega`, a lambda with
  a `let`).
- `lspprobe.py`: opens a file in `stitchwort lsp`, waits for its diagnostics, sends
  `stitchwort/contextAt` at given points and prints the answers and their times.
- A copy of `aoc/src` (cold, then warmed by `check Aoc.Year2025.Day08.Proofs`) for the
  project timings.
- `STITCHWORT_TIMINGS=1 stitchwort check --no-cache` on a file importing `Std (List)` (for
  `List/Lemmas.sw`'s 400 ms), and on `Aoc.Year2025.Day08.Proofs` with and without `--only`.

**Sources** (read for §1 on 11 Nov 2026):

- Lean: [vscode-lean4 manual](https://raw.githubusercontent.com/leanprover/vscode-lean4/master/vscode-lean4/manual/manual.md);
  [InfoTree/Types.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/InfoTree/Types.lean);
  [InfoTree/Util.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/InfoTree/Util.lean);
  [FileWorker/RequestHandling.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Server/FileWorker/RequestHandling.lean);
  [Lean.Data.Lsp.Extra](https://lean-lang.org/doc/api/Lean/Data/Lsp/Extra.html);
  [Zulip, "Infoview in term mode"](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Infoview.20in.20term.20mode.html);
  Nawrocki, Ayers, Ebner, "An Extensible User Interface for Lean 4", ITP 2023,
  [doi 10.4230/LIPIcs.ITP.2023.24](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.24);
  [Mathlib calc widget](https://florisvandoorn.com/LeanCourse24/docs/Mathlib/Tactic/Widget/Calc.html);
  [Paperproof: how to build a proof tree](https://antonkov.github.io/posts/How-to-build-a-proof-tree).
- Rocq: [coq-lsp](https://github.com/ejgallego/coq-lsp) and its
  [PROTOCOL.md](https://raw.githubusercontent.com/ejgallego/coq-lsp/main/etc/doc/PROTOCOL.md);
  [VsRocq](https://github.com/rocq-prover/vsrocq);
  [refman, proof mode and Set Diffs](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/proof-mode.html);
  [coq-diffs.el](https://sources.debian.org/src/proofgeneral/4.5-3/coq/coq-diffs.el);
  Pit-Claudel, "Untangling Mechanized Proofs", SLE 2020 ([MIT DSpace](https://dspace.mit.edu/handle/1721.1/158169),
  [blog](https://systemf.epfl.ch/blog/alectryon));
  Gallego Arias, Pin, Jouvelot, jsCoq, UITP 2016 ([arXiv 1701.07125](https://arxiv.org/pdf/1701.07125)).
- Isabelle: [Isabelle/jEdit manual](https://isabelle.in.tum.de/doc/jedit.pdf) §3;
  [Isar reference manual](https://isabelle.in.tum.de/doc/isar-ref.pdf);
  Wenzel, "Asynchronous User Interaction and Tool Integration in Isabelle/PIDE", ITP 2014
  ([pdf](https://www21.in.tum.de/~wenzelm/papers/itp-pide.pdf)).
- Agda: [Emacs mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html),
  [with-abstraction](https://agda.readthedocs.io/en/latest/language/with-abstraction.html),
  [auto](https://agda.readthedocs.io/en/latest/tools/auto.html).
- Idris 2: [types and functions](https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html),
  [interactive editing](https://idris2.readthedocs.io/en/latest/tutorial/interactive.html).
- F\* and Dafny: [F\* book, Meta-F\*](https://fstar-lang.org/tutorial/book/part5/part5_meta.html);
  Jain et al. 2025, [arXiv 2508.02733](https://arxiv.org/html/2508.02733v1);
  [Dafny VS Code](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/VSCodeIDE.md),
  [Dafny user guide](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/UserGuide.md) §13.7.1.
- Liquid Haskell: [proof combinators](https://hackage.haskell.org/package/proof-combinators-0.1.0.0/docs/LiquidHaskell-ProofCombinators.html);
  [arXiv 1610.04641](https://arxiv.org/pdf/1610.04641).
- Research and agents: Bertot, Kahn, Théry, proof by pointing, TACS 1994
  ([dblp](https://dblp.org/rec/conf/tacs/BertotKT94));
  Aitken et al., JSC 1998 ([abstract](https://cs.ox.ac.uk/publications/publication4695-abstract.html));
  [Prooftree](https://www.friedhofsspaziergang-leipzig.de/software/prooftree);
  Ringer et al., QED at Large, 2019 ([arXiv 2003.06458](https://arxiv.org/pdf/2003.06458));
  Shi et al., QED in Context, OOPSLA 2025 ([pdf](https://jwshii.github.io/OOPSLA25.pdf));
  Kambhamettu et al., Explorable Proofs, 2026 ([arXiv 2604.02598](https://arxiv.org/abs/2604.02598));
  Pantograph ([arXiv 2410.16429](https://arxiv.org/html/2410.16429v2));
  [Lean REPL](https://github.com/leanprover-community/repl);
  LeanDojo ([arXiv 2306.15626](https://arxiv.org/abs/2306.15626v2)).
