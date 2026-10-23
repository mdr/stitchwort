# Goal holes in the editor (language server stage 2)

**Status:** accepted 23 October 2026 (SW-31 stage 2): D635–D641 as recommended.
The decisions are in the
[table at the end](#decisions). It builds on
[`language-server.md`](language-server.md) §5.2 and D497 ("a new `?` goal
hole"), and goes into the detail that note left open.

Labels: **[checked]** read in the source (file:line, at `main` `5321ceaa`);
**[run]** I ran it (the release CLI built at 10:00 today, on a copy of
`aoc/` in this worktree); **[cited]** a web source, linked;
**[inferred]** follows from what I read but I didn't test it;
**[unverified]** I looked and couldn't confirm it.

## 1. The short version

- You write `?` where a proof or value is missing. The checker carries on
  past it, and reports, at the hole, the **goal**: what the hole must be,
  and the local names in scope with their types.
- In VS Code this is an **information diagnostic** (blue underline) on the
  `?`, whose message is the goal. Hovering over the `?` shows it, and the
  Problems panel lists every open goal in the project. No change to the VS
  Code client: diagnostics are standard LSP and already flow through.
- The CLI prints the same text, `check` fails while goals are open, and
  the playground shows a "Goals" section in its output.
- Later, its own stage: a Goals panel that follows the cursor, like
  Lean's infoview, through one custom request.

## 2. Where things stand today

- **There is no `?`.** `stitchwort check` on a file with `?` fails at the
  lexer: `[E-PARSE] unexpected character '?'`, and nothing else in the file
  is reported [run]. `?` isn't used anywhere in the syntax [checked:
  no `'?'` in `crates/syntax/src/`].
- **`_` is "work it out for me"**, a fresh metavariable
  (`crates/elab/src/check.rs:660-664` when inferring, `:1436` when
  checking) [checked]. Where nothing determines it, as for a missing
  proof, you get [run]:

  ```
  [E-UNSOLVED] Error: can't work out an implicit argument
   11 │     | Succ k => _
      │                 ╰── the compiler couldn't work out what goes here
      │ Note: supply it explicitly with `f [x := …]`, or add a type annotation
  ```

  No goal and no context; and the wording is about implicit arguments,
  which is wrong for a proof. The message comes from
  `crates/elab/src/lib.rs:818-823` [checked].
- **The pieces a goal needs already exist:**
  - The checker's context `Ctx` holds the local names, their types, and
    for transparent `let`s their values (`check.rs:37-66`: `names`,
    `types`, `lets`) [checked].
  - `check` already notes the *expected type* of every expression it
    checks, for "type of selection" (`check.rs:1400-1409`, `note_expr`)
    [checked]. The printing waits until the end of the declaration, when
    the metavariables are solved, and drops what an undone attempt noted
    (`crates/elab/src/nav.rs:401-433`) [checked]. Goals need the same
    two rules.
  - **Frozen metavariables**: "unification never solves them, so each is
    equal only to itself", used today for lifted `match`es
    (`crates/core/src/globals.rs:233-238`) [checked]. That is exactly
    what a `?` must be: a placeholder nothing can fill in by accident
    (Lean's `?_` "synthetic holes … are never solved by unification"
    [cited: [Lean reference, Holes](https://lean-lang.org/doc/reference/latest/Terms/Holes/)]).
  - **Failed declarations stay usable by their type.** In a file where
    `lemma1` fails and `useIt` uses it, and `broken` fails and
    `useBroken` calls it, only the two failures are reported [run]. The
    module marks the component `Failed` (`crates/elab/src/module.rs:353-370`)
    [checked]. A declaration with an open `?` can take the same path.
  - **Match branches already refine the goal.** `rfl` in the `Succ k`
    branch of `n + 0 = n` reports "`Succ (k + 0)` and `Succ k` aren't
    equal" [run]: inside a branch, the matched variable *is* the
    constructor (`check.rs:39-40`) [checked].
- **The language server** (`crates/cli/src/lsp.rs`, 1336 lines) has hover,
  definition, references, symbols and selection ranges
  (`lsp.rs:75-91`) [checked]. It maps only two severities, error and
  warning (`lsp.rs:1302-1303`; `Severity` has just those two,
  `crates/syntax/src/diagnostic.rs:4-7`) [checked]. Requests answer from
  the last published state, not a fresh check (`language-server.md`,
  "As built", last list) [checked].

## 3. What the user sees

### 3.1 What other systems do

| System | How a goal is shown in VS Code | When it updates |
|---|---|---|
| **Lean 4** | The **infoview**, a side panel. "If the text cursor is positioned in a tactic proof, the InfoView will display the current proof state with all currently open proof goals at the position of the cursor"; in a term, "the current expected type at the position of the cursor" [cited: [vscode-lean4 manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md)]. Hover shows diagnostics and identifier types, not goals [cited: same]. The panel is fed by Lean-only requests `$/lean/plainGoal` (goals at a position, Markdown plus a list of strings) and `$/lean/plainTermGoal` (expected type at a position) [cited: [Lean.Data.Lsp.Extra](https://lean-lang.org/doc/api/Lean/Data/Lsp/Extra.html)]. | As you type and as the cursor moves (debounced) [cited: manual]. |
| **Agda** (agda-mode-vscode) | Emacs-style commands: load with `C-c C-l`, then "goal type" `C-c C-t`, "context" `C-c C-e`, both `C-c C-,` [cited: [agda-mode-vscode](https://github.com/banacorn/agda-mode-vscode)]. The output goes to a panel below the editor [unverified: the README doesn't say where]. Can use the Agda Language Server [cited: same]. | On load, not as you type [cited: same: "load it by typing C-c C-l"]. |
| **Idris 2** (idris2-lsp) | Holes are acted on through **code actions**: `RefineHole`, `ExprSearch`, `CaseSplit`, `MakeLemma` and others [cited: [idris2-lsp README](https://github.com/idris-community/idris2-lsp)]. Whether hover over a hole shows its type I couldn't confirm [unverified]. | On save (`language-server.md` §2) [checked there]. |
| **Coq/Rocq** (VsCoq 2, now VsRocq) | A **goal view** panel, "customisable", accordion or tabs [cited: [VsCoq 2 release](https://discourse.rocq-prover.org/t/vscoq-2-release/2043), [repo](https://github.com/coq-community/vscoq)]. | "Continuous" mode updates as you edit; the default is step by step [cited: same]. |
| **F\*** (fstar-vscode-assistant) | **Hover**: "hovering over a tactic line shows the last proof state dumped at that line"; no goals panel [cited: [fstar-vscode-assistant](https://github.com/FStarLang/fstar-vscode-assistant)]. | Light checking as you type, full checking on request [cited: same]. |
| **Dafny** | No holes. Verification results as **diagnostics** and **gutter icons**; hover over an error shows expanded information [cited: [Dafny 4 announcement](https://dafny.org/blog/2023/03/03/dafny-4-released/), [Dafny VS Code guide](https://personal.cis.strath.ac.uk/jan.de-muijnck-hughes/temp-dafny/DafnyRef/VSCodeIDE.html)]. | As you type [cited: guide]. |
| **Liquid Haskell / GHC** | Liquid Haskell runs as a GHC plugin so that existing IDE tooling shows its errors [cited: [Well-Typed](https://well-typed.com/blog/2020/08/implementing-a-ghc-plugin-for-liquid-haskell)]. GHC's typed hole `_` is reported as a **diagnostic**: "Found hole" with the expected type, "Relevant bindings include" (the context) and "Valid hole fits" [cited: [GHC guide, typed holes](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/typed_holes.html)]. | As GHC diagnostics do. |

Two families: **a panel that follows the cursor** (Lean, Coq) and **the
goal as a message at the hole** (GHC, and Agda's per-hole commands). A
panel is the richer experience but is VS Code-only custom UI. A message
works in every editor, the CLI and the playground.

### 3.2 The options for Stitchwort

| Option | Gives | Client work | Works outside VS Code |
|---|---|---|---|
| A. Information diagnostic per `?`, goal in the message | Blue underline; hover shows it; Problems panel lists every open goal | None | Yes (any LSP editor, CLI, playground) |
| B. Hover on `?` (a hover answer) | Formatted goal on hover | None | Yes |
| C. Goals panel (webview) following the cursor | Lean-style; goal at any position | A webview, ~150 lines, plus a custom request [inferred] | No |
| D. Inlay hint after `?` | Goal inline in the text | None | Partly; long goals don't fit on a line |
| E. Code lens above the declaration | "2 goals open" | None | Partly |

**A and B together duplicate.** VS Code puts the diagnostic's message and
the hover provider's answer in the same hover popup [inferred from
VS Code's behaviour with errors today; not tested with a goal]. So pick
one at the hole. A wins: it also gives the Problems list and the CLI and
playground text, from one piece of data.

**Recommendation (D635): A for stage 2**, the full goal in the message,
code `GOAL`, severity Information. The hover provider returns nothing
extra at a `?`. C is the later, richer step (§3.4), as its own stage. D
and E: not planned (goals are often several lines).

What it looks like in the CLI (and, without the box drawing, as the
diagnostic message in VS Code):

```
[GOAL] Goal: theorem addZero, branch `Succ k`
    ╭─[ h.sw:11:17 ]
 11 │     | Succ k => ?
    │                 ┬
    │                 ╰── k: Nat
    │                     ⊢ Succ (k + 0) = Succ k
────╯
```

The goal line uses `⊢` as Lean, Coq and the language-server note do
(Agda prints `Goal: T` [unverified for agda-mode-vscode]). Matt prefers Scala/TS
conventions; the alternative is `goal: Succ (k + 0) = Succ k` (D637).

### 3.3 What's in the context

- Every local name in scope, outermost first, with its type: parameters
  (implicit ones too, which Lean also lists), pattern variables, `let`s,
  hypotheses from `match h: … with`.
- **`let`-bound names with their values**: `total: Nat := sum xs`, as Lean
  shows them (D638). `Ctx.lets` has them (`check.rs:59-62`) [checked].
- Names nobody can write (compiler-generated, shadowed) shown as Lean
  does, with a dagger: `n✝: Nat` [inferred: what our printer does for
  shadowed names needs checking].
- **In a `match` branch, the refined types**: the scrutinee replaced by the
  pattern in the goal and in the hypotheses' types. That's free, because
  types in `Ctx` are values evaluated in the branch's environment
  [checked: `check.rs:39-40`; run: the `rfl` message above].
- **Computed, not as written.** The refined goal prints as `Succ (k + 0)
  = Succ k`, not `Succ k + 0 = Succ k`, because values are evaluated
  before printing. `rfl` messages already look like this [run]. Printing
  "as written, with the pattern put in" needs a substituting printer that
  doesn't exist; not for stage 2 (D639).
- Long goals: today's message printer cuts terms at 240 characters
  (`crates/core/src/pretty.rs:49`) [checked]. Goals get a much larger
  limit; a goal is the one place the whole term matters.

### 3.4 "Goal at the cursor" for term proofs

In Lean's tactic proofs the goal changes from line to line, so "the goal
at the cursor" means the proof state between tactics. Stitchwort proofs
are **terms** (an expression that has the theorem's type), so there is no
state between lines. The useful meaning is Lean's *term* mode one: **the
type the expression under the cursor must have, and the names in scope
there**. For example, with the cursor on the second argument of
`Nat.leqTrans a b c h1 ?`, it's "`Nat.leq b c = True`, with `a b c h1`".
Inside a `calc`, it would be the step's statement; after a `rewrite`, the
rewritten goal.

Half of this exists: hover over a selection already shows the expected
type of the smallest expression covering it (`check.rs:1406`, `lsp.rs:568-603`)
[checked]. Missing is the context there, which is too much to record at
every expression; it has to be computed on request by re-checking the
declaration with a "probe" position, the way the completion design
re-checks with a dummy name (`language-server.md` §5.3). That and the
panel are a separate stage after this one (D640).

## 4. What the elaborator must provide

1. **Syntax.** A `?` token and `Expr::Goal(Span)` next to `Expr::Hole`
   (`crates/syntax/src/ast.rs:56-57`, parser at `parser.rs:2692-2695`)
   [checked]. Allowed anywhere an expression goes (D497).
2. **Checking `?` against a type `T`.** Make a fresh **frozen**
   metavariable, record a goal `{span, expected T, the context's names,
   types and lets, the declaration's name, the branch}`, and return the
   metavariable as the term. Carry on: unlike an error, a `?` doesn't stop
   the declaration, so every hole in it is reported.
3. **`?` where the type isn't known** (inferring positions, such as the
   function in an application). The expected type is a fresh metavariable;
   if it's still unsolved when printed, say "the type here isn't known
   yet" instead of printing a metavariable name (`language-server.md`
   §8, Risks, asked for this) [checked there].
4. **Printing.** At the end of the declaration, while metavariable
   solutions are known, as `flush_navigation` does for types
   (`nav.rs:419-433`) [checked], with the existing
   `pretty::value_for_message` and the context's names. Unlike navigation,
   goals are recorded always, not only when the index is wanted: the CLI
   needs them.
5. **Undone attempts.** The elaborator sometimes checks an expression,
   undoes it and tries another way (dot-call candidates, a `match` lifted
   into a helper) (`nav.rs:11-13`, `401-417`) [checked]. Goals noted in an
   undone attempt are dropped with it, and a span checked twice keeps the
   last; the same two rules as the navigation recorder.
6. **The declaration afterwards.** A declaration with an open `?` is
   **unfinished**: it isn't sent to the kernel, and is marked like a
   failed one, but with no error (D636). Later declarations can use it by
   its type, as they can use a failed one today [run: `useIt` above]:
   you can state a lemma, leave its proof as `?`, and use it in the main
   theorem, Lean's `sorry` workflow. Running code that reaches it fails
   as calling a failed definition does. The module's "did the component
   fail" test (`module.rs:353-357`, errors only) gains "or has open
   goals" [checked].
7. **`check` exits non-zero** with "2 goals open", so CI never passes a
   project with holes (D636).
8. **Errors and holes together.** Holes in other declarations, and in
   other branches of the same `match`, are unaffected by an error (branches
   are checked independently, `crates/elab/src/lib.rs:3176-3184`)
   [checked]. A hole *after* an error in the same branch is never reached,
   so its goal is missing until the error is fixed. Lean keeps going
   after errors; we stop at the first error in a branch. Acceptable for
   stage 2, listed as a risk.
9. **The check cache.** A namespace with a failed declaration isn't
   cached (an entry can't mention "a name that failed",
   `crates/elab/src/cache/mod.rs:925-926`) [checked]. A namespace with
   holes is unfinished in the same way, so it's re-checked every time and
   its goals are always fresh [inferred]. No cache change.
10. **Rewinding (live sessions).** The goals live in tables the session
    rewinds (`crates/driver/src/rewind.rs`), so an edit throws away the
    rewound namespaces' goals. The check–rewind–check differential test
    (stage 0b) covers them once they're in the dumped tables [inferred].
11. **`_` wording.** `E-UNSOLVED` stays an error, but where the hole's
    type is a proposition the note says "write `?` to see what's needed
    here" (D641).

### 4.1 Latency on each keystroke

The server re-checks the edited namespace from its start (level 1), then
its dependents in the background. Goals arrive with that namespace's
diagnostics. Uncached checks of whole namespaces [run, `STITCHWORT_TIMINGS=1
stitchwort check --no-cache` on `aoc/`, elaboration + kernel ms]:

| Namespace | ms |
|---|---|
| `Aoc.Day05` / `Aoc.Day07` (programs) | 3 / 2 |
| `Aoc.Day05.Proofs` | 19 |
| `Aoc.Day07.Proofs` | 100 |
| `Aoc.Day04.Proofs` | 406 |
| `Aoc.Day08.Proofs` | 804 |
| whole project, `--no-cache` (wall) | 2420 |
| whole project, warm cache (wall) | 830 |

So in most namespaces the goal follows typing within the server's
100 ms debounce (`lsp.rs:61`) [checked] plus a few tens of ms. In the big
proof namespaces it lags by up to about a second; one theorem alone,
`Aoc.Day08.Proofs.lastNeededExists`, takes 330 ms [run]. Re-checking only
the edited declaration (stage 5, level 2) is what fixes that; goal holes
don't make it worse (a `?` is cheaper to check than the proof it
replaces) [inferred].

**While you type, the declaration often doesn't parse**, and parser
recovery drops the whole broken declaration (`language-server.md` §6.1:
"Not recovered: inside a declaration") [checked]. Its goals then vanish
until it parses again, which would flicker. The server keeps the last
goals of a declaration that no longer parses, until it parses again, so
the goal stays on screen while you type the next token [inferred: needs
the declaration's identity across edits, by name; an implementation
detail, not a decision].

## 5. Protocol and the VS Code client

- **Stage 2: standard LSP only.** `textDocument/publishDiagnostics` with
  `severity: 3` (Information) and `code: "GOAL"`. The server adds an
  information severity to `Severity` and maps it at `lsp.rs:1302`. The
  thin client (`editors/vscode/client.js`, 64 lines; `extension.js`, 104)
  [checked] changes not at all. Neovim, Helix and Emacs's LSP clients show
  information diagnostics too [inferred].
- Optional, tiny: colour `?` in the TextMate grammar
  (`editors/vscode/syntaxes/`).
- **Later stage (panel):** one custom request, `stitchwort/goalAt
  {textDocument, position}` answering `{goal, context: [{name, type,
  value?}]}` or null, like `$/lean/plainTermGoal` [cited above]; and in
  the client, a webview panel that sends it on cursor moves (debounced)
  and renders the answer. Other editors can call the same request.
  Custom because LSP has no "goal" request; Lean adds its own
  (`$/lean/plainGoal`, `$/lean/plainTermGoal`) [cited above].

## 6. The playground

Yes, and cheaply. The playground shows errors and warnings as the CLI's
rendered text in its output panel (`web/index.html:1328-1352`,
`warningsView` at `1532`) [checked]; the WASM `check` returns errors and
warnings as JSON (`crates/web/src/lib.rs:58-69`) [checked]. Goals become a
third list, rendered the same way under a "Goals" heading above the
errors, with the same jump-to-place button. No server, nothing dynamic:
the site stays static. Hover over `?` in the playground's own tooltip
(`navtip`, `index.html:2153`) can come later. Estimate: small (half a
day).

## 7. Tests

- **Examples.** A new folder `examples/goals/`, run by
  `crates/cli/tests/examples.rs` like `reject/` (which snapshots rendered
  errors, `examples.rs:1-11`) [checked]: each file must report goals and
  no errors, and its rendered goals are snapshot-tested. Cases: proof
  holes, a hole in each `match` branch (refined types), `let` values,
  `match h:` hypotheses, an implicit parameter, a hole in an inferring
  position, two holes in one declaration, a hole beside an error in
  another branch, a lemma with a hole used by a later theorem (no
  error there), and a hole inside a dot call that's tried two ways
  (undone attempts).
- **LSP, in process.** `crates/cli/tests/lsp.rs` drives the server over
  `Connection::memory()` (`lsp.rs` tests `:24-60`) [checked]. New tests:
  open a file with a `?`, expect one diagnostic with severity 3 and the
  goal text; replace `?` by the proof, expect it gone; break the
  declaration's syntax mid-edit, expect the goal kept.
  `latency_on_aoc` (`:704-745`, ignored, release) gains a hole edit.
- **The client.** Nothing changes, so `dev/t vscode` (node tests of
  `client.js` against a fake server, `dev/t:450-457`) [checked] needs
  no new test in stage 2. The panel stage adds tests of its message
  handling the same way.
- **Playground.** `web/test.sh` gets one case: a `?` program shows a
  Goals section.
- **Rewind.** The existing check–rewind–check differential test, with a
  `goals/` example in its corpus.

## 8. Cost

Efforts per lane, as in `language-server.md` §6 (small ≤ half a day,
medium about a day). Estimates.

| Stage | What | Effort |
|---|---|---|
| 2a | `?` syntax; frozen-metavariable goal; recording, printing, dropping undone ones; unfinished declarations; CLI rendering and exit code; `examples/goals/` | Medium |
| 2b | Information severity in the server; keep goals across unparsable edits; LSP tests | Small |
| 2c | Playground Goals section | Small |
| 2d (later) | Goal at the cursor: probe re-check, `stitchwort/goalAt`, VS Code webview panel | Medium–large |

2a then 2b and 2c in parallel.

## 8.1 Stage 2a as built

*SW-31 stage 2a, 23 October 2026.*

**Syntax.** `?` is a token (`Tok::Question`) and an atom, `Expr::Goal`,
allowed anywhere an expression is. `x?` lexes as `x ?`.

**The goal** (`crates/elab/src/goals.rs`). `?` checked against `T` is a new
*frozen* metavariable applied to the variables in scope; unification never
solves it. The goal noted with it has the span, `T`, and the context: each
variable in scope that a case split hasn't replaced, outermost first, a
`let` with its value, a shadowed name with `✝`, compiler-made `%` names
left out. `?` where the type isn't known (an inferring position) gets a
fresh metavariable for its type, and "the type here isn't known yet" if
nothing solves it. Goals are printed when the declaration's metavariables
are cleared (`Elaborator::clear_metas`, as `flush_navigation`), with a
printing limit of 4000 characters instead of messages' 240
(`pretty::value_for_goal`). An undone attempt drops the goals it noted
(`undo::Snapshot` keeps their count), and a span printed twice keeps the
last. The diagnostic has its own severity, `Severity::Goal`, and code
`GOAL`; the CLI shows it as in §3.2, except that the heading is
"in `addZero`" (the declaration; the branch isn't named: the context and
the refined goal show it).

**Unfinished declarations** (D636). A goal's metavariable never reaches the
kernel: zonking keeps goals' metavariables while it looks for other
unsolved ones (so they're still reported as themselves), then fails with
the internal error `E-UNFINISHED` if one is left (`Elaborator::zonk_around`).
(The kernel refuses any metavariable anyway, so this is about the message,
not soundness.) The module (`module.rs`) turns a component whose only
errors are `E-UNFINISHED` into `Status::Unfinished`: failed to the kernel
like any other, but nothing reported except its goals. Its declarations go
into `Globals::unfinished`, which the kernel never reads; when the kernel
refuses something only because it uses unfinished declarations
(`E-FAILED-DEPENDENCY` with every failed reference in that set,
`kernel.rs`), and when an error is fallout of a stuck unfinished definition
(`blame_failed_dependency`), that becomes `E-UNFINISHED` too. So what uses an
unfinished declaration, in the same namespace or another, transitively, is
unfinished, silently. A namespace with goals, or with an unfinished
declaration, isn't written to the check cache.

**The commands.** A load with goals but no errors succeeds, with the goals
among the warnings, so each command decides:

| Command | With goals open |
|---|---|
| `check` | Prints them and "N goals open: …", exits 1. |
| `test` | Runs the tests that are finished (an unfinished test isn't admitted, so it can't run), then "N goals open", exits 1. |
| `run` | Runs `main` if it's finished, exit code as usual; if it isn't, `E-UNFINISHED`: "`main` isn't finished …" (`Session::main`). |
| `build --js` | Builds nothing: "nothing was built: N goals open", exits 1. `Session::extract` and `extract_namespace` refuse an unfinished export themselves (`E-UNFINISHED`), for other callers (the playground). |
| `eval`, the REPL | An expression using an unfinished definition, or with a `?` in it, is `E-UNFINISHED` (`infer_expr`). |
| `axioms` | Refuses an unfinished definition. |

The language server and the playground get the goal diagnostics as they
are: the server maps `Severity::Goal` to Information (one line, needed to
compile; the rest is stage 2b), the playground shows them where it shows
warnings until stage 2c.

**`_` as a proof** (D641). A `_` checked against a proposition is noted
(`Elaborator::proof_holes`); if it stays unsolved, `E-UNSOLVED`'s note is
"write `?` to see what's needed here".

**Tests.** `examples/goals/` (11 files: proof hole, each `match` branch,
`let` values, `match h:`, implicit parameters, inferring position, two
holes, beside an error, lemma used later, undone attempt, a test with a
hole) and `examples/projects/goals/across-namespaces/`, run by
`crates/cli/tests/examples.rs` (goals reported, no errors unless declared,
tests of what's finished pass; rendered output snapshot-tested). An
`accept/` example or project with a goal now fails. The rewind
differential test (`crates/driver/tests/rewind.rs`) checks every goals
example. Lexer and parser unit tests for `?`.

**Known gaps.** A `?` in a *signature* makes the declaration's name fail
before it's declared: a use in the same namespace is unfinished, but one
from another namespace reports "has errors". A `?` used as a function with
another `?` as its argument (`? ?`) is a type mismatch, since a frozen
metavariable can't be solved for. A `?` in an instance search's zonk, or in
a lifted local definition's type, may give that path's error instead of
the goal.

## 8.2 Stage 2b as built

*SW-31 stage 2b, 23 October 2026.*

**Severity.** Already in place from 2a: `Severity::Goal` goes out as
`severity: 3` (Information), code `GOAL`, the whole goal as the message
(D635). No client change.

**Goals kept across unparsable edits** (`goals_kept` in `crates/cli/src/lsp.rs`,
used by `Checker::publish`). Parser recovery drops a broken declaration
and its goals. The server remembers what it last published per file; a
goal from that publication is carried into the new one when it lies in a
stretch of the file outside every declaration that parses (from the
outline, which covers the declarations that still parse), and an `E-PARSE`
diagnostic is in the same stretch. It keeps its old range. Since the kept
goals are part of what is published, they survive further broken edits, and
go when the declaration parses again (fresh goals take over) or the
stretch no longer has a parse error.

**PROVISIONAL.** The note left the matching open ("by name, an
implementation detail"). I match by position (the stretch between parsed
declarations) rather than by declaration name, as the diagnostic carries no
name and the broken declaration has none in the outline. Costs: the kept
goal's range may drift if the broken edit adds or removes lines above it;
two broken declarations side by side form one stretch, so a goal could stay
after its own declaration became parseable-but-different only while a
neighbour is still broken. Alternative: record the declaration name with
each goal and match on the broken declaration's header text.

**Tests** (`crates/cli/tests/lsp.rs`): `an_open_goal_is_an_information_diagnostic`
(one diagnostic, severity 3, code `GOAL`, the goal text, gone when `?` is
replaced by a proof) and `goals_stay_while_their_declaration_does_not_parse`
(kept through two broken edits, replaced on re-parse, dropped when the `?`
is fixed, not kept for a parse error elsewhere).

## 8.3 Stage 2c as built

*SW-31 stage 2c, 23 October 2026.*

**WASM side** (`crates/web/src/lib.rs`, `project.rs`). Open goals are split
out of the warnings (they come in `Session::warnings` on a load that
succeeds, and among the diagnostics of one that fails) into their own
field: `"goals": ["…", …]`, each goal rendered as the CLI prints it, left out
when there are none. `check`, every answer for a source that doesn't load,
and the project's `check_project` all carry it; in a project the
`diagnostics` list still has each goal with severity `"goal"` and its file,
line and column.

**Page** (`web/index.html`). `goalsView` renders a "Goals (N open)" heading
and one box per goal, with the goal's full text in a `pre.goals`, above the
errors (as §6 says) and above the warnings. In a project each goal also has
the same jump-to-place button the errors have. Goals have their own colour
(`--goal`, blue, in the light and dark palettes), matching the LSP's
information severity. With only goals open, the status reads "1 goal open" /
"N goals open" (not "Checked by the kernel"), and the Check tab says there
are no errors but the declarations with goals aren't finished, instead of
"Every definition type-checks".

**Tests.** `web/test.sh "a ? program"` (a `?` program shows a Goals section,
no errors box; beside an error the goals come first and the errors stay in
their own box; gone once filled in) and the Rust unit test
`reports_open_goals_apart_from_warnings_and_errors`.

**PROVISIONAL.** (1) The warning-count button counts warnings only; goals
get the status text and heading, not a second button. Alternative: a "N
goals" button beside it that selects the Check tab. (2) Only the Check tab
(and the "doesn't check" views) shows the goals; the Tests, Evaluate and
Run tabs show nothing about them. Recommendation: leave as is until someone
wants it.

## 9. Risks

- **The first error in a branch hides later holes** (§4 item 8). Lean
  recovers from errors inside a term; we don't yet.
- **Big proof namespaces lag** up to about a second per keystroke until
  level-2 re-checking (§4.1).
- **Goals print computed** (`Succ (k + 0)`) rather than as written; for
  big definitions that unfold, goals may be hard to read. The same
  problem `rfl` messages have today.
- **A `?` in a signature** (`def f (x: ?)`) makes the declaration's type
  unknown, so its users fail too. Allowed but rarely useful.
- **Hover duplication** if a hover answer is added at `?` later (§3.2).
- **I haven't tried** how VS Code lays out a multi-line information
  diagnostic in its hover; error messages with notes are multi-line
  today and render fine [inferred], but the context column alignment is
  untested.
- **Agda and Idris details** in §3.1 marked [unverified]: their READMEs
  don't say, and I didn't install them.

## Decisions

**Decided (Matt, 23 Oct 2026):** D635–D641 all as recommended below. D1057: with a goal open, `check` exits 1, `test` runs the finished tests then exits 1, `run` runs `main` if it is finished, `build --js` refuses, and `eval`/REPL/`axioms` refuse anything unfinished (as built in stage 2a).

| ID | Question | Recommendation |
|---|---|---|
| D635 | How does VS Code show a goal in stage 2? | [**An information diagnostic at each `?`** with the full goal as its message: blue underline, shown on hover, listed in Problems; no client change. A Lean-style Goals panel later, its own stage (D640).] |
| D636 | What does an open `?` mean for the rest of the program? | [**Unfinished, not an error**: the declaration isn't checked by the kernel, later declarations can use it by its type (prove top-down, like Lean's `sorry`), running code that reaches it fails, and `check` exits non-zero with "N goals open".] |
| D637 | How is the goal line marked? | [**`⊢ T`**, as Lean and Coq do and as the language-server note showed; the alternative is `goal: T`.] |
| D638 | Do `let`-bound names show their values in the context? | [**Yes**, `total: Nat := sum xs`, as Lean does.] |
| D639 | In a `match` branch, is the goal printed computed (`Succ (k + 0) = Succ k`) or as written with the pattern put in (`Succ k + 0 = Succ k`)? | [**Computed for stage 2**, as `rfl` messages already are; a printer that substitutes without computing is a later improvement if goals prove hard to read.] |
| D640 | Goal at any cursor position (not only at `?`), with a panel? | [**Later, its own stage (2d)**: the expected type and context at the cursor, by a `stitchwort/goalAt` request and a VS Code webview. Not in stage 2.] |
| D641 | Should `E-UNSOLVED` on a `_` whose type is a proposition suggest `?`? | [**Yes**: "write `?` to see what's needed here"; its current note about implicit arguments is wrong there.] |
