# A language server for Stitchwort

**Status:** design note, 22 October 2026 (SW-31). Stages 0a, 0b and 0c
are built (SW-274, SW-275, [As built](#as-built-stages-0b-0c)), and the
server half of stage 1 (SW-282, [As built](#as-built-stage-1-server)).
Decisions D496–D498 are in the [table at the end](#decisions). Measured on
`main` at `d61ff947` with the release CLI, on a copy of `aoc/` with its own
cache folder, load average about 3. Claims about the code were checked by
reading or running the thing named; estimates are marked as estimates.

This note can be read without knowing the codebase. It takes about 15
minutes.

## 0. The short version

A **language server** is a long-running program that an editor talks to
while you type. It answers "what's wrong with this file", "what is this
name", "what can go after this dot", using a standard protocol (LSP), so
one server works in VS Code, Neovim, Emacs, Helix and Zed.

Today the VS Code extension starts a fresh `stitchwort check --index -`
process **when you save**, and reads the JSON it prints. That already gives
errors, go to definition, hover types, find references and the outline. A
server would add, in order of value:

1. **Errors as you type**, without saving, in about 0.1 s for most
   namespaces.
2. **Goals for proofs**: write `?` where a proof is missing and see what it
   has to prove and what you have to prove it with. This is what Lean's
   infoview and Agda's holes give, and the biggest gain for writing proofs.
3. **Completion**: after `xs.`, the functions `xs` can call; after `List.`,
   what's in `List`; plain names in scope; and library names that need an
   import, adding the `import Std (...)` line for you.
4. Smaller things: signature help, rename, "add import" fixes, run-test
   buttons, colouring by meaning, hints for hidden arguments.

The plan is a `stitchwort lsp` command in Rust that keeps one checking
session in memory and re-checks only the namespace you are editing (later,
only the declarations you changed), starting from the on-disk check cache.
The VS Code extension becomes a thin client. The playground shares the
engine (compiled to WebAssembly), not the protocol, so the site stays static.

Two things have to be built first, because the server can't work without
them (§5.1): the parser must keep going after a syntax error (today one
error hides every other error in the file, and a file is broken most of the
time while you type), and the checker must be able to throw away the
namespace it just checked and check it again.

## 1. What you would experience

### 1.1 Today

- Errors appear after you save, about 0.2 s later for a small namespace
  (measured: `check --index - --project . Aoc.Day05`, warm cache, 0.15 s)
  and 0.7 s for `Aoc.Day04.Proofs` after an edit to it. A full index of
  `aoc` runs after that, 0.7 s warm.
- Go to definition, hover, references, outline and workspace symbols answer
  from the last saved index. After you add a line, positions below it are
  off until the next save.
- A syntax error anywhere in a file hides all its other errors. Checked:

  ```
  def f (xs: List Nat): Nat := xs.
  def g: Nat := "a"
  ```

  reports only `E-PARSE expected a field name after '.'`, not the type
  error in `g`. The parser already splits a file into declarations
  (`split_decls`, `crates/syntax/src/parser.rs:54`) and collects every
  declaration's syntax errors, but then returns no module at all if there
  is any (`parser.rs:110`), so nothing is checked.
- A missing proof can be written `_`, and the message doesn't say what is
  missing. Checked:

  ```
  theorem addZero (n: Nat): n + 0 = n := _
  ```

  gives `E-UNSOLVED can't work out an implicit argument`, with the note
  "supply it explicitly with `f [x := …]`". Nothing shows the goal
  `n + 0 = n` or that `n: Nat` is available.
- No completion, signature help, rename or code actions.

### 1.2 With the server

| Feature | What you see | Value | Effort | Stage |
|---|---|---|---|---|
| Errors as you type | Red squiggles update about 0.3 s after you stop typing, in unsaved files too, and in the namespaces that import the one you're editing | High | Medium, after the two prerequisites | 1 |
| Navigation from live state | Definition, hover, references, outline, workspace symbols, as today, but always for the text on screen | Medium (exists, gets better) | Small (the index already exists) | 1 |
| Goals (`?` holes) | Write `?` for a missing proof or term. You get an information message at it: "goal: `n + 0 = n`", with the local names and their types. Hover over it shows the same. Later, a side panel that follows the cursor | **High for proofs** | Medium | 2 |
| Completion after `.` | `xs.` lists `map`, `filter`, `length`, … for a `List`, with their types, by the same rules dot notation uses | High | Medium | 3 |
| Completion of names | After `List.`, the members of `List`. Elsewhere, local names, the namespace's names, imported names, then library names that would need an import (picking one adds the import line) | High | Medium | 3 |
| Code action: add import | On `E-UNKNOWN-NAME` "`sort` is `Std.List.sort`… add `import Std (List)`", a light bulb that adds the line | Medium, cheap | Small | 3 |
| Signature help | Inside `f a |`, a popup with `f`'s parameters and which one you're on | Medium | Small, once completion's context exists | 3 |
| Run tests | "▶ run" above each `test`, and above `main`; a test's result shown next to it, from the test cache | Medium | Small–medium | 4 |
| Rename | Rename a declaration or local everywhere in the project, including `xs.map`-style uses | Medium | Small (from references), but must refuse when the project has errors | 4 |
| Semantic colouring | Constructors, functions, types and locals coloured by what they are, not by guessing from the text | Low (the TextMate grammar is decent) | Small (from the index) | 4 |
| Inlay hints | The hidden arguments the checker filled in (`List.map [Nat] [Text] …`), and types of `let`s, as faint text | Low–medium; noisy in proofs (hidden arguments are 70–80% of proof terms, `folded-calls.md` §1) | Small | 4, off by default |
| Case split | A code action on a pattern variable that writes out one equation per constructor (Agda's `C-c C-c`, Idris's `:casesplit`) | Medium for proofs | Medium | later |

**What first.** Errors as you type (stage 1) is the base everything else
stands on: it's the in-memory session. Goals (stage 2) next, because
proving is where Stitchwort users spend their time and nothing today
helps with it. Completion after that. The rest is cheap once those exist.

## 2. How other systems do it

**Lean 4.** The server runs one worker process per open file. The worker's
documentation:

> "elaboration is executed in a chain of tasks, where each task corresponds
> to the elaboration of one command. When the elaboration of one command is
> done, the next task is spawned. On didChange notifications, we search for
> the task in which the change occurred. If we stumble across a task that
> has not yet finished before finding the task we're looking for, we
> terminate it and start the elaboration there."
> — [Lean.Server.FileWorker](https://lean-lang.org/doc/api/Lean/Server/FileWorker.html)

So after an edit, everything above it is kept and everything from it down is
redone. Requests "iterate over tasks until they find the command that they
need", in a separate task so the main thread isn't blocked. The **infoview**
is a panel next to the editor; in a proof it shows "the current proof state
with all currently open proof goals at the position of the cursor", and in a
term "the current expected type at the position of the cursor"
([vscode-lean4 manual](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md)).
Lean does **not** re-check other files when you edit one: "changes in
`Submodule.lean` do not automatically become visible in `Module.lean`", and
you run "Server: Restart File" (same manual).

**Agda.** Not an LSP originally: Emacs's agda-mode drives the checker with
commands. You "write either `?` or `{! !}` and load the file", Agda turns
each into a numbered hole, and `C-c C-,` "shows the type expected in the
current hole, along with the types of any local variables". `C-c C-c` case
splits, `C-c C-r` refines a hole
([A taste of Agda](https://agda.readthedocs.io/en/latest/getting-started/a-taste-of-agda.html)).
Checking is per load (`C-c C-l`), not as you type. Agda's holes are the
model for our `?` (§4.2).

**Idris 2** ([idris2-lsp](https://github.com/idris-community/idris2-lsp)).
Code actions for holes: `CaseSplit`, `ExprSearch`, `GenerateDef`, `Intro`,
`MakeCase`, `MakeClause`, `MakeLemma`, `MakeWith`, `RefineHole` (README). It
re-checks a whole file **on save**: `didChange` only marks the file dirty,
and `didSave` reloads it
([ProcessMessage.idr](https://github.com/idris-community/idris2-lsp/blob/main/src/Server/ProcessMessage.idr),
lines 582–604); its own comment says commands "will fail" on files with
unsaved changes.

**rust-analyzer** uses salsa, a library of cached queries: "We use the salsa
crate for incremental and on-demand computation". Its key rule is that
"typing inside a function's body never invalidates global derived data".
Cancellation: on an edit the database "bumps this counter and waits until
all other threads using salsa finish"; a running query that notices
"panics with a special value", caught and "transformed into a
`Result<T, Cancelled>`". "Requests that modify the state or might block
user's typing are handled on the main thread. All other requests are
processed in background."
([architecture](https://rust-analyzer.github.io/book/contributing/architecture.html)).
The body rule doesn't hold for us: in a dependently typed language a
theorem about `f` can depend on `f`'s body, because checking it computes
`f`. So we can't copy salsa's granularity, only its ideas (early cutoff,
cancellation).

**Unison.** UCM, the codebase manager, hosts the LSP on a TCP port
(`127.0.0.1:5757`). Features: "Autocompletion", "Inline type and parser
error messages", "Format on save", "Show type on hover". "The LSP listens
for changes from the UCM it's linked to, so name resolution is dependent on
your current UCM path"
([language-server.markdown](https://github.com/unisonweb/unison/blob/trunk/docs/language-server.markdown)).
Its stored code is already checked and hashed, so the server only checks
the scratch file.

**What we take.** Lean's shape (keep everything before the edit, redo from
the edit on, cancel stale work), adapted to our dependency order (§4).
Agda's holes, shown Lean-style next to the code. rust-analyzer's
main-thread/background split and its cancellation by flag. Unlike Lean and
Idris, re-check the files that depend on the edited one, because the
check cache makes that cheap (D496).

## 3. Architecture

### 3.1 One process, two threads

```
 editor ──LSP (stdin/stdout)──▶ main thread ──edits──▶ checker thread
                                 │  documents             │ owns the Session
                                 │  last answers ◀────────┘ publishes answers
                                 └─▶ hover, definition, references (no wait)
```

- **`stitchwort lsp`**, a new subcommand of the existing CLI, speaking LSP
  on standard input and output. One process per editor window; it handles
  every project folder open in it.
- **The main thread** reads messages, keeps each open document's text and
  version, and answers navigation requests at once from the last published
  answers.
- **One checker thread** owns the `Session` and the `Elaborator`. They can't
  move between threads: the elaborator is full of `Rc` and `RefCell`
  (`Elaborator` in `crates/elab/src/lib.rs:133`; core terms share subterms
  through `Rc`). So the design has exactly one thread that checks, and
  everything else talks to it through channels.
- **Published answers** are plain data that can cross threads: the
  navigation index (references, symbols, types as text, diagnostics), the
  goals, and what completion needs (§4.3). The checker builds them after
  each check, as `--index` does today, and swaps them in. When the
  document has changed since, the main thread shifts ranges below the edit
  by its line delta before answering. A request that needs fresh state
  (completion, goals) waits for the check of the current version, with a
  short time limit.

**Which protocol library.** Two serious options:

| | `lsp-server` | `tower-lsp` (and its fork `tower-lsp-server`) |
|---|---|---|
| From | rust-analyzer (owned by the rust-analyzer team on crates.io) | Community |
| Style | "a synchronous crossbeam-channel based API" ([docs.rs](https://docs.rs/lsp-server/latest/lsp_server/)): you write the loop | Async (tokio): you implement a trait, methods take `&self` |
| Fits a non-`Send` session | Yes: the loop sends work to our checker thread | Needs `Arc<Mutex<…>>` state and a separate thread for the session anyway |
| Ordering | Messages in order, by construction | "handles notifications asynchronously, which is semantically incorrect and introduces out-of-order issues" ([async-lsp README](https://github.com/oxalica/async-lsp)): a `didChange` can be processed after a request that depended on it |
| Maintenance | Released with rust-analyzer | The original stalled in 2024; a community fork carries on |
| New dependencies | `lsp-server`, `lsp-types`, `serde_json`, `crossbeam-channel` | The same plus `tokio`, `tower` |

**[`lsp-server`.]** It's the one rust-analyzer itself runs on, we need our
own thread for the session whatever we pick, and the in-order guarantee
matters when every edit changes what the next request means. This is an
implementation choice, not a decision for Matt.

### 3.2 What happens on an edit

1. The editor sends `didChange` with the new text. The main thread updates
   the document and tells the checker "file F is now version v".
2. If the checker is busy with an older version, it is **cancelled** (§3.3).
3. The checker waits for typing to pause (about 150 ms; the extension's
   save debounce is 300 ms today), then re-checks what changed (§4) and
   publishes diagnostics for version v. An answer for a version older than
   the newest is dropped, never shown.
4. Then, in the background and still cancellable, it re-checks the
   namespaces that import the edited one, so their errors update too.
   Navigation answers for the rest of the project stay from the last full
   check until then.

### 3.3 Cancellation

Checking a big proof can take a second. The checker counts evaluation
steps already, through `Budget::step` (`crates/core/src/budget.rs:264`),
which every long computation calls. A shared flag checked there every few
thousand steps, turning into a new `ResourceError::Cancelled`, stops any
check promptly. This is rust-analyzer's design without the panic. The
elaborator is then in a half-finished state, so a cancelled check always
**rewinds** to the last good point (§5.1) before starting the next.

### 3.4 Memory

A full `aoc` check peaks at 162 MB resident (measured, `--no-cache`; 172 MB
warm). The server keeps one session per project, so expect about that per
open project. Lean keeps a snapshot per command, which is cheap for it
because its data structures are persistent; ours aren't, and copying the
session per declaration would multiply memory. So the server **rewinds**
instead of keeping copies. Rewinding also never frees the memory of the
library files a session loaded (they're kept), so memory stays near the
size of a full check. If it grows past a limit (default 1 GB, a setting),
the server starts a fresh session from the disk cache, which takes under a
second for `aoc` (§3.5).

### 3.5 Starting up: the on-disk check cache

On opening a project the server loads it the way `stitchwort check` does
today: every namespace and library file comes from
`.stitchwort/cache/check/` if its key matches (`check-cache.md`, stages 1
and 2). That's 0.7 s for `aoc` with navigation (measured, warm full index).
The server also **writes** entries when a namespace checks cleanly, so the
command line benefits from what the editor checked and the other way round.
The key is the text itself, not a file date, so an entry made from unsaved
text is correct for that text; but it would churn the cache on every
keystroke. **[Write entries only when the text equals the file on disk]**
(implementation detail).

## 4. Re-checking only what changed

Three levels, each a stage. The numbers say where each pays off.

**How long namespaces take to check** (measured, `STITCHWORT_TIMINGS`,
`--no-cache`, elaboration plus kernel): `Aoc.Day04.Proofs` 1.37 s,
`Aoc.Day02.Proofs` 0.95 s, `Aoc.Day07.Proofs` 0.20 s, `Aoc.Day03.Proofs`
0.12 s, every other `aoc` namespace under 0.1 s (`Aoc.Day05` 0.04 s).

**How long single declarations take:** of 690 `aoc` declarations, the
median is 0.1 ms, 90% take under 4 ms, 99% under 100 ms, and the slowest,
`Aoc.Day02.Proofs.dividesOfWritten`, 259 ms.

### 4.1 Level 1: the edited namespace, in memory (stage 1)

When you edit a file of namespace N, the server's session holds N's
imports (from memory, already checked) and N last. To re-check, it
rewinds the session to just before N and checks N again from the current
text. The fixed costs of a fresh process disappear: the core (about 60 ms)
and parsing the whole project (about 60 ms; `check-cache.md`, stage 2
measurements). So a namespace like `Aoc.Day05` re-checks in about 40 ms
instead of 150 ms, and the two big proof namespaces in about 1–1.4 s
(estimates, from the timings above).

If you then edit a file of another namespace M, the server rebuilds the
session in the order "M's imports, then M", from the disk cache. That costs
about what a scoped warm check costs today (0.15 s for `Aoc.Day05`), once
per switch.

**Dependents.** After N checks, the namespaces that import N are
re-checked in the background, in a second pass over a session that has N's
new state. Lean leaves this to "Restart File"; here it's automatic (D496).

### 4.2 Level 2: only the declarations that changed (stage 5, if needed)

Within a namespace, Stitchwort doesn't check in source order. Every
top-level name is visible everywhere in the namespace, and declarations are
checked in **dependency order**: a declaration after everything it uses,
earliest in the source first among those that are ready
(`crates/elab/src/module.rs:1–37`). So Lean's rule "keep everything above
the edit" becomes "keep everything **checked before** the first declaration
the edit affects":

1. The parser already splits a file into one token group per declaration.
   Compare each group's text with the last version's. Unchanged
   declarations are those with identical text.
2. If the set of top-level names or the imports changed, fall back to
   level 1.
3. Otherwise the affected declarations are the changed ones and everything
   in the namespace that depends on them (the dependency graph `module.rs`
   already computes), plus everything after an edited instance (instances
   are found by type, so anything later may have used one).
4. Rewind to just before the first affected declaration **in the check
   order**, and check from there on.

Editing a leaf proof then re-checks only that proof and whatever was
ordered after it. Editing a data type near the start re-checks nearly
everything, like Lean editing near the top of a file.

The hard part is **positions**. A declaration below the edit whose text is
unchanged keeps its recorded data (references, local types, warnings,
lifted helpers' spans), but its text has moved. Each kept declaration
needs an offset from where it was checked to where it is now, applied when
answers are published. It's bookkeeping, but it touches every table that
holds a span.

**Is it needed?** Only for the big proof namespaces: level 1 already gives
under 0.1 s for all but four of `aoc`'s namespaces, and 0.12–0.2 s for two
of those four. The two that take a second are exactly the ones where people
write long proofs, so it probably is needed eventually, but it's the last
stage and it should start from measurements of stage 1 in real use.
(Splitting a 2,000-line proof namespace into several is a workaround that
also helps today.)

### 4.3 Level 3: stop at unchanged results ("early cutoff")

If an edit doesn't change what a namespace produces (a comment, a proof
that is rewritten but proves the same statement, renaming a local), its
dependents needn't be re-checked. The check cache already plans this
(D280): compare the content hashes and exported tables a namespace produced
before and after, and if they're equal, its dependents are still valid.
In the server it's simpler than on disk, because the old results are in
memory. A rewritten proof still changes the theorem's content hash today,
so the cutoff wouldn't fire for it; whether it could depends on the proof
irrelevance design (`proof-irrelevance.md`), which isn't built.

## 5. Building blocks

### 5.1 Two prerequisites

**Parsing that keeps going.** Return the declarations that parsed together
with the syntax errors of those that didn't, and check the good ones. A
broken declaration's name should still be declared, as "failed", so uses of
it say "`f` has errors" (the existing `E-FAILED-DEPENDENCY` path,
`module.rs:452`) instead of "unknown name". The name is usually readable
even when the body isn't (`def f (...)`). Lexer errors (an unclosed string)
need the same treatment: stop the token group at the next line that starts
a declaration. Useful on its own: the command line would report all errors
of a file at once.

**Rewinding the session.** The check cache already does a small version of
this: before replaying a unit it notes the size of each table, and if the
kernel refuses a replayed declaration it removes everything the replay
added (`snapshot` in `crates/elab/src/cache/mod.rs:290`;
`Registry::forget_from` in `crates/core/src/registry.rs:361`). Rewinding is
that, made general: a `mark()` that notes every table's size (the
definitions, the data types, the about 20 side tables `check-cache.md` §A.2
lists, the name table, the navigation recorder, the source map), and a
`rewind(mark)` that truncates them all. The same differential test idea as
the cache's catches a forgotten table: check a namespace, rewind, check it
again, and compare the canonical dump (`crates/elab/src/cache/dump.rs`)
with a fresh session's.

### 5.2 Goals: `?` holes and the context at a position

**The user's side (D497).** Add `?` as a **goal hole**, in any place an
expression can go. Checking a file with one reports, at the hole, an
information diagnostic (not an error, but the declaration counts as
unfinished, like a failing one, and a project with holes doesn't pass
`check`):

```
[goal] theorem addZero: the proof is missing here
  n: Nat
  ⊢ n + 0 = n
```

It lists the local names in scope and their types, and the type the hole
must have, after the checker has used what it learned (in a `match` arm,
the refined types). This works in the CLI and the playground with no
editor at all. `_` keeps its current meaning, "work it out for me". In the
editor, the same text is the hover over `?`, and a later "Goals" panel can
follow the cursor like Lean's infoview, showing the expected type wherever
the cursor is, not only at holes.

**The compiler's side.** One new recording: **the context at a position**.
When the elaborator checks an expression whose span contains the
requested position (or a `?`), it notes the local names with their types
and the expected type, printed as text while metavariable solutions are
known. The navigation recorder already prints local variables' types at
the end of each declaration in the same way (`code-navigation.md`, "How
it's recorded"), so this is the same machinery at one more place. This one
recording serves goals, completion of local names, signature help (which
function is being applied and which argument is next), and expected-type
hover.

### 5.3 Completion

- **After `.`**, the receiver's type decides. Dot notation already finds
  the namespace from the receiver's type as written (`p: Price` tries
  `Price.f`, then `Nat.f`; `crates/elab/src/dot.rs:1–9`), and dot notation
  needs no import (D261). Completion lists the definitions of those
  namespaces that have a parameter the receiver can go into, by the rule
  `dot-receiver.md` settles, with record fields first.
- **After `List.`** (a namespace prefix), the members of that namespace.
- **Plain names**: locals (from §5.2), then the namespace's own names, then
  imported names, then library names that would need an import. Picking one
  of the last adds the import line, the way TypeScript's auto-import does.
  The scope code already knows the import each name needs: it's what the
  slim-prelude error says (`crates/elab/src/scope.rs:1078–1176`).
- **The text is broken while you complete.** `xs.` doesn't parse. The
  usual trick (IntelliJ's, rust-analyzer's) is to complete on a copy of
  the text with a dummy name inserted at the cursor (`xs.zzzz`), check that
  declaration in "completion mode", which records the receiver's type and
  the context at the dummy instead of reporting it unknown, then throw that
  check away (rewind).

### 5.4 Code actions

- **Add the import** for `E-UNKNOWN-NAME` and the slim-prelude errors. To
  avoid parsing English, diagnostics get an optional machine-readable fix
  (`"fix": {"addImport": "Std (List)"}`) next to the message; the index
  carries it too, so the playground can show the same button.
- Later: **fill a hole** with a candidate (`Eq.refl`, a hypothesis whose
  type matches), **case split** on a variable, **add the missing cases**
  for `E-NONEXHAUSTIVE`. These are Agda's and Idris's interactive
  commands, as code actions.

### 5.5 Tests and running

A code lens "▶ run" above each `test` and above `main`. Running a test
reuses `stitchwort test`'s cache of results, so the lens can show "passed"
from the cache without running anything. It runs in a separate process
(the CLI), not in the server's session, so a test that loops can be killed
without losing the session.

### 5.6 What the extension becomes

`extension.js` (431 lines) and `navindex.js` (301) shrink to a client that
starts `stitchwort lsp` and lets VS Code's standard client library
(`vscode-languageclient`, from Microsoft) do the rest. The TextMate
grammar stays for instant colouring. The lookup logic in `navindex.js`
moves into the server in Rust (it's the same logic: find the reference at a
position, follow it). `std-source` stays: the server serves library files
under the same read-only `stitchwort-std:` scheme. Other editors get the
same features from configuration alone. No transition: once the server
does what the extension does, the old process-per-save path is removed
(`check --index` stays, for the playground and scripts).

### 5.7 The playground (static site)

The playground can't run `stitchwort lsp`: that needs a server process,
and the site must stay static. It doesn't need the protocol, only the
engine. **[Share the engine, not the protocol]** (D498): the session layer
(documents, rewinding, re-checking, the published answers) lives in a
crate with no file or thread access, used by both `stitchwort lsp` and
`crates/web`. The worker keeps a session between requests instead of
starting fresh each time, so the playground gets level-1 re-checking,
goals, and completion through JSON calls like the ones it uses now.

Two limits. Cancelling: the worker can't share a flag with the page
without `SharedArrayBuffer`, which needs response headers a plain static
host may not let you set, so the playground keeps cancelling by
terminating the worker, as it does today
(`web/playground-worker.js:1–4`), and the next request starts a fresh
session. And the playground's editor is a plain `<textarea>`, so
completion menus and hover need an editor component first (a separate
playground decision, not this note's).

## 6. Stages

Efforts are for one lane, as on recent tickets: small is up to about half a
day, medium about a day, large several lanes. Estimates.

| Stage | What | Effort | Done when |
|---|---|---|---|
| 0a | Parser keeps going after a syntax error; broken declarations' names declared as failed | Small–medium | The file in §1.1 reports both errors; examples snapshots updated |
| 0b | `mark()`/`rewind()` on the session, with the check–rewind–check differential test | Medium | The test passes on every example and on `aoc` |
| 0c | Cancellation flag in `Budget::step` | Small | A cancelled check rewinds and the next check matches a fresh one |
| 1 | `stitchwort lsp` (`lsp-server`), checker thread, level-1 re-checking, dependents in the background, diagnostics as you type, navigation from live state, the thin VS Code client | Large (2 lanes: server, client) | Typing in `aoc` shows errors without saving; definition, hover, references, outline match today's |
| 2 | `?` goal holes and the context-at-position recording; hover on a hole | Medium | §5.2's example prints its goal in the CLI and the editor |
| 3 | Completion (dot, prefix, names, auto-import), signature help, the add-import action with machine-readable fixes | Medium–large | Completion after `xs.` in `aoc` lists `List`'s functions |
| 4 | Test lenses, rename, semantic colouring, inlay hints (off by default) | Medium | Each works in VS Code on `aoc` |
| 5 | Level-2 re-checking within a namespace, and early cutoff | Large | Editing a leaf proof in `Aoc.Day04.Proofs` re-checks in under 0.3 s |
| 6 | The playground shares the session engine | Medium | The playground re-checks without starting a fresh session |

Stages 2 and 3 can run in parallel after stage 1. Stage 0a is worth doing
now whatever happens to the rest.

### 6.1 As built (stage 0a)

- `parse_module_recovering` (`crates/syntax/src/parser.rs`) returns the
  declarations that parsed plus every syntax error; `parse_module_within`
  is that, returning `Err` if there are errors, so library and other
  callers are unchanged. Recovery is at declaration boundaries only (a
  line at column 0, as `split_decls` already split them). A lexical error,
  or a first declaration not at column 0, still stops at that one error.
- A declaration that failed to parse is left out of `Module::decls`; the
  names it would have declared are read off its tokens into
  `Module::failed`: the name after `def`, `theorem`, `instance`, `type`,
  `interface` or `ability` (after `export` too), and for the last three
  each name after a top-level `|`. A declaration that broke before its
  name declares nothing.
- The elaborator enters each failed name as `Global::Failed` (the state
  elaboration failures already use), unless something else declared it.
  A use then gives `E-FAILED-DEPENDENCY`, which the load drops when there
  are syntax errors: the syntax error says it. `E-UNKNOWN-NAME` doesn't
  appear for it.
- A single file (`load_file`) and a project namespace check what parsed
  and report parse and check errors together, in file order. Such a load
  is always an error. A project namespace with syntax errors is never
  cached, its dependents are skipped as before (`E-NAMESPACE-FAILED`),
  and `import N (..)` of it brings no names, as before.
- Not recovered: inside a declaration (the whole declaration is dropped,
  so errors in its later lines aren't seen), and the namespace and import
  lines (an error in one is reported but its effect is lost: a bad import
  adds no names, so uses can give `E-UNKNOWN-NAME`).
- Examples: `reject/syntax-errors-two`, `syntax-error-and-type-error`
  (the §1.1 file), `syntax-error-then-use`.

## 7. What to measure

- **Time from keystroke to squiggle**, per namespace of `aoc`, at level 1:
  the median and worst, for an edit to a leaf proof and to a definition
  near the top. Target: under 0.3 s for all but the two big proof
  namespaces. This decides whether and when stage 5 is needed.
- **Hover and definition latency** while a check is running: should be
  under 20 ms, since they answer from published data.
- **Cancellation delay**: from an edit to the old check stopping. Target:
  under 20 ms, which sets how often `Budget::step` looks at the flag.
- **Memory** after an hour of editing `aoc` (rewinding shouldn't leak),
  against the 162 MB of one full check.
- **Correctness**: after any sequence of edits, the server's diagnostics
  and index equal a fresh `check --index` of the same text. A test can
  replay recorded edit sequences and compare.

## 8. Risks

- **A table rewinding forgets.** Same risk as the cache's, same defence:
  the differential test, and every table goes through the same mark.
- **Stale or wrong answers after many edits** that a fresh check wouldn't
  give. Defence: the replay test of §7, and a "restart server" command.
- **Parser recovery reporting nonsense** after a syntax error (cascades).
  The per-declaration split limits the damage to one declaration.
- **The two big proof namespaces stay slow** until stage 5, which is the
  hardest stage (positions of kept declarations). Workaround meanwhile:
  smaller namespaces.
- **Unsaved text seen by other namespaces** (D496) means an error can
  appear in a file you haven't touched because of a half-typed edit
  elsewhere. That's how TypeScript and rust-analyzer behave too, and it
  goes away when the edit is finished.
- **A dependency for the extension.** `vscode-languageclient` makes it an
  npm package rather than plain files. Small, but the extension currently
  has none.
- **Kernel time.** Every re-check runs the kernel (D277, option A). In the
  big proof namespaces that's about a quarter of the time (372 of 1,369 ms
  for `Aoc.Day04.Proofs`). If D277 ever chooses B for interactive runs,
  the server is where it would pay.

## 9. Critical self-review

- **The level-1 numbers are estimates.** I measured fresh processes and
  per-declaration timings, and subtracted the fixed costs. The real
  in-memory re-check may differ, for example if rewinding loses library
  files the namespace loaded lazily and they must be replayed from the
  cache each time (about 5–25 ms per file, `check-cache.md` stage 1
  measurements). Stage 1's first job is to measure this.
- **Level 2 is less designed than it looks.** Besides positions, `auto`
  arguments search all eligible declarations (`auto_eligible`,
  `module.rs:1634`), so adding a lemma can change what a later `auto`
  finds. Step 2 of §4.2 (a changed name set falls back to level 1) covers
  adding, but I haven't checked every other kind of hidden dependency
  (instances are covered by step 3; `include` files; derived instances).
  It needs its own short note before it's built.
- **Rewinding the session in the middle of a namespace** assumes every
  table only grows during a namespace. Stage 1 of the cache found
  exceptions ("an older instance or table row changed", `check-cache.md`
  stage 1, point 3), which it handles by not caching. The rewind has to
  handle them, by recording old values, not just sizes.
- **Goals at `?` assume the expected type is known there.** In inferring
  positions (the function in an application) it isn't; the goal then
  shows an unknown, as Lean does. Fine, but the message should say so
  rather than print a metavariable name.
- **I haven't tried `lsp-server`** in this repo; the choice rests on its
  documentation, rust-analyzer's use, and the `Rc` constraint, which I
  did check.
- **The playground part depends on an editor component** that doesn't
  exist yet; the engine-sharing is sound, but the user-visible gain there
  waits on that separate choice.
- **I didn't look at how other editors render goals.** Lean's infoview is
  a VS Code webview with its own protocol extension; outside VS Code, the
  hover and the diagnostic are what remain. That's why §5.2 puts the goal
  in a diagnostic first.

## As built (stages 0b, 0c)

*SW-275, 22 October 2026.*

**The API** (`crates/driver/src/rewind.rs`, on the existing `Session`):

| | |
|---|---|
| `session.mark() -> Mark` | Where the session is. Only between loads (it asserts no metavariables and no library file loading). |
| `session.rewind(&mark)` | Back to the mark. A mark can be rewound to any number of times, until the session is rewound to an earlier one. |
| `session.cancel_flag() -> Arc<AtomicBool>` | The flag another thread sets to stop the check running. |
| `session.cancellable(\|s\| …) -> Result<T, Cancelled>` | Runs a check that the flag can stop: clears the flag, marks, watches the flag while the closure runs, and if it was seen, rewinds and returns `Cancelled` instead of what the half-finished check reported. |

The elaborator's part is `Elaborator::mark`/`rewind` (`crates/elab/src/rewind.rs`)
and the kernel environment's is `Globals::mark`/`rewind`
(`crates/core/src/globals.rs`), which changes no rule of the kernel: it
removes declarations, and what was recorded about them.

**What rewinds, and how.** Each table goes back one of three ways:

- *Cut back to its length*: definitions, data types, abilities, lifted
  helpers, tests, the source map, the session's warnings, and the caches
  indexed by definition (erasure, result heads, `performs`, content hashes).
  Natives and primitives registered for removed definitions, and built-ins
  bound to them, are dropped (`Builtins::rewind`, `Registry::forget_from`).
- *Rows for removed data types dropped*: records, interfaces, data owners,
  and why `==`, `show` and `compare` aren't derived.
- *A copy taken at the mark put back*: the name scope, instances, the module
  state, the project's tables, the check cache's namespace keys and
  replayed names, the library's load state (so library files loaded since
  are unloaded), the dot-call caches, the `include` locations, and the whole
  navigation recorder. These are the tables a later load can change an old
  row of, or whose keys are spans in files that exist before the mark.
- *Emptied*: every per-declaration table (obligations, drafts, local
  definitions, `decreasing`'s state, metavariables), which a cancelled
  check can leave half-full; the budget goes back to "no operation
  running". The `glue` switch and `Globals::module` are restored.
- *Left alone*: settings (limits, test switches, `disable_natives`), the
  check cache's store and statistics, and `STITCHWORT_TIMINGS`' rows, which
  are process-wide and describe time spent, rewound work included.

`Elaborator::rewind` and `Globals::rewind` destructure every field without
`..`, so a new field doesn't compile until it says how it rewinds.

**Cancellation.** `ResourceError::Cancelled`, from a flag in `Budget`. The
fast path of `Budget::step` is unchanged: while the flag is watched, the
threshold it compares against is the next poll point (every 16,384 steps,
`POLL`) instead of the limit, and the cold path reads the flag. It is also
read when every operation starts, and once seen it is sticky: every later
operation fails at once, so the rest of the check runs through in
microseconds per declaration. Only `cancellable` watches the flag, so
printing, the index and tests afterwards never stop. A check cache entry
is never written once cancellation is seen (`cache/mod.rs`), and test
results that ran out of resources were already never cached.

**Tests** (`crates/driver/tests/rewind.rs`). Compared with a fresh session:
the canonical dump, every definition's and data type's content hash, the
navigation index JSON and the rendered diagnostics. Three ways: check,
rewind, check (and the rewound session must equal a fresh one before the
second check, and a mark is rewound to twice); in a project, every
namespace checked, rewound to just before it and checked again (a hidden
`recheck_namespaces` switch in the project loop); and a check cancelled at
its first operation, then checked again. With `STITCHWORT_SLOW=1`: every
example (506 files, 53 projects) and `aoc` pass, and a check of `aoc`
cancelled from another thread at 1, 10, 50, 150, 400 and 900 ms rewinds and
the next check matches a fresh one. The normal tier runs every eighth file
and every fourth project.

**Measured.**

- *Cost of the flag*, `aoc`, `check --no-cache`, release, instructions
  retired (`/usr/bin/time -l`, 3 runs each): before 19.12–19.15 G; after,
  flag not watched (the CLI) 19.08–19.12 G; after, the whole check run
  through `cancellable` 18.97–18.98 G. All within run-to-run noise (about
  0.3%), so no measurable cost. `STITCHWORT_TIMINGS` wall time, best of 3:
  1,489 ms before, 1,483 ms after, 1,464 ms watched.
- *Cancellation delay*: 5–23 ms from setting the flag to `cancellable`
  returning, with the full example test running on 8 other threads. The
  slow part is elaboration that takes no evaluation steps, which only an
  operation start notices.
- *Mark and rewind*, after a full `aoc` check with navigation: `mark()`
  1.9 ms, rewinding to it 3.5 ms, rewinding to an empty session 34 ms
  (dropping every declaration).

**What the note got wrong or left open.**

- §5.1 says a mark "notes every table's size" and rewind "truncates them
  all". Sizes are enough for less than half the tables; the scope,
  instances, module state, navigation and the dot-call caches are copied
  (§9's third point predicted this). At a namespace boundary that costs 2 ms
  for `aoc`; per declaration (stage 5) it would need an undo log instead.
- §3.4 says rewinding "never frees the memory of the library files a
  session loaded (they're kept)". As built it unloads them, because keeping
  them changes definition ids and the order of names, and then nothing
  equals a fresh check. Keeping them is a possible stage-1 optimisation, but
  needs a different notion of "the same result" (by path and hash, not id).
- §3.3's "checked there every few thousand steps … stops any check
  promptly": the 20 ms target of §7 is only just met under load. If stage 1
  measures worse, `Budget::nesting` can poll too.
- D498's "a crate with no file or thread access": the session layer is in
  `crates/driver`, which `crates/web` already uses. `Session`, `mark`,
  `rewind` and `cancellable` touch neither files nor threads, but the crate
  also holds `DiskFiles` and the test thread pool. Splitting those out is
  only needed if the rule is to be enforced by the compiler.
- Marks are only valid between loads. Rewinding to a point inside a
  namespace (stage 5) needs the module loop to stop between declarations.

## As built (stage 1 server)

*SW-282, 22 October 2026 (D515). The VS Code client is SW-283.*

### What the client can rely on

**Command line:** `stitchwort lsp`, with no arguments. It speaks LSP on
standard input and output and logs to standard error. With
`STITCHWORT_LSP_TRACE` set, it also logs each namespace checked and how
long checking and publishing took.

**`initialize`** replies with `serverInfo: {name: "stitchwort", version}`
and exactly these capabilities:

```json
{
  "textDocumentSync": { "openClose": true, "change": 1, "save": { "includeText": true } },
  "definitionProvider": true,
  "hoverProvider": true,
  "referencesProvider": true,
  "documentSymbolProvider": true,
  "workspaceSymbolProvider": true
}
```

`change: 1` is full sync: each `didChange` carries the whole text. The
only initialization option is `{"debounceMs": N}`: how long typing must
pause before a check starts. The default is 100 ms; the tests use 0.

**Messages handled:**

| Method | What the server does |
|---|---|
| `textDocument/didOpen`, `didChange` | For a `file:` URI: the unsaved text replaces the file's text in its project, or the file is checked on its own if it isn't in a project's source folders. A `stitchwort-std:` document is accepted and ignored: it's read-only and gets no diagnostics. |
| `textDocument/didClose` | A project file goes back to its text on disk. A file on its own is forgotten, and its diagnostics are cleared. |
| `textDocument/didSave` | Records the saved text as the file's text on disk. This only decides when the check cache may be written. |
| `workspace/didChangeWatchedFiles` | Reads the file from disk again, unless it's open. The server doesn't register for this notification itself; a client may send it. |
| `textDocument/publishDiagnostics` (sent) | With the document's `version` for open files, and none for others. Sent for a file when its diagnostics change, or when the version they're for changes. `code` is the error code (`E-TYPE-MISMATCH`), `source` is `stitchwort`. The message is the main text, then the first label and the notes (`Note: …`), one per line, as the extension showed them. Other labels are `relatedInformation`. Diagnostics with no place go on the project's `stitchwort.yaml`. |
| `textDocument/definition` | One `Location`, or `null`. |
| `textDocument/hover` | Markdown: the type in a `stitchwort` code block, then the kind and the full name (``def  `Aoc.Day01.parseTurns` ``, `local` for a local). The range is the name's. |
| `textDocument/references` | Every use in the project, sorted by file and position, plus the declaration if `includeDeclaration`. |
| `textDocument/documentSymbol` | `DocumentSymbol`s nested by container (a type's constructors and fields under it). `detail` is the type, or the kind when there's no type. |
| `workspace/symbol` | Ranked as the extension ranked them: the exact short name first, then a part of the full name, then the letters in order. A flat list of `SymbolInformation`. |
| `shutdown`, `exit` | As the protocol says. Any other request gets `MethodNotFound`. |

**Library files** are named by `stitchwort-std:` URIs, followed by the
path under `std/` with no slash after the colon: `stitchwort-std:core/Data.sw`
(a file of the core), `stitchwort-std:List/Toolkit.sw`. These are the
`std` markers of `check --index`. The client shows their text with
`stitchwort std-source <path>`. Definition, hover and references work in
these documents too, answered from the first workspace that has
references there.

Navigation answers what the last check published. Between an edit and its
check, ranges in the edited file are those of the text checked last; they
aren't shifted by the edit's line delta (see "Not done" below).

### Architecture

- **The engine** is `crates/driver/src/live.rs`. `LiveProject` and
  `LiveFile` take texts and give `Answers`: for each file, its references
  (each with its target, name, kind and type), outline and diagnostics,
  with LSP ranges. They have no file or thread access (D498). The answers
  come from `nav::index_data`, the data that `index_json` now prints, so
  the server and `check --index` share one code path. The project loop's
  per-namespace check became `Session::check_project_namespace`, which
  both the command line and the engine call. `analyse` was split so that
  the engine can analyse files already parsed (`analyse_parsed`).
- **The front end** is `crates/cli/src/lsp.rs`, with the `lsp-server`
  crate. The **main thread** reads messages in order. It sends edits to
  the checker, then sets the shared cancel flag. It answers navigation at
  once from the published answers, behind an `RwLock`. The **checker
  thread**, with a 64 MB stack, owns one `Session` per project and one per
  file on its own. All the sessions share one cancel flag
  (`Session::share_cancel_flag`). The checker applies every pending edit,
  waits for the debounce, then does one step: it checks one namespace, in
  `cancellable_at` (`cancellable`, with the step's own mark). It publishes
  after the edited namespace's step and after the last step. Between steps
  it takes new edits, so the background part stops for an edit as well as
  being cancellable inside a step.
- **What re-checks when (level 1).** The engine marks the session before
  each namespace, in the order it checks them. After an edit, it finds the
  first namespace in that order whose files' texts differ, rewinds to the
  mark before it, and plans the rest. The plan is: the namespaces the
  edited one uses that were rewound too, then the edited namespace, then
  everything else that was rewound, in canonical order. That includes the
  namespaces that use the edited one, so their diagnostics update from the
  unsaved text (D496). It falls back to rewinding everything in three
  cases:
  - a namespace appears or disappears;
  - a namespace that was kept now uses one after it;
  - the analysis fails (a file without a namespace line, clashing
    namespaces, a cycle). Then its diagnostics are published and nothing
    is checked.

  Which namespaces exist, and what each uses, is read from a scratch parse
  of every file, kept for as long as a file's text is the same. A
  namespace's files are parsed into the session when it's checked, after
  its mark, so rewinding drops their old text too.
- **Library files are loaded up front.** `LiveProject::new` calls
  `load_all_libraries` before the first mark. Loaded on demand, a library
  file that a namespace uses is unloaded whenever that namespace is
  rewound (§"As built" 0b), then loaded again from the cache. That runs
  the kernel again: `Mod` made re-checking `Aoc.Day01` take 140 ms instead
  of 28. Since the library never changes after that, the library files'
  answers are computed once (`index_data_of(…, library: false)` from then
  on), which cut publishing from 50 ms to 11 ms. A file on its own still
  loads the library on demand, with no check cache.
- **Each publish recomputes every checked file's answers**, not only the
  answers of the namespaces just checked. A namespace checked later can
  add to an earlier one's answers: a use of a generated declaration, such
  as a record's `ext` theorem, makes it a symbol at the record's
  declaration. The navigation test caught this.
- **Check cache.** A project's session uses `.stitchwort/cache` in the
  project folder, as the command line does. Writes happen only while every
  open file's text equals its text on disk: the store is wrapped, and the
  wrapper drops writes otherwise. Reads always happen.

### Measured

Release build, on a copy of `aoc` with a warm cache, after rebasing onto
the fix for `Std.Nat.digitsExample` (SW-286). Before that fix, any open
of `aoc` cost 11 s of kernel time on that one theorem. These are the times
from sending `didChange` to receiving its `publishDiagnostics`, in process,
with the debounce at 0. Each edit adds a new `def` at the end of the file,
and the two files are edited in turn, six rounds each:

| Edited | First edit | Then (6 rounds) | Of which: checking the namespace / publishing |
|---|---|---|---|
| `Aoc.Day01` (`Day01.sw`) | 66–105 ms | 41–47 ms | 28 ms / 11 ms |
| `Aoc.Day04.Proofs` (`Proofs/Core.sw`) | 589–629 ms | 586–641 ms | 550 ms / 30 ms (more files) |

So the target of §7 (under 0.3 s for all but the two big proof
namespaces) is met. `Aoc.Day04.Proofs` takes as long as checking it does,
which is what stage 5 is for. Other numbers:

- Cancellation (`a_newer_edit_cancels_the_check_running`): one check of
  `Aoc.Day04.Proofs` took 657 ms. An edit sent a quarter of the way into
  the next check got its diagnostics 639 ms after it was sent. Without
  cancelling, that would be about 1.1 s.
- Memory: 348 MB resident for the test process after these rounds, against
  165 MB for `check --index` of `aoc`. The extra comes from a mark per
  namespace (each mark copies the scope, the navigation recorder and the
  other copied tables) and from the whole library being loaded. §3.4's
  limit-and-restart isn't built.

### Tests

`crates/cli/tests/lsp.rs` drives `serve` in process over
`Connection::memory()`:

- **A file on its own.** It opens with an error and gets `E-TYPE-MISMATCH`
  at the right line. A `didChange` that fixes the error gets empty
  diagnostics; the text is unsaved, so the file on disk still has its
  error. Then definition, hover (type and name), references, a local's
  binder, the outline, and a library definition that gives a
  `stitchwort-std:core/…` location, whose document then answers a hover.
- **AoC against `check --index`.** For every word start in `Day01.sw`,
  `Proofs/Part2.sw` and `Day05.sw` (more than 500 names), the definition
  and hover type equal the extension's lookups (`refAt`, `targetOf`,
  `hoverOf`) done on `check --index` JSON. The outlines are equal, the
  references to `Turn` are equal, and workspace symbols are checked. Then
  an unsaved edit breaks `Aoc.Day01`: it gets `E-TYPE-MISMATCH`, and
  `Aoc.Day01.Proofs`, which uses it, gets `E-NAMESPACE-FAILED`. Undoing
  the edit clears them.
- **Cancellation.** An error edit, then before its check can finish, a
  fixing edit. No diagnostics are ever published for the error's version,
  and the fix's arrive in about one check's time.
- **Latency.** `latency_on_aoc` is ignored by default; run it with
  `cargo test --release -p stitchwort-cli --test lsp -- --ignored --nocapture`.

The AoC tests share a copy of `aoc` in Cargo's test temporary folder, whose
cache is kept between runs.

**Fixed after the merge: nested references.** A record's generated `ext`
lemma (SW-263) is declared at the whole record declaration. Once
something used it, the index gave it a reference covering the whole
declaration, which contained the names written inside it. The
extension's `refAt` is a binary search that assumes references don't
overlap, so what it found at a position depended on the array it
searched. On `type Dial (n: Nat) = …`, at `n`, `check --index` gave the
whole declaration and the server gave the binder. Now the index makes a
declaration's reference to itself only where its name is written there
(`navigation_index`, as for every other reference). The server's lookup
also picks the innermost reference that contains the position.

**Hover over a selection and Expand Selection (SW-293, D523).** The
elaborator's `infer` and `check` entry points each note the type of the
expression they were given, by its span (`note_expr` in
`crates/elab/src/nav.rs`). Like a local variable's type, it is printed at
the end of the declaration, when its metavariables are solved, and an
undone attempt drops what it noted. This costs a printed type per
expression, so it is off unless the server turns it on
(`Elaborator::enable_expression_types`); it has its own check-cache tag
(`+nav+ty`) and entry section (`FORMAT` 5), so a namespace loaded from
the cache has its expression types too. `FileAnswers::exprs` keeps them
for the program's files only (library files have none). The parser drops
parentheses, so a span can start after a `(` (`(a).f x`) or end before a
`)` (`f (x + 1)`). When the index is built, the file is lexed and each
expression is recorded twice if needed: with the parentheses that are inside
it put back, and with a pair around the whole of it too, so that a selection
with or without its parentheses finds the expression. The server trims
whitespace off both ends of a selection (against the text it holds for each
open document) before looking it up.

- **Hover with a range.** `textDocument/hover` may carry `range` beside the
  position (rust-analyzer's convention; the server advertises
  `experimental.hoverRange`). A non-empty range is answered with the type
  of the smallest expression containing it, as a `stitchwort` code block
  whose range is that expression's. With nothing found, or no range, it is
  the ordinary hover. A type under binders is printed in its own context
  (it may name locals); showing the context is not done.
- **`textDocument/selectionRange`**: the expressions containing the
  position, innermost first, then the declarations (outline ranges).
- **VS Code.** `middleware.provideHover` sends the request itself, with the
  selection, when the active selection is non-empty and contains the hover
  position (`hoverRangeParams` in `client.js`, unit tested); otherwise it
  calls `next`. Not run in a real VS Code.
- Tests: `hover_over_a_selection_gives_the_type_of_the_expression` and
  `selection_ranges_walk_outward_through_the_expressions` and
  `hover_over_a_selection_covers_parentheses_and_trims_whitespace`
  (`tests/lsp.rs`),
  `expression_types_come_back_from_the_cache` (`check_cache.rs`), and the
  `hover range` test of `editors/vscode/test/client.test.js`.

### Not done (later, or for the next lane)

- **Shifting ranges** by the edit's line delta between an edit and its
  check (§3.1). Answers can be up to one check old (40 ms in most of
  `aoc`).
- **Memory.** The memory limit with a fresh session (§3.4) isn't built,
  and neither is the "restart server" command (§8). Dropping the marks of
  namespaces that are unlikely to be rewound to would cut the 2× above.
- **Configuration changes.** `stitchwort.yaml` is read when a project is
  first opened. Changing it needs a restart.
- **No dynamic registration** for watched files. Files changed on disk
  while closed are only seen if the client sends `didChangeWatchedFiles`.
- **A file on its own has no check cache**, and loads the library on
  demand.
- **Requests that need fresh state** (goals, completion: stages 2 and 3)
  don't exist yet. Every request answers from published state.
- **§7's replay test**, that any sequence of edits gives what a fresh check
  gives, is covered only by the edit-and-undo cases above.

## Decisions

| ID | Question | Recommendation |
|---|---|---|
| D496 | While you type, what do other namespaces see: your unsaved text, or the saved file? | [**The unsaved text**, and they're re-checked in the background after the edited namespace, so errors you cause elsewhere show up before you save. TypeScript and rust-analyzer do this. Lean and Idris don't (Lean needs "Restart File", Idris checks on save), but our check cache makes re-checking dependents cheap.] |
| D497 | How do you ask for a goal? | [**A new `?` goal hole**, usable anywhere an expression goes. Checking reports an information message at each hole with the local names, their types, and what the hole must be (Agda's holes, shown like Lean's goals). A file with holes doesn't pass `check`. `_` keeps meaning "work it out". Later, a side panel that shows the expected type at the cursor.] |
| D498 | Does the playground get the server? | [**It shares the engine, not the server.** The session layer is a crate with no file or thread access, used by `stitchwort lsp` and by the playground's worker, which keeps a session between requests. No protocol, no server process; the site stays static.] |

Implementation choices made here and not asked: `lsp-server` rather than
`tower-lsp`; one checker thread; rewinding instead of snapshots;
cancellation through `Budget::step`; cache entries written only for saved
text; the extension uses `vscode-languageclient` and the old path is
removed; stage order as in §6.
