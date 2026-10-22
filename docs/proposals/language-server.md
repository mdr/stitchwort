# A language server for Stitchwort

**Status:** design note, 22 October 2026 (SW-31). Nothing here is built.
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
