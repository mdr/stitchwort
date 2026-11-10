# Refactoring in the editor and playground

**Status:** draft for Matt's review (SW-2626), 10 November 2026; §3.1 updated as built in R2 (SW-2628). Design note
only: no code changed, nothing built or run. Facts were read in the code at
`main` `8250e6579`. Sizes are estimates: S under a day, M a few days, L a
week or more. Nothing here was measured.

**In short.** There is no refactoring today, but most of what rename needs
is already there: references across a project, read-only library files, and
content hashes that leave names out. The references have a handful of gaps
that would make a rename *wrong* (it would silently change what code means),
not just incomplete; those get fixed first. Every refactoring is then checked
before it is applied: the edited text is checked again, and the content
hashes of every declaration are compared with what the refactoring promises
(for a rename of a function, theorem or local: all hashes the same). The
playground runs the same language server in a worker, so whatever is built
in the server reaches it with a small client change. Suggested first build:
rename of locals, hypotheses, functions and theorems, with that check.

## 1. What exists to build on

### 1.1 The pieces

| Piece | Where | What a refactoring gets from it |
|---|---|---|
| References | Elaborator notes each name it resolves (`note_name`, `note_dot`, `note_field`, `note_import`; `crates/elab/src/nav.rs`); a syntax walk finds local binders and uses (`Walk::run`). `driver::nav::Index` (`Ref`, `RefTarget::{Symbol, Binder}`) and `driver::live::FileAnswers` hold them per file | The edit sites of a rename. Uses are matched to their target by location (`Loc`: file and range), so a local's uses and a declaration's uses across files work the same way |
| Find references | `references` in `crates/lsp/src/lib.rs`: every ref in every *checked* file whose target is the same `Loc` | The rename's site list, almost as is |
| Live project | `driver::live::LiveProject`: checks namespaces one at a time, marks the session before each, rewinds to the first changed one on an edit | A trial check of edited text: rewind, check, compare, and keep or roll back |
| Answers at a position | `driver::at` (SW-1116): `reference_at`, `hover_at`, `signature_at`, `goal_at`, `context_at_text`/`context_at_project` (expected type and names in scope at any expression), `actions_from` (`Action { title, range, newText }`) | Free variables with types for extract; the goal and its context for "make this a lemma" |
| Code actions | `code_action`/`code_actions` in `lsp/src/lib.rs`: quick fixes only, one edit per action, in one file. `imports.rs` (add import), `arms.rs` (fill match, case split) | The pattern for small actions. Nothing yet makes an edit across files |
| Missing-import data | `SuggestedImport` on unknown-name diagnostics; `ScopeName::import`; `Elaborator::names_in_scope` | Organise imports, and the "does the new name clash?" query |
| Formatter | `crates/fmt`: layout only, keeps comments and line breaks, re-parses its output and refuses a change of syntax tree (formatter.md §4) | Tidy a generated declaration (range formatting is already served) |
| Content hashes | `stitchwort_core::hash::{def_hash, data_hash}`; docs/core.md "Tests and content hashes" | The oracle (§3). Names are not hashed (not a definition's own, not binders, not locals), but data types are nominal: their names, constructors' and fields' names are |
| Hash tests | `crates/driver/tests/library/fmt_hashes.rs` (every file as written and formatted, same hashes in the same order); `tests/elaboration/pipe_forms.rs` (dot, pipe and prefix calls hash alike) | The harness for refactoring oracles; SW-686 (backlog) generalises it |
| Read-only library | `stitchwort-std:` URIs, and the real std files opened in this repo, are never checked or edited by the server (`notified`, `lsp/src/lib.rs`) | Renames refuse library targets for free |
| Playground | `web/editor/src/editor-entry.js`: CodeMirror 6 with `@codemirror/lsp-client`, on `stitchwort_lsp::Inline` in a worker (`crates/web/src/lsp.rs`) | The same server answers. Its client applies only the first code action, and only edits to the open file |

The server already advertises definition, references, hover, completion,
signature help, inlay hints, semantic tokens, code lenses, document links,
formatting and quick fixes (`capabilities()`), but not `renameProvider`, and
code actions only of kind `quickfix`.

### 1.2 Where references are wrong for a rename

A rename built straight from today's references would write the new name
at each reference. Three kinds of gap: **caught** (the edited text has a new
error, so a re-check refuses it), **silent** (the edited text checks but
means something else), and **corrupting** (the edit lands at the wrong
offset). Only the first is safe to leave for the re-check; the rest must be
fixed before rename ships, or refused.

| Case | Today | A naive rename would | Kind | Fix (size) |
|---|---|---|---|---|
| **Punned record fields**, `{ name }` in a literal or a pattern | The field name and the variable are the same token: a field ref (elaborator) and a local ref (walk) share one span | Rename the field: `{ label }`, now also binding or using `label`. In a pattern the body still says `name`, which is unknown, or *found in an outer scope*. Rename the local: `{ who }`, a field that doesn't exist | silent when an outer name matches; else caught | Expand the pun in the edit: `{ label = name }`, `{ name = who }`. Detect it by equal spans (S) |
| **Import aliases**, `import List (map as each)` | Uses of `each` refer to `List.map` | Write the new name over `each` | silent or caught | Edit only a site whose text ends with the old name; renaming from `each` renames the alias only, in that file (S) |
| **Qualified names**, `List.map`, `Day05.parse`, `f.eq2` | One ref covering the whole written name, to the last component's declaration; the prefix refers to nothing | Write the new name over the whole span, deleting the qualifier | corrupting (text) then caught | Replace only the trailing component (S). The prefix needs refs of its own for type and namespace renames (below) |
| **A type's or namespace's members**, `def Pt.sum`, `Pt.sum p`, `p.sum` | `Pt` in the declaration `def Pt.sum` is a ref to `Pt`; `Pt` in a use `Pt.sum p` isn't | Rename `Pt` to `Point`: the method becomes `Point.sum`, qualified calls still say `Pt.sum` | caught | Treat a type or namespace rename as renaming every declaration under it, editing the prefix of each qualified use (M) |
| **Generated declarations**, `f.eq2`, `f.induct`, `T.induct`, a record's `ext` | Separate symbols, named after the owner | Rename `f`; `rewrite f.eq2` is left behind | caught | Same as the members of a type: rename the subtree (with the previous row) |
| **Named arguments**, `(atLeast := 1)`, `[n := k]`, patterns `VCons [n := k] _ _` | The name is noted as its own binder (`note_parameter`), not linked to the parameter or field | Renaming a parameter misses every named call | caught | Note the name as a use of the parameter's binder in the callee's signature, and `Pattern::Named` the same way (S-M) |
| **`decreasing` measures and parameter defaults** | Not walked (`Walk::signature` walks the type and equations only) | Renaming a parameter misses `decreasing n - i` and `(stop: Nat := start + 1)` | silent if a global has the old name; else caught | Walk both (S) |
| **Doc links**, `` [`name`] `` in doc comments | Links are resolved (`SymbolLink`) but have no ranges, and aren't refs | Leave stale links (a doc-link warning) | caught as a new warning only | Record link ranges as refs (S); the roadmap's row 12 wants them too |
| **Files not checked yet** | `references` reads only checked files (`WorkspaceNav::files`); unchecked namespaces have outlines only | Miss uses in the rest of a big project (`aoc/` has 633 files) | caught by the trial check of the dependants, but slow | Wait for the project to finish checking, saying so (S) |
| **Files that don't parse** | `WorkspaceNav::parsed` keeps the answers of the last text that parsed | Edit at ranges from older text | corrupting | Refuse while any file in the project has `E-PARSE`, and check each answer's text version against the editor's (S) |
| **Names Rust and std's machinery mean**, `registry.rs`, calls built by name (SW-1392) | Std only, which the editor never edits | Nothing in the editor | n/a | A std rename stays a repo change, by hand (SW-1392's guard catches mistakes) |

Checked and fine: names in proofs and tactics are ordinary expressions
(`rewrite p at h in t` walks `p`, `h` and `t`; `omega [e]`, `ring [e]` and
`calc` steps are walked; `cases` names nothing; `induct` arms bind their
names), so locals and hypotheses there are found. Dot calls (`xs.map`) and
field projections are noted by the elaborator at the field's span
(`note_dot`, `note_field`; SW-1114 done). Pipes and method sections go
through the same code (`pipe.rs`). Interface methods implemented in an
instance's record literal are field refs to the interface's field, so they
follow a rename of the method. `unfolding f, g` is noted (`opaque.rs`).

Not checked by reading: whether the walk's scoping agrees with the
elaborator's in every corner (implicitly bound names in signatures, clause
lambdas). The trial check and the hash oracle (§3) cover that whatever the
answer is.

## 2. Candidate refactorings

"Needs" is what the checker or driver must add beyond §1. Every edit goes
through the check of §3 before it's offered or applied.

### 2.1 General

| Refactoring | What the user gets | Needs | Size | Risks |
|---|---|---|---|---|
| **Rename a local or hypothesis** (`let`, parameter, pattern variable, `match h:`, `if h:`) | F2 on any use, every use follows; the most common rename in proofs | The §1.2 fixes for puns, `decreasing`, defaults and named arguments; a clash check (does the new name already mean something at any use?); `prepareRename` | S after the fixes | Capture: the new name shadows or is shadowed. All hashes must be equal, which catches it |
| **Rename a function or theorem** | Safe rename across the project, including dot calls, pipes, `rewrite`, doc links | The fixes for aliases, qualified names, generated declarations, doc links; refuse library targets; wait until the project is checked | M | A dot call can start finding a *different* function with the new name (a field, or another type's). Hashes catch it. Renaming an `export` changes the JavaScript API (Q4) |
| **Rename a field or constructor** | Same, for data | Puns expanded; field refs in record updates and patterns (exist) | M | Derived `Show` prints constructor and field names, so program output changes; JS shapes change. Hashes change by design (nominal), so the oracle compares hashes through the name map (§3.2) |
| **Rename a type or namespace, move a file** | Rename `Pt` to `Point`, `Day5` to `Day05`, with all `Pt.*` members, imports and the file's path | Prefix refs; a project-level edit that renames a file (LSP `RenameFile` in `documentChanges`); namespace line and `import` lines | L | Every dependant re-checks; in `aoc/` that is many namespaces. Projects map namespaces to paths, so a namespace rename is a file move |
| **Organise imports, remove unused** | Sorted, merged `import` lines; unused items gone | A use count per imported item (refs to its symbol from the file, other than the `import` line itself). Today there is no unused-import warning at all | S-M | An import can matter without a written use (an instance found by `auto`, or an ability's operations). Removing it then changes what `auto` finds, which hashes catch |
| **Extract a `let`** | Select an expression, name it, every copy in scope optionally replaced | The selected expression's range (exists: `expr_chain`), the innermost enclosing block | S | Effects: a `let` of an operation runs it once and before the lines after it; extracting from inside a lambda or a branch moves when it runs. Refuse when the expression performs operations, unless it's already at the start of the block |
| **Extract a definition** | Select an expression, get a new top-level `def` with the free locals as parameters, and a call in its place | Free variables of the selection with their types (`context_at` gives the names in scope; needs which are *used* and in what order they depend on each other); a printer whose output parses back | L | Printed types may not read back (implicit arguments, `…` from the print budget, shadowed names). The selection may rely on the value of a `let` above it (the checker knows a `let`'s value in later lines), which a parameter doesn't carry, so the new function fails to check |
| **Inline** | Replace a call (or every call) by the body; delete the definition if no uses remain | Substitution with capture avoidance, in source syntax; a definition by equations inlines only as a `match` | M (a `let` or a one-line `def`); L (equations) | Effects run at a different time; a proof that used the definition's name (`rewrite f.eq1`, `unfold`) breaks. Only offered when the check of §3 passes |
| **Change a signature**: reorder, add, remove, name a parameter, add a default | Every call site updated (positional, named, piped, dot) | The call sites with which argument is which: today's refs give the head only; needs the elaborated spine mapped back to written arguments | L | Pipes and dot calls fill the *first explicit* parameter, so a reorder changes which argument they feed; effectful arguments run in written order, so reordering them changes meaning. Hashes catch both |
| **Switch call style**: dot, pipe, prefix, method section | `List.map xs f` to `xs.map f` to `xs |> .map f`, one action each | The written form of each call (parser), and the receiver's namespace (exists for dot calls) | S-M | The forms are the same term only in the cases `pipe_forms.rs` covers; a pipe's left side runs first, so turning `x |> f (g ())` into prefix keeps the order only when `x` lands first. All hashes must be equal, so an unsafe case is never offered |

### 2.2 For proofs

| Refactoring | What the user gets | Needs | Size | Risks |
|---|---|---|---|---|
| **Rename a hypothesis** | As a local (above): `h` in `match h: e`, `if h: c`, a guard's binder, `rewrite … at h` | Nothing beyond the local rename | S (with it) | The same name is often rebound (`rewrite p at h in t` makes a new `h`); the walk links all of them to the first binder, which is what a rename wants |
| **`?` closed by search into a named lemma** | The proof search's answer, or a goal, becomes `theorem name (hyps…): goal := proof` above the declaration, and a call in its place | `goal_at` (goal and context, exists); which context entries the proof uses; the goal printed as source | M | Printed goals may not read back (implicit arguments, `…`). Only the entries the proof uses become parameters, or the lemma is unreadable |
| **Extract a lemma from a `let`-proved fact or a subgoal** (Stitchwort has no `have`: it's `let h: P := proof` in a block) | `let h: a + b = b + a := …` becomes a theorem whose parameters are the locals that `P` and its proof use, and `let h := lemma a b` | Extract-definition's machinery, for a proposition; the parameter list from the free locals of `P` *and* the proof | M (given extract definition) | The proof may rely on facts the context computes (a `match` refining a variable, a `let` the checker unfolds) that don't carry over to a top-level lemma; refuse then, naming the dependency |
| **Generalise** | Replace a term in the goal by a new parameter (`n + 1` into `m`), with an equation if asked | The occurrences in the goal (kernel term to written text: hard), and an edit to the signature | L | Rarely mechanical in source; the term may also appear hidden in implicit arguments. Later |
| **Turn `cases`, `omega` or search into the written proof** | See and edit the proof a tactic found | The tactic's found term printed as source (search already does this for `?` via `paste_text`) | M | Large, unreadable terms (`folded-calls.md`: implicits are most of a proof term) |

## 3. Correctness

### 3.1 The trial check

Every refactoring produces a set of text edits (possibly in several files)
and a **promise** about hashes (§3.2). Before the edit is offered (for cheap
ones) or applied (for the rest), the server runs a **trial**. Built in R2
(SW-2628) as `LiveProject::trial(edits, promise)` in
`crates/driver/src/live/trial.rs`, so the playground's server has it too:

1. **Refusals.** The trial refuses at once, with no way to go ahead, when
   the edits could land in the wrong place or there's nothing to compare
   with: the project isn't fully checked (`NotChecked`), it can't be checked
   at all (`CantCheck`: a file without a namespace line, an import cycle), a
   file has `E-PARSE` (`Unparsed`), an edit is to a library file
   (`Library`), or an edit doesn't fit the text (`BadEdit`: a file not in
   the project, a range past a line's end, overlapping edits). Q2's
   exception for a local rename inside one declaration isn't made: a
   refusal is the orchestrator's call, reversible.
2. **Check.** The edits are applied to the project's texts (the old texts
   kept), and `LiveProject` rewinds to the mark before the first changed
   namespace and checks from there to the end. That re-checks every later
   namespace, not only the dependants; with a check cache, those that don't
   depend on the change replay from it.
3. **Compare.** The result is a **problem list**, not a verdict:
   - **New diagnostics**, each with its file, range, code, message and the
     declaration it's in. Diagnostics are compared by file, code and
     declaration (renamed through the promise), counting each, so those
     already there stay allowed (a project with an unfinished `?` can still
     rename), errors *and* warnings, so a stale doc link counts.
     `E-NAMESPACE-FAILED` is left out: it only says a namespace used has
     errors, which are listed themselves.
   - **Declarations whose meaning changed** but which still check: their
     hash isn't the one the promise says. Each has its file and range (of
     its name, in the edited text), because no error will ever point at
     it. One that uses another changed declaration says so (`uses`), and
     those that use none come first: they're where to look. Generated
     declarations (`f.eq1`) aren't listed beside their owner. Only
     namespaces checked cleanly both before and after are compared; a
     namespace with errors now has them among the new diagnostics.
4. **Finish**, either way:
   - **Keep** (`LiveProject::keep`): the checked state stays, so applying
     costs no second check. With an empty list that's the normal case;
     with problems it's **apply anyway** (D3467): the edit goes in and the
     user or agent fixes the few problem spots by hand, from the list.
   - **Restore** (`LiveProject::restore`): the old texts go back and are
     checked again (the session's journal can only go back, so the state
     before is rebuilt, from the check cache where there is one). The
     diagnostics and answers are then those from before.

The wording, for `doing` = "renaming `h` to `n`" (`Problems::describe`,
`Refusal::describe`):

- "renaming `h` to `n` would change what `step` means (src/Day05.sw,
  line 12)", with ", because it uses `cap`" when that's why;
- "renaming `h` to `n` would cause an error in `step` (src/Day05.sw,
  line 12): unknown name `h`";
- "can't check renaming `h` to `n`: `src/Day07.sw` doesn't parse (line 3)";
  "can't check renaming `h` to `n` yet: the project is still being
  checked"; "renaming `map` to `each` would change `List.sw`, which is in
  the standard library and can't be changed here".

The trial can't say which name changed meaning inside `step` (the hash
covers the whole declaration), so the message names the declaration, not
the name inside it.

The cost is a check from the first changed namespace on. Measured in
SW-2628, one run each (`trial_timings_on_aoc` in
`crates/driver/tests/projects/trial.rs`, run by hand), on part of `aoc/`:
`Aoc.Common` and the 2021 days, 177 files in 75 namespaces, with a warm
check cache, on Speedwell:

| Edit | Trial | Restore |
|---|---|---|
| Rename `lines` in `Year2021.Day05.main` (3 edits) | 1.7 s | 1.6 s |
| Rename `range` in `Aoc.Common`'s `Range.size` (3 edits) | 8.9 s | 4.8 s |

Both found no problems, as they shouldn't. The local rename costs more than
its one namespace because every namespace checked after Day05 is rewound
too and replays from the cache. For the whole of `aoc/`, where 167 files
import `Aoc.Common` against 47 here, a Common rename is estimated at about
30 s (scaled by importers, not measured).

### 3.2 What hashes promise

Names don't take part in hashes, except a data type's, its constructors' and
its fields' (docs/core.md). So:

| Refactoring | Promise |
|---|---|
| Rename local, hypothesis, function, theorem; switch call style; organise imports; reformat | Every declaration's hash unchanged, matched by position in the namespace and by the rename map for names. Strongest: any change of meaning shows |
| Rename field, constructor, type | Hashes equal when computed with the old names put back for the renamed data: a hash function that takes a name map (`data_hash` with a substitution, S-M) |
| Extract `let` | The enclosing declaration's hash unchanged when the `let` is of a pure value (whether a pure `let` elaborates to the same term as its inlined value is to be checked in R6); otherwise as for extract definition |
| Extract definition or lemma; inline | The changed declarations' *types* unchanged, the new one's body is the selection, and for a definition (not a theorem) the old and new bodies are convertible: the trial adds `theorem _: oldBody = newBody := rfl` to a scratch copy, which the kernel checks with unfolding. For a theorem only its type matters (proof irrelevance) |
| Change a signature | No hash promise (the type changes): diagnostics only, and the tests of the project still pass, which the trial can run when they're cached |

Theorems whose proof body changes do change their hash, and so does
everything hashed after them (a reference is hashed as the target's hash).
That costs re-run tests, not correctness; it's expected for proof
refactorings.

### 3.3 Testing with an oracle

The same promises, run in bulk, are the test suite:

- **Rename everything.** For each accepted example and each project, rename
  every local, hypothesis, function and theorem in turn (or a sample) to a
  fresh name through the refactoring code, and check the promise. This is
  SW-686's "local renames" with the real rename as the rewriter, which is
  what makes it a test of the refactoring rather than of the elaborator.
  Pairs with `fmt_hashes.rs`, whose harness (load, list hashes by position)
  it reuses.
- **Round trip.** Rename `a` to `b` then `b` to `a`: the text is the same
  as before, byte for byte. Cheap, and catches edits at wrong offsets.
- **Every style.** Each call in the examples converted to each other style
  it allows: hashes unchanged (generalises `pipe_forms.rs`).
- **Extract and inline back.** Extract every `let` and subexpression of a
  sample, then inline it: same hash as the start.

Size of these runs: like `fmt_hashes`, a full pass over every example is a
daily or full tier test; a lane runs it on a filter (`FMT_HASHES=<text>`
style). Unit tests per refactoring use small fixtures, one per row of §1.2.

## 4. The playground and library limits

**Standard library.** Read-only in both surfaces: a rename whose target is
a std declaration is refused at `prepareRename` with "the standard library
can't be renamed here". A user can still rename their *own* alias of it
(`import List (map as each)`). Renaming std itself stays a repo change made
by hand, because Rust code and the registry name std declarations
(`registry.rs`, SW-1392), and docs and the guide mention them.

**A project's own users.** A project's tests are `test` declarations in its
own files, so they're in the rename. What lies outside the project isn't:
in this repo, renaming a declaration in `aoc/src/Aoc/Common` reaches the AoC
days (same project), but not the AoC notes (`NOTES-*.md`), the guide, or
other projects; nothing imports across projects today. The rename can list
textual mentions in the project's other files (comments, `.md` files next to
it) as a warning, without editing them.

**The playground.** It runs the same server (`stitchwort_lsp::Inline`) in a
worker, so rename, organise imports and the code actions come from the same
code. What its client needs:

- F2 with a name prompt, and applying a `WorkspaceEdit` to every file of a
  bundled project (today `codeAction` applies only the first action, and only
  to the open file). `@codemirror/lsp-client` has a rename command; whether
  its version (`^6.3.0`) applies edits to files that aren't open, through
  the page's `project.texts`, is to be checked (from memory, not verified).
- A menu of code actions instead of "apply the first".
- Your own code in the playground is one file or a bundled project kept in
  the browser, so a rename can't reach anything else.
- The trial check runs in the worker, as checks already do; on a large
  bundled project (AoC) it may take seconds. Same refusal rules.

## 5. Suggested order

1. **R1, the reference fixes that make rename wrong** (§1.2: puns, aliases,
   qualified names' last component, `decreasing` and defaults, named
   arguments), each with a fixture whose references are checked. Needed by
   every rename, and it improves find references today.
2. **R2, the trial check** (`LiveProject::trial` and the hash promise for
   names) in `crates/driver`, with the refusal messages. Measure its time on
   `aoc/` for a local and a Common rename.
3. **R3, rename of locals, hypotheses, functions and theorems** in the LSP
   (`prepareRename`, `rename`) and the playground client (F2, multi-file
   edits, action menu). This is the first visible result.
4. **R4, the rename oracle tests** (§3.3: rename everything, round trip), in
   the daily tier.
5. **R5, organise imports and unused imports**, and **switch call style**:
   small, hash-identical, built on R2.
6. **R6, `?` to a named lemma** and **extract a `let`**: the cheapest proof
   wins, on `goal_at`.
7. **R7, rename of fields, constructors, types and namespaces** (hash with a
   name map, prefix refs, file moves).
8. **R8, extract definition and lemma**, then **inline**; **change a
   signature** and **generalise** last.

### Tickets to file

| Ticket | Title | Model | Estimate |
|---|---|---|---|
| R1 | References a rename can trust: punned fields, import aliases, qualified names, `decreasing` and default expressions, named arguments and `[n := k]` patterns linked to their parameter, doc link ranges | Sonnet | 1 day |
| R2 | A trial check for edits: `LiveProject::trial` (rewind, check, compare diagnostics and hashes by a rename map, keep or restore), with timings on `aoc/` | Opus | 1.5 days |
| R3 | Rename (locals, hypotheses, functions, theorems) in the server and the playground: `prepareRename`, `rename`, F2, multi-file edits, a code action menu | Sonnet | 1.5 days |
| R4 | Rename oracle tests: rename every name of the examples and projects (sampled), hashes unchanged; round trip; in the daily tier (generalises SW-686's local renames) | Sonnet | 1 day |
| R5a | Organise imports, and remove unused ones (with Q3's warning if chosen) | Sonnet | 1 day |
| R5b | Code actions to switch a call between dot, pipe, prefix and method section, offered only when hashes stay the same | Sonnet (or DeepSeek once set up) | 1 day |
| R6 | A `?` closed by search, or any goal, into a named lemma; extract a `let` | Opus | 2 days |
| R7 | Rename fields, constructors, types and namespaces, with file moves; data hashes through a name map | Opus | 3 days |
| R8 | Extract a definition or lemma with its free locals as parameters; inline | Opus | 1 week |

## 6. Open questions for Matt

- **Q1: first build.** Build R1 to R4 (rename of locals, hypotheses,
  functions and theorems, with the trial check and its oracle tests) before
  any other refactoring? **Recommendation: yes.** It's the most used
  refactoring, the trial check it needs is the base of all the others, and
  it's about a week in all (estimated).
- **Q2: when the check can't run.** If the project has a file that doesn't
  parse, or hasn't finished checking, should rename refuse, or go ahead with
  a warning? **Recommendation: refuse, saying why** ("`Day07.sw` doesn't
  parse"); except a local rename inside one declaration, whose sites are all
  in one file and whose check is that file's namespace.
- **Q3: unused imports.** Add a warning, `W-UNUSED-IMPORT`, to `check` (a
  user-visible message, documented in the guide), with organise imports as
  its quick fix; or offer only the editor action? **Recommendation: the
  warning and the quick fix.** The CLI and the playground then show it too,
  and std and `aoc/` get tidied once.
- **Q4: renames that change behaviour.** Renaming a constructor, a field or
  a type changes derived `Show` output (`"${shape}"` prints constructor
  names) and the JavaScript shape of exported types, and renaming an
  `export`ed function changes its JavaScript name. Offer these with a note
  listing what changes, or refuse? **Recommendation: offer, with the note**
  ("`Show` output and the exported JavaScript change: `Circle` becomes
  `Disc`"). A rename that only changes names stays meaning-preserving for
  the checker and the proofs; what changes is output, which the user can
  judge.
