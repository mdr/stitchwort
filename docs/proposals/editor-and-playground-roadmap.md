# Editor and playground roadmap

**Status:** draft for Matt's review (SW-1111, D2237), 3 November 2026. Design
note only; tickets follow once the order and the open questions at the end are
settled. Facts below were read in the code at `main` `bfa58a2c` (nothing was
built or run). Sizes are estimates: S under a day, M a few days, L a week or
more.

## 1. What exists today

**VS Code and the language server** (`editors/vscode`, `crates/cli/src/lsp.rs`,
`crates/driver/src/{live,nav,search_at}.rs`). The server (`stitchwort lsp`)
re-checks the edited namespace on each change and publishes diagnostics. It
answers: definition (including into read-only `stitchwort-std:` library
files), hover (type, signature, doc, generated equations, defaults used),
references, document and workspace symbols, selection ranges, document and
range formatting, quick-fix code actions (what closes a `?`, from
`search_at`), and completion of named-argument names inside `(` and `[`
(`completion.rs`, from the signature of the called function; no completion of
names). One custom request, `stitchwort/goalAt`, feeds the "Show Goals"
webview, which follows the cursor but shows only goals the checker already
published (a `?` hole, not "the context at any cursor"; lsp-goal-holes.md
§8.4). The extension's only command is Show Goals.

**Playground** (`web/index.html`, `web/playground-worker.js`, `crates/web`).
A `<textarea>` over a regex-coloured `<pre>`; no editor component. The
compiler runs in a worker, one stateless request per check (`check`,
`check_index`, `test`, `evaluate`, `extract`, `format`, `run`, live-key runs,
plus project variants), re-sent 250 ms after typing stops, with the worker
terminated to cancel. Tabs for Check, Tests, Evaluate, JavaScript, Run; a Goals
list (open `?`s with a jump button) above the errors; Cmd-click definition
(also into library text), find references, a hover tooltip with the type
(expression types come from `enable_expression_types`), formatting, a dropdown
of examples and the bundled AoC and roguelike projects (file tabs, reset), and
the Guide (`web/guide/*.sw`, 29 chapters). Links reach the examples, AoC days
and guide chapters (`#example/…`, `#aoc/…`, `#guide/…`); your own code is kept
in `localStorage` only. Not offered: completion, search, code actions, sharing
your own snippet, a cursor-following goal panel, explanations of error codes.
The playground does not use `driver::live` (no incremental session), and
`crates/web` does not expose `search_at`.

**Shared base.** Both surfaces consume the same recorded facts: the
navigation index (`nav::Index`: refs with target, type, defaults; symbols with
doc and signature; expression types), diagnostics, and the `?` goal text.
They get them by different routes (LSP: `LiveProject`; playground:
`check_index`), so each feature below is built twice unless it lands in
`crates/driver` as a function over `Session` that both call.

## 2. Candidate features

"Has" is what to build on; "Needs" is what the checker or driver must add.
LSP = VS Code; PG = playground.

| # | Feature | User gets | Has | Needs | Surf. | Size | Depends |
|---|---|---|---|---|---|---|---|
| 1 | **Name completion** (locals, scope, after `.`, `Ns.`; auto-import) | Writing without the library open in another tab | `completion.rs` (named args only); `dot.rs` knows which namespaces a receiver reaches; `scope.rs` knows the import a name needs; `FileAnswers` has refs/outline | The broken text does not parse (`xs.`). Needs the dummy-name trick from language-server.md §5.3 (check a copy with `xs.zzzz`, record receiver type and local scope there, rewind), and "context at a position" (see 2). Verify: does the parser keep going after `xs.`? | both | L | 2 |
| 2 | **Context at a position** (expected type and locals at any cursor, not only at `?`) | Lean-style infoview that works everywhere; basis of 1, 3, 4, 8 | Goals text and `goalAt`; nav recorder prints local types per declaration | An elaborator probe: record expected type plus local context for the expression covering a position, as the goals code does for `?`. lsp-goal-holes.md §8.4 marks it deliberately not built | both | M | none |
| 3 | **Live goals panel in the playground** | Same follow-the-cursor goals as VS Code | Goals list in the output; `goal_at`'s parsing of the message | Move `goal_at` (finding the goal, splitting context) from `lsp.rs` into `driver`; return structure in the diagnostic rather than parsing the text (§8.4 caveat 3); worker action `goalat` | PG | S-M | 2 for non-`?` positions |
| 4 | **Case split / fill match / `match induct` skeleton** | One keystroke writes the arms | `search_at` produces proofs to paste (`paste_text`); `induct_match.rs`, `cases.rs`; E-NONEXHAUSTIVE (`families.rs`, `lib.rs`) lists what is missing | A structured "missing cases" payload on E-NONEXHAUSTIVE (constructor names and arity, not English); case split needs the variable's type at the cursor (item 2) and a printer for constructor patterns with fresh names | both | M each; fill-match is S given the payload | 2 (split) |
| 5 | **Lemma search from a goal** | "What closes this?" including lemma suggestions, in the editor | Already built for quick fixes: `search_at_text`, `search_at_project`, class "applicable/…" results; `stitchwort search` | LSP shows only the first few as quick fixes. PG cannot call it: `crates/web` does not expose `search_at` and has no search index (needs the library theorem index built at wasm build time, or on first use; check size and time budget in the worker) | LSP done in part; PG missing | S (LSP list/command), M (PG) | 3 |
| 6 | **Rename** | Safe rename across the project | `references` (one ref set per target); library files read-only | A workspace edit built from refs, refusing library targets and clashes with existing names in scope (a scope query: does the same name resolve differently after rename?); `prepareRename` | LSP; PG later | M | none |
| 7 | **Add / organise imports** | Fix "unknown name" with one click; sort and prune imports | Slim prelude errors already know the missing import (scope.rs); the formatter | A machine-readable `fix: {addImport}` field on the diagnostic (language-server.md §5.4); "unused import" needs a use count per imported name (refs give it) | both | S-M | none |
| 8 | **Signature help** | Parameter names and defaults while typing a call | `LiveRef::signature`, `completion::call_at`, `completion::parameters` (named-arg completion already does the parsing) | Only protocol plumbing plus the active parameter; no checker change | LSP; PG tooltip | S | none |
| 9 | **Inlay hints** (types of `let`s, filled-in hidden arguments) | See what the checker inferred | Expression types and `defaults` recorded; `LiveRef` | Hidden arguments: does the elaborator record solved implicit arguments at the call head? Not in `nav::Ref` today; `folded-calls.md` says they are 70-80% of proof terms, so default off. `let` types need only a ref at the binder (exists) | both | S (lets), M (implicits) | none |
| 10 | **Semantic tokens** | Colour by meaning (constructor, theorem, local) | refs carry kind (`def`, `ctor`, `local`); TextMate grammar stays | Protocol plumbing and the token legend. PG: its colouring is regex (`web/tests/colour.test.mjs`); semantic colours would need a token list in the index | LSP; PG optional | S | none |
| 11 | **Test Explorer and code lenses** (run main, run test, audit theorem) | Run and see results in the sidebar; "audit" next to a theorem | `test` outline items; `stitchwort test` with result cache; `driver::audit`, `run.rs` | A list of tests per file with ranges (outline has them), and a driver call that runs one test by name and returns pass/fail plus message, out of process. Library tests (SW-1113) are outside the project, so Explorer covers project tests only | LSP; PG has a Tests tab | M | none |
| 12 | **Doc links, `[`name`]` clickable** | Jump from a doc to the item | `SymbolLink` (text and target) in the index; links checked by `doc_links.rs` | Hover markdown rendering of links to `file:` or `stitchwort-std:` URIs; document links in the file's own comments need ranges (not recorded) | both | S | none |
| 13 | **Go to implementation / call hierarchy** | Instances of an interface; callers and callees | `RefTarget` links uses to declarations (callers = refs grouped by enclosing outline item) | Instance-to-interface relation: an index of which `instance` implements which interface method. Call hierarchy over refs is S-M | LSP | M | none |
| 14 | **Extract / inline definition** | Refactor without hand-editing | Formatter; refs | Free-variable analysis of an expression, with types, to write the new signature; inlining must respect the checker. Hard to make correct for proofs | LSP | L | 2 |

### Playground-specific

| # | Feature | Notes | Size |
|---|---|---|---|
| P1 | **Share a snippet by URL** | Link carries the source (compressed into the fragment, no server). The `#example/…` router already exists. Limit the length, warn when long | S |
| P2 | **A real editor component** (CodeMirror 6, or Monaco) | The textarea-plus-overlay cannot host completion menus, signature help, inlay hints, squiggles or multi-cursor, and it fights mobile keyboards. Everything in 1, 8, 9, 10 is cheaper after this. Needs a build step or a vendored bundle (the page is a single static file today); a size/offline decision is Matt's | M-L |
| P3 | **Inline diagnostics** | Squiggles and gutter marks at error ranges rather than only in the output tab. Ranges are already in the JSON | S (after P2, S-M before) |
| P4 | **Persistent worker session** | Today every request re-loads the session. Keeping it between requests (language-server.md §5.7) is the route to completion and fast re-checks; cancellation stays by terminating the worker. Depends on whether `driver::live` is wasm-clean | M-L |
| P5 | **Runnable guide examples** | Guide chapters are `.sw` files shown as text; make each code block runnable or openable in the editor with one click, with a check that every chapter still passes | S-M |
| P6 | **Error code explanations** | Diagnostic codes (`E-…`) link to a page; `docs/errors` content exists in `errors.md` | S |
| P7 | **Mobile layout** | Narrow layout exists for the guide only; needs the editor/output split to stack, and P2's touch behaviour | S-M |
| P8 | **Browser matrix** | SW-47 (Firefox, Safari) and SW-82 (stack guard) are open and decide whether a public launch is safe | S |

## 3. Shared work

One change serves both: **make `crates/driver` the single home for "answers
at a position"**. Today `goal_at`, hover assembly (`hover` in `lsp.rs`),
`completion::call_at`, and the quick-fix builder live in the CLI crate, and
the playground has its own JS equivalents (`targetOf`, `navtip`). If the
driver exposes `Session`-level functions (`goal_at`, `context_at`,
`signature_at`, `hover_at`, `actions_at`) returning plain structs that both
serialise (LSP to lsp-types, `crates/web` to JSON), each feature of items 2-9
is done once plus two thin adapters. This also means diagnostics carry
machine-readable payloads (`fix`, missing cases, goal context) instead of
English that a client re-parses. **Open check:** whether `driver::live`
(`LiveFile`, `LiveProject`) builds for wasm32; `crates/web` does not use it,
and the thread and file access it assumes is unverified.

**As built (SW-1116, 4 November 2026).** `crates/driver/src/at.rs` is the home
of the answers, as functions over `FileAnswers` or a `Session` returning plain
serde structs: `goals_of`/`goal_at` (`Goal`, `Local`), `reference_at`,
`hover_at`/`hover_of` (`Hover`), `signature_at` (`Signature`, with the moved
`completion.rs`), `actions_from`/`actions_at_text`/`Session::actions_at_project`
(`Action`, `action_options`), the text helpers (`offset_at`, `position_at`,
`word_at`, `trimmed`) and `Session::context_at_text`/`context_at_project`
(`Context`). The goal now comes from the diagnostic's `GoalData`
(`LiveDiagnostic::goal`), not from re-parsing its message. `lsp.rs` is the
adapter: `stitchwort/goalAt` and the code actions answer from these structs,
and the new request `stitchwort/contextAt` (a custom request, not hover: hover
is about the name under the cursor, and the payload is structured) runs on the
search threads. Context at a position is an elaborator probe
(`Elaborator::probe_context`, `goals.rs`): `note_expr` offers each expression
to the probe, which keeps the smallest one containing the offset with its type
and the names in scope, printed at the end of the declaration with the goals,
so the list is the one a goal shows. It costs a check of the file (the file's
namespace is not replayed from the check cache). Limits: positions in
signatures, patterns, comments and declarations that do not parse have no
expression, so no answer; the probe is not yet kept by the live session, so
each request re-checks (the persistent-session step, P4, removes that). Not
done here: `crates/web` still has its own JS equivalents.

Known LSP gaps already filed: **SW-1113** (names in library test bodies do
not navigate; library tests are not elaborated on load, so it also limits
Test Explorer for library files, and is cheapest after item 2 as the probe
could elaborate on demand), **SW-1114** (field projections on locals do not
navigate in library files; not checked in program files, which should be done
before rename (6), because rename that misses projections is wrong, not just
incomplete).

## 4. Suggested order

1. **Shared driver API for position answers** (section 3), then **context at
   a position** (2). Unlocks 1, 3, 4, 9 on both surfaces, and removes the
   LSP-only parsing. M.
2. **Signature help (8), add import fix (7), `let` inlay hints and semantic
   tokens (10)**: all S, no checker work beyond a diagnostic field; quick,
   visible wins and they exercise the new API. Do 7 first: unknown-name
   errors are the commonest beginner failure.
3. **Goals panel in the playground (3) and share-by-URL (P1)**: the two
   cheapest things that make the public playground feel like a proof tool;
   both S-M.
4. **Fill match and case split (4)**: the best proof-writing gain per unit
   work, since `search_at` already provides the paste machinery; start with
   fill-match from E-NONEXHAUSTIVE.
5. **Editor component for the playground (P2) with inline diagnostics (P3)**:
   the gate for completion, signature help and hints in the browser; schedule
   after Matt decides the dependency question.
6. **Name completion (1)**: the largest win for both surfaces but the largest
   cost; do it once 1-5 are in, on top of context-at-position and a
   persistent session (P4).
7. **Test Explorer and code lenses (11), rename (6)** after checking SW-1114
   on program files.
8. Later: lemma search in the playground (5), go to implementation, call
   hierarchy, extract/inline, mobile, explained errors.

Reason for the order: proof writing is the product's reason to exist, so
goals and proof skeletons come before general-purpose conveniences, but the
shared API comes first because every later item is then half the cost.

## 5. Open questions for Matt

1. May the playground take a third-party editor component (CodeMirror 6 is
   about 150-300 kB minified for a minimal setup; an estimate, not measured),
   or must the page stay a single file with no dependencies?
2. Is the playground a public launch target soon (then P8, P1, P6 move up),
   or mainly a tour (then P5 moves up)?
3. Should completion in the playground wait for a persistent worker session,
   or is an approximation from the last good index acceptable?
4. Inlay hints for hidden arguments: worth recording solved implicits in the
   index, given the noise in proofs, or restrict hints to `let` types?
5. Test Explorer: project tests only, or also run library tests (SW-1113)?
6. Should the tickets be one per row of section 2, or grouped (1+2 as one
   lane, the S items as a sweep)?
