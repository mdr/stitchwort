# Proposal: code navigation index

**Status:** built (SW-201, D238, 21 October 2026; version 2 with diagnostics and
the library's own references, SW-211, D251). Tooling only, so no external
review. A later language server (SW-31, D239) reuses the same recording.

The compiler resolves every name, but used to throw the answer away. With
`stitchwort check --index` it keeps, for every written name, *which declaration
or binder it refers to*, and writes that as JSON. Editors use it for
go-to-definition and hover; the playground can use it the same way. This note is
meant to be enough to write a client without reading the compiler.

## What is recorded

**References.** For each occurrence of a name in a checked file: its position,
and its target, which is one of

- a *declaration*: a definition, theorem, instance, data type, record,
  interface, constructor, record field, ability or operation. It may be in
  the project or in the standard library;
- a *binder*: where a local variable is bound (a parameter, a `let`, a lambda
  or pattern variable, a local `def`, a handler variable, an `if h :` name).

and the *type* at that occurrence, printed as text, for hover. For a
declaration this is the declaration's own type (a generic function shows its
generic signature, `[a: Type] -> ...`); for a local variable it's the
variable's type where it's used.

Covered: plain and qualified names; names in `import N (a, b)`; dot notation
(`xs.map` points `map` at `Std.List.map`, chosen by the type of `xs`); method
sections and pipes (`|> .f`, `|> f`); constructors in patterns and
expressions; record fields in literals, updates, patterns and projections;
interface methods and instances where a name is written; ability names in
rows and operations in calls and handlers; local `def`s; local variables of
every kind, including `p.name` where `p` is local (the reference is `p`; `name`
is a reference of its own).

Not covered: operators (`+`, `==`, `<`, ... resolve through dictionaries and
have no name written; they have no entries), literals, the names compiler
derivations generate, and import paths (`List` in `import List (map)` is a
namespace, not a declaration). Abilities and their operations have no `type`. Names the elaborator didn't reach because a
declaration failed to check can be missing; locals are found from syntax and
so are present anyway, without a type.

**Definitions.** Every definition in the checked project files (the "outline"):
name, kind, name position, whole-declaration range, and the declaration it
sits in (a constructor or field in its type, an operation in its ability).
Local definitions aren't listed (they are binders).

## Format (`"version": 3`)

```json
{
  "version": 3,
  "errors": false,
  "files": [
    {"path": "Main/Main.sw"},
    {"path": "crates/elab/src/std/List/Toolkit.sw", "std": "List/Toolkit.sw"}
  ],
  "symbols": [
    {"name": "Main.sum", "kind": "def", "file": 0, "range": [2, 4, 2, 7],
     "fullRange": [2, 0, 4, 20], "container": null,
     "type": "(xs: List Nat) -> Nat"},
    {"name": "Std.List.map", "kind": "def", "file": 1, "range": [10, 4, 10, 7],
     "type": "[a: Type] -> [b: Type] -> (f: a -> b) -> (xs: List a) -> List b"}
  ],
  "refs": [
    {"file": 0, "range": [2, 4, 2, 7], "symbol": 0, "type": "(xs: List Nat) -> Nat"},
    {"file": 0, "range": [3, 9, 3, 16], "symbol": 1, "type": "..."},
    {"file": 0, "range": [3, 4, 3, 6], "type": "List Nat",
     "binder": {"name": "xs", "file": 0, "range": [2, 8, 2, 10]}}
  ],
  "diagnostics": [
    {"severity": "error", "code": "E-TYPE-MISMATCH", "message": "type mismatch",
     "file": 0, "range": [3, 9, 3, 16],
     "labels": [{"file": 0, "range": [3, 9, 3, 16],
                 "message": "expected `Nat`, but this has type `Text`"}],
     "notes": []}
  ]
}
```

- `files`: indexed by position; `file` fields elsewhere are indexes into it.
  `path` is relative to the project root (for a single file, as given on the
  command line). A *standard library* file has `std` set to its path under
  `std/` (`core/Data.sw` is one of the core's files), and `path` is its repo-relative location
  (`crates/elab/src/std/...`), which exists only in a checkout of this repo. A
  client without that checkout shows the text from `stitchwort std-source
  <std>` (read-only).
- A **range** is `[startLine, startCharacter, endLine, endCharacter]`:
  **0-based lines, 0-based UTF-16 code-unit characters** (what VS Code's
  `Position` uses), end exclusive. The CLI does the conversion from byte
  offsets, so a client never sees bytes.
- `symbols`: `name` is the full name (`Main.sum`, `Std.List.map`); `kind` is
  one of `def theorem instance type data record interface ctor field ability
  op test`; `range` is the declaration's name, only its last component
  (`length` in `def List.length`; a test's whole description); `container` is
  an index into `symbols`, or `null`, and always present; `fullRange` is
  present for definitions of the checked files. Symbols of the project files
  come first, in source order; those of the library are only the ones
  referenced. `type` may be missing.
- `refs`: sorted by file, then position. Exactly one of `symbol` (index into
  `symbols`; the target is `symbols[i].file/range`) and `binder` is present.
  `type` may be missing. Ranges never overlap each other except that `p.name`
  gives two adjacent ranges.
  A declaration's own name has a ref to its symbol (so hover and definition
  work there), a local variable's binder has a `binder` ref to itself (no
  `type`), and the files of the library that were loaded have refs of
  their own, with the same rules, so navigation continues inside them. (A
  library file's local variables and its names are covered, and the name of
  a declaration something refers to has a ref to itself; its outline is not,
  only the symbols something refers to. The core, `std/core/`, is covered like
  the other files: a session must record from its start, as
  `Session::navigable` does, since the core loads when it is made.)
- `errors`: whether checking reported errors. The index is still written, for
  the parts that were elaborated.
- `diagnostics`: everything checking reported, errors and warnings, in the
  order the compiler reported them: `severity` (`error` or `warning`), `code`
  (`E-TYPE-MISMATCH`), `message` (the main text), `labels` (each `file`,
  `range` and `message`; the first is where the diagnostic is, and `file` and
  `range` of the diagnostic are its range, absent if it has no label), and
  `notes` (plain strings). A label's file may be a library file. An open
  goal, `?`, has `severity` `goal` and code `GOAL`, and two more members
  (below); any diagnostic may have `counterexample`.

### Goals (version 3)

Agents read goals and diagnostics more than anything else
(docs/research/agentic-proving.md T3, §7.3). So a goal comes as data as well
as text. Its label is unchanged: the names in scope a line each, then
`⊢ target`. Beside it:

```json
{"severity": "goal", "code": "GOAL", "message": "in `doubleIsSquare`",
 "file": 0, "range": [2, 50, 2, 51],
 "labels": [{"file": 0, "range": [2, 50, 2, 51], "message": "n: Nat\n⊢ n + n = n * n"}],
 "notes": ["this statement is false; a counterexample:\n  n = 1\n`n + n = n * n` is false:\n  left:  2\n  right: 1"],
 "goal": {"hypotheses": [{"name": "n", "type": "Nat"}],
          "target": "n + n = n * n",
          "lemma": "theorem doubleIsSquareGoal1 (n: Nat): n + n = n * n := ?"},
 "counterexample": {"verdict": "false", "types": [],
                    "bindings": [{"name": "n", "value": "1"}]}}
```

- `goal.hypotheses`: the names in scope, in the label's order: `name`,
  `type`, and `value` for a `let` of data (a `let` of a proof shows only its
  statement). `goal.target`: what must be shown, as after `⊢` (`(the type
  here isn't known yet)` if it isn't). Each is printed as the label prints
  it, so the label is exactly the lines `name: type` (or `name: type :=
  value`) and `⊢ target`. A name shown as `n✝` can't be written there.
- `goal.lemma`, when present: the goal as a declaration of its own, to paste
  at the top level of the same file (after the declaration, in the same
  namespace): `theorem <decl>Goal<i> (h: T) …: target := ?`, or `def` when the
  target is data, not a proposition. `<decl>` is the declaration's name less
  its namespace and `<i>` the goal's place among the declaration's goals,
  from 1 (`goal<i>` in a test). Each hypothesis becomes an explicit
  parameter (an implicit `a: Type` too); a type that starts with a record
  update is put in brackets. Checked, it is a goal with the same hypotheses
  and target (`crates/cli/tests/goal_index.rs` checks this for every lemma of
  `examples/goals/`). It is left out when it might not mean the same at the
  top level:
  - a `let` of data is in scope (the lemma would lose its value);
  - a name can't be written: a hypothesis named `n✝` or `%x`, a compiler-made
    name in the text, or a declaration or constructor the printer names in a
    way the top level can't resolve (`List.count` without `import Std
    (List)`; one shown as notation, `+` or a record update, is fine);
  - it mentions a variable the goal doesn't show (one bound as `_`), or a
    hypothesis's type mentions a later hypothesis (a case split can refine an
    earlier one's type);
  - part of it isn't shown in full (`…`) or isn't known (`?`), or whether the
    target is a proposition wasn't known when the hole was checked.
  The name may already be taken; rename it then.
- `counterexample`: on the diagnostic whose note says the counterexample
  search found one (the first error of a failed theorem, or the goal of a
  proof that is wholly `?`): `verdict` (`"false"`: the statement is false, as
  `check --counterexamples` names it), `types` (each type parameter `name`,
  and the `type` it was tried at, `Nat`), and `bindings` (each input's `name`
  and `value`, as the note shows them). The note itself is unchanged.

On the command line (not in the index), a line of a goal longer than 400
characters is cut in the middle, keeping 200 characters at each end and
saying how many it leaves out: `…[203 characters left out; --full-goals
shows them]…`. `--full-goals` (any command) shows goals in full. The index
always has the whole text.

To go to a definition: find the ref whose range contains the cursor, follow
`symbol` or `binder`. To hover: show the ref's `type` (and `symbols[i].name`).
For an outline: the symbols with `fullRange`, nested by `container`.

## Command line

```
stitchwort check --index FILE.json [targets] [--project DIR]
stitchwort check --index - ...            # to standard output
stitchwort std-source List/Toolkit.sw     # prints an embedded library file
```

Works in project mode and for single files. With `--index -` the diagnostics
still go to standard error, and the JSON alone to standard output. The exit
status is `check`'s, unchanged.

## Playground

`crates/web` exposes the same JSON. `check_index(source)` (one file) and
`check_index_project(paths, texts, targets)` (a project, like
`check_project`) return the index object above with an extra `"ok"` field
(whether checking succeeded), in place of the usual check answer, and
`std_source(path)` returns the text of an embedded library file by the `std`
value of a file entry (empty if unknown). Files with `std` set have no repo
path in the page: show `std_source(std)` read-only, with the same ranges.
Paths are the ones given to the call (`playground.sw` for a single file).
Ranges are the same UTF-16 ranges, which is what a `<textarea>` or
CodeMirror offset counts. A UI is then: map the click position to a ref,
and on click or Cmd-click call the page's `goTo(path, line, column)` (add 1
to the 0-based values), or open the std text for a `std` file.

**Type of a selection (SW-295, D526).** Both calls turn on expression types
(`Elaborator::enable_expression_types`, as the language server does, SW-293),
and the index then has an extra `"exprs"` array: `[file, [l1, c1, l2, c2],
"type"]` for each expression of the program's files (never the library's),
as `nav::index_data_of` builds it, with the parentheses already put back, so
the page does only the lookup (no lexing). The page trims the whitespace off
the textarea's selection and takes the smallest of these ranges that
contains it. That type is shown in the hover tooltip when the pointer is
inside a non-empty selection (it takes the place of the name's), and in a
small `selection: T` pill beside the status line whenever the selection
changes (the mouse, the keyboard, a phone's handles: `selectionchange`),
cleared when it is empty or nothing covers it. A selection in a library file
has none. Cost (native release build, AoC project whole): the index takes
about 2.2 s instead of 1.56 s and is 9.97 MB instead of 8.04 MB (Day 2 with
its tests and proofs: 0.91 s instead of 0.66 s, 5.4 MB instead of 4.8 MB).

## How it's recorded

Off by default: a session opts in (`Elaborator::enable_navigation`), so normal
checking does no extra work. When on, the elaborator notes, at each place it
resolves a written name to a declaration, the name's span and the target (a
map by span, so a declaration elaborated twice records once). A walk over the
syntax of each file (the same scoping rules as the dependency analysis) finds
local variables and their binders and the definitions. Types of local
variables are printed at the end of each declaration, while metavariable
solutions are still known. The index is assembled from these on request.
