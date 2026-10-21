# Proposal: code navigation index

**Status:** built (SW-201, D238, 21 October 2026). Tooling only, so no external
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

## Format (`"version": 1`)

```json
{
  "version": 1,
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
    {"file": 0, "range": [3, 9, 3, 16], "symbol": 1, "type": "..."},
    {"file": 0, "range": [3, 4, 3, 6], "type": "List Nat",
     "binder": {"name": "xs", "file": 0, "range": [2, 8, 2, 10]}}
  ]
}
```

- `files`: indexed by position; `file` fields elsewhere are indexes into it.
  `path` is relative to the project root (for a single file, as given on the
  command line). A *standard library* file has `std` set to its path under
  `std/` (`core.sw` is the core), and `path` is its repo-relative location
  (`crates/elab/src/std/...`), which exists only in a checkout of this repo. A
  client without that checkout shows the text from `stitchwort std-source
  <std>` (read-only).
- A **range** is `[startLine, startCharacter, endLine, endCharacter]`:
  **0-based lines, 0-based UTF-16 code-unit characters** (what VS Code's
  `Position` uses), end exclusive. The CLI does the conversion from byte
  offsets, so a client never sees bytes.
- `symbols`: `name` is the full name (`Main.sum`, `Std.List.map`); `kind` is
  one of `def theorem instance type data record interface ctor field ability
  op test`; `container` is an index into `symbols` or `null`; `fullRange` is
  present for definitions of the checked files. Symbols of the project files
  come first, in source order; those of the library are only the ones
  referenced. `type` may be missing.
- `refs`: sorted by file, then position. Exactly one of `symbol` (index into
  `symbols`; the target is `symbols[i].file/range`) and `binder` is present.
  `type` may be missing. Ranges never overlap each other except that `p.name`
  gives two adjacent ranges.
- `errors`: whether checking reported errors. The index is still written, for
  the parts that were elaborated.

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

## How it's recorded

Off by default: a session opts in (`Elaborator::enable_navigation`), so normal
checking does no extra work. When on, the elaborator notes, at each place it
resolves a written name to a declaration, the name's span and the target (a
map by span, so a declaration elaborated twice records once). A walk over the
syntax of each file (the same scoping rules as the dependency analysis) finds
local variables and their binders and the definitions. Types of local
variables are printed at the end of each declaration, while metavariable
solutions are still known. The index is assembled from these on request.
