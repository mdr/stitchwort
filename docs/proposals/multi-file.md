# Proposal: programs in several files

**Status:** draft 1, 19 October 2026. Design only, nothing is built. It
waits for the user and an independent review
([§12](#12-questions-for-the-user), [§13](#13-questions-for-the-reviewer)).

This note can be read without knowing the codebase. §2 describes what exists
today, checked against the source at commit `f604c41`, with file and line
references. Claims about other languages cite their sources
([Sources](#sources)). Anything not checked against a source is marked
**unverified**.

## Contents

0. [Summary](#0-summary)
1. [What the user wants](#1-what-the-user-wants)
2. [What exists today](#2-what-exists-today)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design)
5. [Tests and proofs next to what they're about](#5-tests-and-proofs-next-to-what-theyre-about)
6. [What `aoc/` would look like](#6-what-aoc-would-look-like)
7. [Errors](#7-errors)
8. [Hashing and caching](#8-hashing-and-caching)
9. [The CLI, the playground and JavaScript](#9-the-cli-the-playground-and-javascript)
10. [`include "file"`](#10-include-file)
11. [Stages](#11-stages)
12. [Questions for the user](#12-questions-for-the-user)
13. [Questions for the reviewer](#13-questions-for-the-reviewer)
- [Sources](#sources)

## 0. Summary

**In plain words.** A program can be split over several `.sw` files. A file
uses another with the `import` it already uses for library namespaces:

```
-- aoc/day05.sw
import Range (Range)

def solvePart2 (ranges : List Range) : Nat := … r.size …
```

`import Range (Range)` finds the file `Range.sw` at the top of the project,
checks it first, and makes its `Range` usable here. Its functions are
reached the usual ways: `Range.parse t`, or by dot notation, `r.size`. A
file only sees the files it imports. Files can't import each other in a
circle. `stitchwort run`, `test` and `check` take a file and follow its
imports.

**The decisions, each with a recommendation.**

| | Decision | Recommendation |
|---|---|---|
| D1 | What is a file? | **A file is a module, and its path is a namespace** (`aoc/Lib/Grid.sw` is `Lib.Grid`), as in Agda, Haskell, Idris, OCaml and Rust. This is what [namespaces.md §8](namespaces.md#8-extending-it-later-without-breaking-anything) reserved. The alternative, Lean's "files and namespaces are unrelated", is §4.1's main alternative. |
| D2 | How are files found? | **From the project root**: the nearest directory above the file with a `stitchwort.toml` (empty for now), or else the root file's own directory. `import Lib.Grid` means `<root>/Lib/Grid.sw`. A file that's imported has a capitalised path, since namespace components are uppercase. |
| D3 | What does `import` do with a file? | **It loads it, then works exactly as for a library namespace** (namespaces.md D3). Two new forms: `import Lib.Grid` alone (load, use with a qualifier), and `import Lib.Grid (..)` (everything; reserved in namespaces.md §8). Both are parse errors today. |
| D4 | Which names does a file see? | **Its own, the library's, and those of the files it imports directly.** Not its imports' imports, and never a file it doesn't import. One exception: dot notation always finds functions declared in the same file as the value's type (§4.4). |
| D5 | Cycles? | **Refused** (`E-IMPORT-CYCLE`), as in Lean, Agda, Idris, OCaml, Haskell (without boot files) and Gleam. Within one file, any order still works. |
| D6 | Can a file add to another file's namespace (`theorem Range.mergeDisjoint` in a proofs file)? | **Not at first** (`E-FOREIGN-NAMESPACE`, the same rule as `E-STD-NAMESPACE`). Theorems and tests about another file's definitions are fine anywhere; only their *names* stay in their own file. Allowing it later is compatible (§4.6). A question for the user (Q3). |
| D7 | Which proofs does `auto` see? | **The current file's (above the use), the library's, and everything the file imports, directly or not.** Never a file outside that set, so `auto`'s answer can't depend on which other files happen to be loaded. |
| D8 | Identity and hashes | A file's **logical name** is its path from the project root (`Lib.Grid`), never where the project sits on disk. Data types hash it (`Lib.Grid.Grid`), as DESIGN §11 already says. Definitions still don't hash names, so moving a definition between files changes no hash; moving a *type* does. |
| D9 | CLI | `run`, `test`, `eval`, `repl` and `build` take one root file and follow its imports. `check` takes files or directories. `test` runs the tests of the root and of every project file it imports, grouped by file, using the cache as now. |
| D10 | Playground | **One file, as now.** Importing a project file is `E-IMPORT-UNKNOWN` with a note saying the playground has no files. The driver reads files through an interface, so a later playground can offer several tabs. |
| D11 | JavaScript | `build --js` exports the root file's `export`s only; everything they use, from any file, goes in the one generated module, as now. `run --js` is unchanged. |
| D12 | `include "path"` | Path relative to the file that contains it; the contents are part of the definition's hash, the path isn't. Independent of the rest; can be built before or after. |

**Smallest useful stage** (§11): stage 1 is D1-D5, D7-D9 and D11 with
`import M (names)` and `import M`. It's enough to move the `Range` type that
`aoc/day02.sw` and `aoc/day05.sw` both declare word for word into one
shared file. Stage 2 adds `import M (..)`, which makes splitting one day
over several files comfortable.

## 1. What the user wants

From the user, Matt (19 October 2026), for Advent of Code
(`aoc/day01.sw` … `aoc/day05.sw`):

1. **A shared library across days**: parsing helpers, grids, ranges.
   Today it's copied: `aoc/day02.sw:34-39` and `aoc/day05.sw:22-27`
   declare the same `type Range = { lo : Nat, hi : Nat }` and the same
   `Range.parse`, character for character.
2. **One day split over several files.** How to split isn't decided. It
   might be proofs in one file and the program in another, or tests and
   proofs next to the definitions they're about with the files split by
   topic. So the design mustn't assume any particular split.

From the second point come the questions §5 answers: can a test or theorem
live in a different file from its subject; can a later file add theorems
about an earlier file's definitions; can a file add to a namespace another
file declares?

**Not goals for now:** packages and versions, downloading code, separate
compilation into stored files, privacy (`private`), and making the
playground a multi-file editor.

## 2. What exists today

**Every command loads one file.** `check` accepts several files but gives
each its own session: "Files can't refer to each other yet, so each gets its
own session" (`crates/cli/src/main.rs:118-129`). Checked with the release
build at `f604c41`: with `a.sw` defining `double` and `b.sw` using it,
`stitchwort check a.sw b.sw` gives `[E-UNKNOWN-NAME] unknown name double`
for `b.sw`. `test`, `run`, `eval`, `repl` and `build` take one file
(`main.rs:23-64`).

**But a session can already hold several modules in sequence.** The prelude
is itself a module, loaded first as `<prelude>` with `loading_prelude` set
(`crates/driver/src/driver.rs:65-83`), and the user's file is loaded into the
same session afterwards (`driver.rs:87-118`). Loading more files one after
another into a session is the mechanism multi-file needs; what's missing is
that every non-prelude module is treated as *the* program:

- **The program's names have no prefix.** The program's root is the empty
  key prefix (`crates/elab/src/scope.rs:151-155`: `root()` is `"Std."` for
  the prelude and `""` otherwise), and a module's own short names are looked
  up as bare keys (`scope.rs:279-287`). Two files loaded into one session
  would share one root, so both declaring `main` would be `E-DUPLICATE`
  (`crates/elab/src/module.rs:410-427` checks a new name against everything
  already in scope). *From reading the code; not run, since the CLI can't
  load two files into one session.*
- **Every program module is called `Main`** (`module.rs:153`), and a data
  type's hash includes that path (`crates/core/src/globals.rs:164-203`,
  `crates/core/src/hash.rs:138`). So `day02`'s and `day05`'s `Range` today
  both hash as `Main.Range`.
- **A qualified name may name any namespace in scope** (`scope.rs:169-178`),
  so in a shared session a file could reach another file's namespace without
  importing it.
- **`auto` uses every finished definition outside the current module**
  (`module.rs:1055-1066`, `auto_eligible`), so in a shared session it would
  see files the current file doesn't import.
- **`main` is found by name, as the last definition called `main`**
  (`crates/driver/src/run.rs:142`).
- **JavaScript exports every definition marked `export`**, from every
  module loaded (`crates/js/src/lib.rs:478-484`, `:494-498`).
- **Tests accumulate** across modules in the elaborator's list
  (`module.rs:150`, `:206`), and `run_tests` runs them all
  (`driver.rs:252-300`).
- **Abilities in rows are ordered by `(module counter, position)`**
  (`crates/elab/src/lib.rs:761-766`, sorted at `crates/elab/src/effects.rs:832`).
  The counter is the order modules were loaded in. With several files, two
  abilities from sibling files could be ordered differently depending on
  which root loaded them, which would change the elaborated row and so
  (probably; **unverified**) the hash of a definition that mentions both.

**`import` exists for namespaces.** `import N (a, b)`, at the top of a file,
with an uppercase path and at least one item (`crates/syntax/src/parser.rs:480-516`;
the AST is `Module { imports, decls }`, `crates/syntax/src/ast.rs:598-611`).
Today `import Lib.Grid (x)` is `E-IMPORT-UNKNOWN: there's no namespace
Lib.Grid`, `import Lib.Grid` without a list is `E-PARSE`, and `import Grid ()`
is `E-PARSE` (all three run at `f604c41`). namespaces.md §4.5 says an import
"doesn't load anything"; that's the one sentence this note changes.

**What namespaces.md reserved** (§8, table row "Other files"): `import
Geometry (area)` where `Geometry` is a file `Geometry.sw`; a file's root is a
namespace (§4.2); a file's types are hashed with its module path instead of
`Main` (§7.4, DESIGN §11's "logical module name"). Also `import X (..)` for
everything, and `import Std ()` for "no default names".

**The playground** compiles one string named `playground.sw`
(`crates/web/src/lib.rs:19`, `:362-366`) and runs tests without a cache
(`lib.rs:76`).

**The test cache** keys a result by the test's content hash, the compiler's
version and fingerprint, and the evaluation modes
(`driver.rs:166-219`), in `.stitchwort/cache/tests/` (`main.rs:36-39`). A
test's hash covers everything it depends on (DESIGN §11), whatever file
that's in.

## 3. How other languages do it

| Language | File = module? | Namespace across files? | Cycles? | How files are found | Orphans (instances/theorems about others' types) |
|---|---|---|---|---|---|
| Lean 4 | Yes: path from a root, `.` for `/` [L1] | Yes: "Source files may add names to any namespace" [L1] | No (**unverified**) | Lake package roots [L1] | Instances anywhere, active after import (**unverified**) |
| Agda | Yes: `A.B.C` is `A/B/C.agda` [A1] | No | No: users ask for cycles and are told to split out a module [A2] | Library files / include paths | Instance arguments anywhere (**unverified**) |
| Idris 2 | Yes: `Foo.Bar.M` at `Foo/Bar/M.idr` under the `.ipkg`'s `sourcedir` [I1] | `namespace` blocks inside a module [I1] | No (**unverified**) | `.ipkg`, else the working directory [I1] | — |
| Haskell (GHC) | Yes: `A.B.C` in `A/B/C.hs` on a search path [H1] | No | Only with hand-written `hs-boot` files [H1] | Search path, default `.` [H1] | Allowed, flagged as "orphan instances" [H1] |
| OCaml | Yes: `a.ml` is module `A` [O1] | No | No: a unit sees only units linked before it [O1] | Build tool (dune) | — |
| Rust | Module tree declared by `mod foo;`, file mirrors path [R1] | No | Modules in a crate may refer to each other; crates can't (**unverified**) | From the parent file [R1] | The orphan rule forbids them across crates (**unverified**) |
| Scala 3 / Kotlin | No: a file says its package; directories are a convention [S1, K1] | Yes | Within a compilation, yes | Compiler sees every file of the build | Kotlin: extension functions anywhere, "next to the client" if client-specific [K1] |
| Gleam | Yes: module name from file path [G1] | No | No (the compiler has cycle detection; **unverified** wording) | Package `src/` | — |
| Unison | No files: definitions live in a database by hash; "names are just separately stored metadata" [U1] | n/a | n/a | n/a | — |
| Dhall | An import is a path or URL to one expression; may be pinned with `sha256:` of its normal form [D1] | n/a | — | Relative to the importing file [D1] | — |

What the table suggests:

- **"A file is a module, its path is its name"** is the usual choice for
  languages like Stitchwort (Agda, Idris, Haskell, OCaml, Gleam, and Lean
  for file *names*). It needs no project manifest to find a file.
- **Lean is the exception that matters**: in Lean, files and namespaces are
  unrelated, so a file can add to any namespace, and Mathlib relies on that.
  §4.1 weighs it.
- **Almost everyone refuses cycles.** Haskell allows them only with extra
  files, and Agda users who want them are pointed to splitting a module out
  [A2]. Scala and Rust allow them inside one compilation unit, at the cost of
  checking everything together.
- **Unison** is closest to Stitchwort's hashing: names don't enter hashes.
  Stitchwort already has that for definitions (DESIGN §11), so how code is
  split over files can't change a definition's hash, only a type's (§8).
- **Dhall and Rust's `include_str!`** resolve paths relative to the file
  that contains them [D1, R2]. §10 does the same.
- **Hiding a body.** In Idris, `export` exports only a definition's type;
  `public export` exports its body too [I1]. A proof in another module can't
  compute with a merely exported function. Stitchwort shouldn't do this by
  default: a proof in another file must see exactly what a proof in the same
  file sees (§5).

## 4. The design

### 4.1 A file is a module, and its path is a namespace (D1)

A **project** is a directory tree of `.sw` files with a root (§4.2). Each
file has a **logical name**: its path from the root, with `/` written `.`
and `.sw` dropped. `aoc/Lib/Grid.sw`, with root `aoc/`, is `Lib.Grid`.

Each file's declarations live under its logical name, as the library's
live under `Std`:

| File | Declares | Full name |
|---|---|---|
| `aoc/Range.sw` | `type Range`, `def Range.parse` | `Range.Range`, `Range.Range.parse` |
| `aoc/Lib/Grid.sw` | `type Grid`, `def neighbours` | `Lib.Grid.Grid`, `Lib.Grid.neighbours` |
| `aoc/day05.sw` | `def merge` | `day05.merge` |

Nobody writes `Range.Range.parse`: after `import Range (Range)`, `Range`
means the type and `Range.parse` the function, by the existing rules of
namespaces.md §4.4. Full names appear in hashes and in messages that must be
unambiguous.

**Inside its own file, nothing changes.** A file's short names (level 2 of
namespaces.md §4.4) are its own declarations, as now; `Geometry.area` in a
file is in that file's namespace `Geometry`.

**Why this and not Lean's way.** In Lean a file's path names the file for
`import`, but where its declarations go is up to them (`namespace List … end`
in any file adds to `List`). Compared with that:

- *For it:* moving a definition between files doesn't rename it, which
  suits a user who isn't sure how to split yet. And a proofs file can add
  `Range.mergeDisjoint` next to `Range.merge`.
- *Against it:* every file's names land in one shared tree, so a helper
  called `parseLine` in a library file clashes with every day's own
  `parseLine` unless every file is careful to use namespaces (Lean uses
  `private` and `namespace` blocks for this; Stitchwort has neither). The
  resolution levels of namespaces.md, where "the file's own" outranks
  imports, need "the file's own" to mean something.
- *Compatibility:* namespaces.md §8 promised "a file's root is a namespace".

With D1, moving a definition between files *does* change its full name.
With `import M (..)` (stage 2), short names keep working after a move, so
in practice only qualified uses (`Day05.merge`) need editing. And D6 can be
relaxed later to give Lean's main benefit (§4.6).

### 4.2 Finding files: the project root (D2)

The **project root** is the nearest directory, from the root file upwards,
that has a file called `stitchwort.toml`. Without one, it's the root file's
own directory. The marker file can be empty; later it can say where
sources live and the package's name (as Cargo, Lake, Gleam, dune and Idris's
`.ipkg` do).

`import Lib.Grid …` looks for `<root>/Lib/Grid.sw`, and nowhere else.

- **Why a marker, and not just the root file's directory?** A file's
  logical name decides its types' hashes and so which test results are
  cached. If `aoc/Day05/Proofs.sw` were checked on its own with root
  `aoc/Day05/`, it would be called `Proofs`, but `Day05.Proofs` when
  `aoc/day05.sw` imports it, and its tests would miss the cache. Worse,
  `import Range` wouldn't find `aoc/Range.sw`. With a marker in `aoc/`, a
  file has one name however it's reached.
- **Why not paths relative to the importing file** (`import "../Range.sw"`)?
  The same file would be reached by many spellings, so it would need a
  canonical name anyway; and namespaces.md reserved `import Geometry (…)`.
- **Capitals.** An imported file's path must consist of capitalised
  components (`Lib/Grid.sw`, not `lib/grid.sw`), because a namespace
  component starts with an uppercase letter and the lexer reads
  `lib.grid` as a field access on a variable `lib` (namespaces.md §4.13).
  A file that is only ever a root, like `aoc/day05.sw`, may keep its
  lowercase name; its logical name `day05` is used only in hashes and
  messages. Importing a file whose name can't be written is
  `E-MODULE-PATH` with a note saying to rename it.
- **Case-insensitive file systems** (macOS by default): `import Lib.grid`
  must not find `Lib/Grid.sw`. The loader compares the name as found in the
  directory listing with the name written (`E-MODULE-PATH`).
- **Reserved names.** A file can't be called `Std` (`Std.sw` at the root),
  and a root-level file can't have the name of a `Std` root namespace
  (`List.sw`, `Text.sw`), since `import List (…)` already means the
  library's. `Lib/List.sw` is fine: it's `Lib.List`.

### 4.3 What `import` does with a file (D3)

namespaces.md D3: `import` means the same for namespaces and files. A file
import:

1. **Loads** the file, if this session hasn't loaded it yet: parses,
   elaborates and checks it (and its imports first).
2. **Then behaves exactly like a namespace import.** `import Range (Range)`
   makes `Range` (and its constructors, if any) visible at the import level.

An import path is resolved in this order: `Std.…`; the file's own namespace
(as now); the library's namespace; **a project file**. If a path names both
a project file and a namespace the file declares itself, that's
`E-MODULE-CLASH` (rare, and clearer refused than guessed).

**Two new forms**, both parse errors today (checked at `f604c41`), so
adding them breaks nothing:

- **`import Lib.Grid`**, without a list: load it, and make the qualifier
  `Lib.Grid` usable (`Lib.Grid.neighbours g`). For a library namespace this
  form would mean nothing new (they're always usable as qualifiers), so it's
  allowed only for files. This is Haskell's `import qualified`.
- **`import Lib.Grid (..)`**: every name at the file's root, below explicit
  imports in priority, as namespaces.md §8 planned (Scala's wildcard level,
  Rust's globs). It makes splitting a day comfortable: the proofs file
  writes `import Day05 (..)` instead of listing twenty names. Stage 2.

`import Std ()` (no default names) stays reserved and unrelated.

**Qualifiers need an import.** A file can write `Lib.Grid.x` only after
some `import Lib.Grid …`. Today a qualifier may name any namespace in scope
(`scope.rs:169-178`); with several files, a file's namespace is only
reachable from files that import it.

**An import doesn't open anything else.** `import Day05 (..)` gives
`Day05`'s own names, not the names `Day05` imported (D4).

**Later, all compatible** (each is a parse error today): renaming,
`import Lib.Grid as G`; re-exporting, Idris's `import public` [I1] or Agda's
`open … public` [A1], so a `Lib.sw` could gather `Lib.Grid` and `Lib.Parse`;
and `private` declarations a file keeps to itself.

### 4.4 Which names a file sees (D4)

A file sees, by the levels of namespaces.md §4.4:

| Level | Names |
|---|---|
| 1 | Locals |
| 2 | The file's own declarations |
| 3 | Explicit imports, from library namespaces or files |
| 3½ | `(..)` imports (stage 2) |
| 4 | The default set |

and, with a qualifier, the library and the files it imports.

**Not its imports' imports.** If `day05.sw` imports `Day05.Merge`, and
`Day05.Merge` imports `Range`, then `day05.sw` can't write `Range` without
importing it too. This is Haskell's, Agda's and Gleam's rule; Lean opens
the transitive imports [L1]. The direct rule means adding an import to a
library file never changes what a name means in a file that uses the
library.

**One exception: dot notation finds a type's own file.** If `day05.sw`
gets a `Range` value from `Day05.Merge` without importing `Range`, then
`r.size` still finds `Range.Range.size`, because it's declared in the same
file as `Range`. The value's type was necessarily loaded, and functions
declared next to a type are what dot notation is for. This is Rust's
distinction between a type's own (inherent) methods, usable everywhere, and
trait methods, usable only where the trait is imported (**unverified**
against the Reference text).

**Never a file it doesn't import.** In one session, files load in a
topological order of the imports, so when `day05.sw` imports `A` and `B`, and
`B` doesn't import `A`, `A` is loaded before `B` but stays invisible to `B`.
Today that wouldn't hold (§2): resolution and `auto` must both filter by
"which files does this file import". Concretely, each scope entry records
the file that declared it.

**Clashes between imports** are the existing rules: two imports of the same
short name are `E-AMBIGUOUS` where it's used; an import that a file's own
declaration would hide is `E-IMPORT-CLASH`. The same file imported along two
paths is one thing, not a clash.

### 4.5 No cycles (D5)

If `A` imports `B`, `B` may not import `A`, directly or through other
files: `E-IMPORT-CYCLE`, listing the chain.

- **Why.** Files then form a tree-like order (a DAG). Each is checked once,
  completely, before anything that imports it. The meaning of a file never
  depends on a file that imports it. And the order is what a future
  per-file cache needs (§8.3).
- **What it costs.** Two definitions that call each other must be in one
  file. A proof that the program needs *inside* the program (a proof field,
  a termination lemma) must be in the program's file or in a file it
  imports, not in a proofs file that imports the program.
- **The alternative**, checking all files of a project as one big module
  (Scala, and Rust within a crate): Stitchwort's whole-module pre-pass
  already sorts declarations into dependency order (`module.rs:1-32`), so it
  could in principle span files. It's refused for now because it makes
  every file's meaning depend on the whole project, and needs the whole
  project re-checked after any change. Allowing cycles later turns errors
  into programs, so it's compatible.

### 4.6 Adding to another file's namespace (D6)

`theorem Range.mergeDisjoint …` in `aoc/Day05/Proofs.sw`, where `Range`
means `Range.Range` from `aoc/Range.sw`, would add to another file's
namespace.

**Recommended for now: refused**, `E-FOREIGN-NAMESPACE`, the same rule and
check as `E-STD-NAMESPACE` (namespaces.md §4.3, `scope.rs:340-386`), with the
library counted as one more foreign file. The proofs file calls it
`mergeDisjoint`, or `Merge.disjoint` in a namespace of its own.

**Why not allow it now.** It's useful mainly for dot notation: a day-specific
`r.overlaps` on the shared `Range`. But then what `r.overlaps` means depends
on which files are visible, and two sibling files could both add
`Range.overlaps`. Lean allows this [L1]; Kotlin allows it and advises putting
client-specific extensions "next to the code of that client" [K1].

**How it could be allowed later** without breaking anything: an addition
from file `F` to `T`'s namespace is found (by `T.f` or by dot notation) only
in `F` and the files that import `F`; the type's own file's declarations win
(§4.4's exception), and two visible additions with one name are
`E-AMBIGUOUS` at use. The same rule would answer namespaces.md Q4 (adding
`List.sum` to the library's `List`) for user code. Q3 asks the user.

### 4.7 `auto` (D7)

`auto` searches definitions whose result is `Decidable …`
(namespaces.md §7.1). With several files it searches:

- the current file's, declared above the use (unchanged, `module.rs:983-990`);
- the library's;
- those of **every file this file imports, directly or not**.

Not just direct imports: `auto` is about types, not names, and a procedure
for a type is usually in the type's file, which may only be imported
indirectly. Not files outside the closure: then `auto`'s answer would
depend on which other files a command loaded (§2: `auto_eligible`,
`module.rs:1055-1066`, accepts any definition outside the current module).
"Imports decide which names you can write; they never change which proofs
are found" (namespaces.md §7.1) still holds *within* a file's closure.

This is the same question as **orphan instances** for the planned
interfaces (TODO, "Interfaces design note"): Haskell flags instances
declared away from both their class and their type [H1]; Rust forbids them
across crates (**unverified**); Lean allows them. The closure rule makes
the search deterministic per file; whether to also restrict where an
instance may be declared is left to the interfaces note.

### 4.8 What a file can see of another file's definitions

**Everything.** An imported function's body is as visible to the checker as
one in the same file: a proof in `Proofs.sw` can compute with
`Day05.merge` exactly as a proof in `day05.sw` can. There's no Idris-style
`export` that hides a body [I1]. Hiding bodies (`opaque`) would be a
separate, later feature for both cases.

## 5. Tests and proofs next to what they're about

The user hasn't decided how to split a day; these rules make every split
work.

- **A test or theorem may live in any file that can see its subject.** Tests
  and theorems are definitions; they name what they're about. So
  `aoc/Range.sw` can carry its own tests, and `aoc/Day05/Proofs.sw` can prove
  facts about `day05`'s functions.
- **A later file can add theorems about an earlier file's definitions.**
  They're named in the later file (D6), and the earlier file never sees them.
- **A file can't use a theorem from a file that imports it** (D5). A proof
  the program itself needs goes in the program's file or below it.
- **Moving a test or theorem between files changes nothing it depends on.**
  Its hash doesn't include names or files, so a moved test keeps its cached
  result (§8).
- **`stitchwort test day05.sw` runs the tests of `day05.sw` and of every
  project file it imports** (D9), grouped by file, so tests next to a shared
  library are run (or found in the cache) by every day that uses it. A test
  in a file nothing imports, such as `aoc/Day05/Proofs.sw`, runs when that
  file is the root, or with `stitchwort test aoc/` (§9.1).
- **`theorem`s are checked, not run**, as now: checking a file checks every
  theorem in it and in its imports.

## 6. What `aoc/` would look like

**A shared library file.** `Range` moves out of days 2 and 5:

```
-- aoc/Range.sw
-- A range of ids, both ends included.
type Range = { lo : Nat, hi : Nat }

def Range.parse (t : Text) : Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

def Range.contains (r : Range) (id : Nat) : Bool := r.lo <= id && id <= r.hi

def Range.size (r : Range) : Nat := r.hi + 1 - r.lo

test "parse" := (Range.parse "4-14").map Range.size == Just 11
test "parse junk" := Range.parse "4-x" == Nothing
```

```
-- aoc/day05.sw
import Range (Range)

def main () : {IO} () := …

type Database = { fresh : List Range, available : List Nat }

def parseDatabase (lines : List Text) : Database :=
  { fresh = lines.mapMaybe Range.parse, available = lines.mapMaybe Text.toNat }

def solvePart1 (db : Database) : Nat :=
  db.available.count (\id => db.fresh.any (\r => r.contains id))
…
```

`aoc/day02.sw` does the same. A grid library would be `aoc/Grid.sw`
(`import Grid (Grid)`, then `g.rolls`), or `aoc/Lib/Grid.sw` if the user
prefers a directory (`import Lib.Grid (Grid)`). The directory must be
capitalised (§4.2).

**One day split by kind** (proofs apart):

```
aoc/day05.sw            -- main, parseDatabase, solvePart1/2, merge, absorb
aoc/Day05/Proofs.sw     -- import day05 …?  (see below)
```

Here the proofs file must import the day, but `day05` can't be written in an
import (lowercase, §4.2). So a day that's split has a capitalised file:

```
aoc/Day05.sw            -- the program: main, parsing, solving, merge
aoc/Day05/Proofs.sw     -- import Day05 (..); theorem mergeDisjoint …; theorem part2Correct …
```

`stitchwort run aoc/Day05.sw` runs it; `stitchwort test aoc/Day05/Proofs.sw`
checks the proofs and runs the tests of both files.

**One day split by topic** (tests and proofs next to their subject):

```
aoc/Day05/Merge.sw      -- import Range (Range); merge, absorb, their tests, mergeDisjoint
aoc/Day05.sw            -- import Range (Range); import Day05.Merge (merge); main, parsing, solving
```

Here `Day05.sw` is a file and `Day05/` a directory of the same name, as Rust
allows `util.rs` next to `util/` [R1]. `Day05.Merge` is the file
`Day05/Merge.sw`, not a namespace inside `Day05.sw`; if `Day05.sw` also
declared a namespace `Merge`, that's `E-MODULE-CLASH`.

**Real-input tests** (TODO's `include` item):

```
-- aoc/Day04/RealInput.sw
import Day04 (parseGrid, solvePart1, solvePart2)

def input : List Text := (include "../inputs/day04.txt").lines

test "real input" := (solvePart1 (parseGrid input), solvePart2 (parseGrid input)) == (1435, 8623)
```

(The numbers are placeholders.) Inputs stay gitignored, so this file fails
to check on a fresh clone with `E-INCLUDE-MISSING`, which is why it's
separate.

## 7. Errors

New codes, each a one-line shape (wording for implementation):

```
error[E-IMPORT-UNKNOWN]: there's no namespace or file `Lib.Grd`
 1 | import Lib.Grd (Grid)
   |        ^^^^^^^ looked for aoc/Lib/Grd.sw
   = note: did you mean `Lib.Grid` (aoc/Lib/Grid.sw)?
```
(Existing code, new note. In the playground the note says it has no files.)

```
error[E-IMPORT-CYCLE]: these files import each other: Day05 → Day05.Merge → Day05
 1 | import Day05 (..)
   |        ^^^^^ aoc/Day05/Merge.sw imports Day05, which imports it (aoc/Day05.sw:2)
   = note: move what both need into a third file that both import
```

```
error[E-MODULE-PATH]: `aoc/lib/grid.sw` can't be imported: `lib` isn't a namespace name
   = note: namespace names start with a capital: rename it aoc/Lib/Grid.sw
```
(Also: case differs from the file on disk; a file called `Std.sw`; a
root-level file named like a library namespace, `List.sw`.)

```
error[E-MODULE-CLASH]: `Day05.Merge` is both a file (aoc/Day05/Merge.sw) and a namespace in aoc/Day05.sw
```

```
error[E-FOREIGN-NAMESPACE]: `Range` belongs to aoc/Range.sw, and another file can't add to it
 4 | theorem Range.mergeDisjoint …
   |         ^^^^^ `Range` here means `Range.Range`
   = note: name it in this file: `mergeDisjoint`, or `Merge.disjoint`
```
(The same check as `E-STD-NAMESPACE`, which stays for the library.)

```
error[E-IMPORT-FAILED]: `Range` has errors, so this file isn't checked
 1 | import Range (Range)
   |        ^^^^^ aoc/Range.sw: 2 errors (shown above)
```
An imported file's own errors are reported first, once; files that import
it (directly or not) aren't checked, so one mistake doesn't cascade.

`include` errors are in §10. **Unchanged codes** that now also cover files:
`E-AMBIGUOUS` (two imports, at use), `E-IMPORT-CLASH`, `E-DUPLICATE`
(within a file only, since files no longer share a root), `E-NO-MAIN`
(about the root file), `E-EXPORT` (§9.3).

## 8. Hashing and caching

### 8.1 Hashes

- **Definitions: no change.** Names aren't hashed (DESIGN §11), so neither
  is the file a definition is in. Moving `merge` from `Day05.sw` to
  `Day05/Merge.sw` keeps its hash and every hash above it.
- **Data types hash their full path**, which becomes the file's logical
  name plus the type's namespace path: `Range.Range`, `Lib.Grid.Grid`,
  `day05.Database`, where today every program's is `Main.…`
  (`module.rs:153`). That's DESIGN §11's rule ("a nominal type's hash
  includes its logical module name and its own name"). Moving a type to
  another file makes it a new type with a new hash, and everything that
  mentions it rehashes. DESIGN §11 already accepts that, and hashes aren't
  a design constraint yet (TODO "Later").
- **One-off change:** every AoC program's types change hash once (`Main.X`
  becomes `day05.X`), so cached test results are recomputed once. Sessions
  with no file (the playground, the REPL without a file, the driver's own
  tests) keep `Main`, so `crates/driver/tests/hash_stability.rs` should be
  unaffected unless a test loads from a path.
- **The logical name, never the disk path.** Moving the checkout, or
  checking a file from another working directory, changes nothing. That's
  why §4.2 insists on one name per file.
- **Ability order in rows** must not depend on load order (§2): order by
  (logical file name, source position) instead of `(module counter,
  position)`.

### 8.2 The test cache

Unchanged in mechanism: a result is keyed by the test's hash with the
compiler fingerprint and modes (`driver.rs:166-219`). Consequences:

- A library test run by `day02` is found in the cache by `day05`.
- A test moved to another file keeps its result.
- Editing `aoc/Range.sw` reruns exactly the tests that depend on what
  changed, in every file.
- The cache directory stays `.stitchwort/cache` under the working
  directory (`main.rs:36-39`). Putting it at the project root instead would
  share it between working directories; a small, separate choice (Q5).

### 8.3 Elaboration is still redone

Every command re-elaborates the root and all its imports (no elaboration
cache exists; DESIGN §11 "Later"). For AoC sizes this is small (days check
in 0.1-0.3 s, TODO). A per-file elaboration cache would need each file's
source hash, its imports' results, and (namespaces.md §7.5) the lookups it
made; the acyclic file order (D5) is what makes it possible. Not proposed
now.

## 9. The CLI, the playground and JavaScript

### 9.1 The CLI (D9)

- **`run FILE`**, **`eval FILE EXPR`**, **`repl [FILE]`**: load `FILE` and
  its imports in one session; `main` and the expression are the root file's.
  `main` is looked up as the root file's own `main`, not as the last
  definition named `main` (`run.rs:142`).
- **`test FILE`**: tests of `FILE` and of every project file it imports,
  printed grouped by file (`Range.sw`, then `day05.sw`), library tests
  excluded as now.
- **`check FILE|DIR …`**: every `.sw` file named or under a named
  directory, each file loaded once in one session (in import order), each
  seeing only its own imports (§4.4). So `stitchwort check aoc/` checks
  everything, including proofs files nothing imports.
  - `test DIR` likewise runs every file's tests once.
  - A file under the directory whose `include` target is missing
    (gitignored inputs) fails `check aoc/` with `E-INCLUDE-MISSING`; Q4.
- **`build --js FILE`**: §9.3.
- **No project file is needed to run anything.** Without `stitchwort.toml`,
  the root file's directory is the root (§4.2), and a single-file program
  works as today.

### 9.2 The playground (D10)

The playground has no file system; its source is one string
(`crates/web/src/lib.rs:19`). In stage 1:

- It stays a one-file editor. Library imports work as now.
- `import Range (…)` is `E-IMPORT-UNKNOWN` with the note "the playground
  has only this file".
- `include` is `E-INCLUDE-UNAVAILABLE`.

To leave room for more, the driver reads files through a small interface
("give me the text of logical file `Lib.Grid`"), with the disk behind it in
the CLI and an in-memory map in tests. A later playground with tabs would
pass the map from JavaScript. The driver's own tests use the map too, so
multi-file tests don't touch the disk.

### 9.3 JavaScript (D11)

- **`build --js FILE`** exports the root file's `export` definitions only.
  Today it exports every `export` in the session (`js/src/lib.rs:478-498`),
  which with imports would leak a library file's exports into every
  program. Everything the exports use, from any file, goes into the one
  generated module, as now. Re-exporting another file's export is a later
  feature (with `import public`).
- **Names don't collide**: generated names already encode the full logical
  name injectively (DESIGN §12 "Names"), and full names now start with the
  file's logical name, so `day05.merge` and `Range.Range.size` are distinct.
  Export names are short names and `E-EXPORT` refuses two with the same
  short name (DESIGN §12), which now matters only within the root file.
- **`run --js`**: unchanged; `main`'s closure is compiled whatever files it
  spans.

## 10. `include "file"`

The TODO item: a compile-time `include "file" : Text` whose contents are
part of the definition's hash, so the test cache covers input files
(precedents: Rust `include_str!`, Zig `@embedFile`, Lean `include_str`,
Dhall). How it fits multi-file:

- **Paths are relative to the file containing the `include`**, as Rust's
  `include_str!` ("The file is located relative to the current file") [R2]
  and Dhall's relative imports [D1]. `include "../inputs/day04.txt"` in
  `aoc/Day04/RealInput.sw` reads `aoc/inputs/day04.txt`, whichever
  directory the command runs from and whichever root file imported it.
- **Only inside the project root** (`E-INCLUDE-OUTSIDE` otherwise), so a
  project's meaning doesn't depend on files outside it. Without a
  `stitchwort.toml` the root is the root file's directory, which an
  `include` with `..` may leave; a marker fixes that. (Rust doesn't
  restrict this; **unverified** whether that's caused problems.)
- **Hashing: the contents, not the path.** `include` elaborates to the text
  value (compact text, so a 20 KB input is one literal), and that literal
  is in the definition's hash. Moving the input file, or renaming it,
  changes no hash; editing it reruns exactly the tests that use it. This is
  Dhall's integrity-check idea [D1] without writing the hash in the source.
- **Errors:** `E-INCLUDE-MISSING` (with the full path tried),
  `E-INCLUDE-NOT-TEXT` (not UTF-8), `E-INCLUDE-OUTSIDE`,
  `E-INCLUDE-UNAVAILABLE` (the playground).
- **Independent of the rest.** Only the "relative to the containing file"
  rule touches multi-file, and it holds for a single file too. So `include`
  can be built before stage 1 or after; it's listed as its own stage.

## 11. Stages

Each stage is one lane, merged on its own, with `nix flake check`.

**Stage 1: a shared library file.**

- Logical names and the project root (§4.1-4.2); the file interface
  (§9.2), disk and in-memory.
- `import M (names)` and `import M` loading files, in topological order,
  each once per session; `E-IMPORT-CYCLE`, `E-IMPORT-FAILED`,
  `E-MODULE-PATH`, `E-MODULE-CLASH`, `E-IMPORT-UNKNOWN`'s new note.
- Per-file roots for keys (`scope.rs:151-155` and level 2's lookup), the
  file recorded on each scope entry, and visibility filtered by imports
  (§4.4), including dot notation's own-file exception.
- `E-FOREIGN-NAMESPACE`, generalising `E-STD-NAMESPACE`.
- `auto` limited to the file's import closure (§4.7).
- Data type paths from logical names; ability order by logical name.
- CLI as §9.1 (`check DIR` included), `main` lookup, `build` exporting the
  root's exports only. Playground: the new note.
- AoC: `aoc/Range.sw`, used by days 2 and 5.
- **Tests:**
  - accept: a two-file program; a diamond (two files importing a third,
    loaded once); a qualified-only import; dot notation on a type from an
    indirectly imported file;
  - reject, one per new code, each asserting its code; a cycle of three
    files; a file not importing a sibling can't use its names, qualified or
    not, even when the sibling was loaded first;
  - `auto` doesn't find a procedure in a sibling file loaded earlier;
  - **stable identity**: a nested file's tests have the same hashes when
    checked directly and when reached through an importer (with a
    `stitchwort.toml`), so the second run is all cache hits;
  - moving a definition between files keeps its hash; moving a type
    changes it;
  - two files each declaring `type Range` with identical fields get
    different hashes;
  - a `main` in an imported file isn't the one `run` runs;
  - `build --js` with an `export` in an imported file doesn't export it;
    `run --js` on a two-file program;
  - abilities from two sibling files get the same row order whichever root
    loads them;
  - `test` output grouped by file, and library tests cached across roots.

**Stage 2: `import M (..)`.** The wildcard level of §4.4 (below explicit
imports, above the default set), for files and library namespaces alike
(namespaces.md §8). `W-MODULE-NAME` covers names it brings in (a
lowercase type variable that a wildcard-imported definition now names).
AoC: split one day both ways of §6 as a trial. **Tests:** precedence (own >
explicit > wildcard > default), ambiguity at use between two wildcards, a
wildcard not bringing the imported file's own imports.

**Stage `include`** (any time; §10). **Tests:** relative to the containing
file whatever the working directory; contents in the hash (edit the input,
the test reruns; move it, it doesn't); each error; the playground's error.

**Later, each when needed:** adding to another file's namespace (§4.6);
`import M as N`; re-exports; `private`; cycles; a playground with several
files; a per-file elaboration cache; the cache at the project root.

## 12. Questions for the user

Short; each has a recommendation.

- **Q1. A `stitchwort.toml` marker at `aoc/`** (empty for now) so every
  file has one name however it's checked? *Recommendation: yes.* Without
  it, files nested in directories can't import files above them.
- **Q2. `test day05.sw` also runs the tests of the files it imports**
  (cached, so cheap)? *Recommendation: yes*, grouped by file.
- **Q3. Should a file be able to add to another file's namespace** (a
  proofs file declaring `Range.mergeDisjoint`, or day 5 adding
  `r.overlaps` to the shared `Range`)? *Recommendation: not at first*
  (§4.6); tests and theorems can live anywhere regardless, only their names
  stay in their own file.
- **Q4. Imported files have capitalised names** (`Day05.sw`, `Lib/Grid.sw`);
  a day that's only ever run can stay `day05.sw`. OK to rename a day's file
  when it's split? *Recommendation: yes*; the alternative is a second way to
  write import paths. And: should `check aoc/` skip files whose `include`d
  input is missing, or fail? *Recommendation: fail*, and keep real-input
  files out of `nix flake check`'s list.
- **Q5. Test cache location**: stay in the working directory, or move to
  the project root? *Recommendation: the project root, once there's a
  marker*; minor.

## 13. Questions for the reviewer

- **R1. Visibility by direct import only, with dot notation's own-file
  exception (§4.4).** Is the exception enough, or will users hit "can't
  write `Range`" often enough to prefer Lean's transitive rule?
- **R2. `auto` over the transitive closure (§4.7)** while names are
  direct-only: is the mismatch confusing (a procedure found by `auto` but
  not nameable)? It mirrors Haskell instances versus names.
- **R3. The ability-order risk (§2, §8.1)**: does row order reach the
  hash? If it does, is ordering by (logical file name, position) enough?
- **R4. Failure policy (`E-IMPORT-FAILED`)**: stop at the first failed
  file, versus checking importers with the failed file's names marked
  failed, as components are within a file (`module.rs:177-192`).
- **R5. `E-MODULE-CLASH`** versus letting the file win: is there a case
  where a namespace inside `Day05.sw` called `Merge` and a file
  `Day05/Merge.sw` should coexist?

## Sources

- [L1] Lean Language Reference, "Source Files and Modules":
  https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/
  ("Source files may add names to any namespace"; module names from paths
  under a root; transitive imports).
- [L2] Lean Language Reference, "Namespaces and Sections":
  https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/
  ("Namespaces are orthogonal to modules").
- [A1] Agda documentation, "Module System":
  https://agda.readthedocs.io/en/latest/language/module-system.html
  (`A.B.C` in `A/B/C.agda`; `open import`; `open M public`).
- [A2] Agda mailing list, "Allow cyclic module imports" (April 2018):
  https://lists.chalmers.se/pipermail/agda/2018/010231.html
  (a request to allow cycles; users create modules to break them).
- [I1] Idris 2 documentation, "Modules and Namespaces":
  https://idris2.readthedocs.io/en/latest/tutorial/modules.html
  (path relative to the `.ipkg` `sourcedir`; `import public`; `private`,
  `export`, `public export`; `namespace` blocks).
- [H1] GHC User's Guide, "Filenames and separate compilation":
  https://downloads.haskell.org/ghc/latest/docs/users_guide/separate_compilation.html
  (search path, `A/B/C.hs`; "Every cycle in the module import graph must be
  broken by a hs-boot file"; orphan instances).
- [O1] OCaml manual, "The module system", compilation units:
  https://ocaml.org/manual/latest/moduleexamples.html
  (`A.ml` defines `A`; a unit can refer only to units linked before it).
- [R1] The Rust Reference, "Modules":
  https://doc.rust-lang.org/reference/items/modules.html
  (`mod foo;` loads `foo.rs` or `foo/mod.rs`; the file mirrors the module
  path).
- [R2] Rust standard library, `include_str!`:
  https://doc.rust-lang.org/std/macro.include_str.html
  ("The file is located relative to the current file").
- [S1] Scala 3 Book, "Packaging and Imports":
  https://docs.scala-lang.org/scala3/book/packaging-imports.html
  (package names "typically follow directory structure", not required).
- [K1] Kotlin coding conventions:
  https://kotlinlang.org/docs/coding-conventions.html
  (directories follow packages by recommendation; extension functions for
  one client "next to the code of that client").
- [G1] Gleam language tour:
  https://tour.gleam.run/everything/
  (module name from the file's path; qualified and unqualified imports).
- [U1] Unison, "The big idea":
  https://www.unison-lang.org/docs/the-big-idea/
  ("names are just separately stored metadata that don't affect the
  function's hash").
- [D1] Dhall documentation, "Safety guarantees":
  https://docs.dhall-lang.org/discussions/Safety-guarantees.html
  (imports by path or URL; relative imports resolved against the importing
  expression; `sha256` integrity checks on the normal form).

Not checked against a source, and marked **unverified** where used: whether
Lean, Idris and Gleam refuse import cycles (believed so); Rust's orphan rule
and its inherent-versus-trait method visibility; Lean's and Agda's treatment
of instances after import; Koka and Roc (not researched).
