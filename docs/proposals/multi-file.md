# Proposal: programs in several files

**Status:** draft 3, 19 October 2026. Design only, nothing is built. It
folds in Matt's decisions on draft 2 and waits for an independent review
and then Matt ([§13](#13-questions-for-matt),
[§14](#14-questions-for-the-reviewer)).

## Changes since draft 2

1. **Matt's decisions are folded in as decided** (19 October 2026), and
   removed from the open questions: every project file declares a namespace
   (`E-NO-NAMESPACE`, no default); cycles between namespaces are refused for
   now; imports are per file and name namespaces; the test cache lives in
   the project folder, gitignored (§8.2).
2. **Adding definitions to another namespace is deferred** to its own design
   (§4.7). Draft 2's "stage 3" rule for it is dropped; only the stage-1
   refusal (`E-FOREIGN-NAMESPACE`) remains.
3. **`run` has two modes** (§4.3, §9.1). `stitchwort run Ns.fn` is *project
   mode*: any function whose type a `main` could have. `stitchwort run
   path/file.sw` is always *file mode*, inside a project or not: the file
   may import only the standard library and must have a suitable `main`.
   This replaces draft 2's `E-RUN-FILE` (which refused a project file) and
   both options its Q4 offered.
4. **New §4.9: how `auto` finds candidates across files and namespaces**,
   compared with instance search in Lean 4, Haskell, Agda and Idris 2, and
   designed so the same rule can serve type-class-style interfaces later.
   It keeps draft 2's rule (own file above the use, then the namespaces this
   one depends on, then `Std`), explains why, makes the ordering exact, and
   records something draft 2 missed: which procedure `auto` picks is
   visible to proofs, not only to speed (§4.9.4).
5. **AoC-specific questions are parked** (draft 2's Q1 shared namespace
   name, Q6 playground AoC loading, Q7 `aoc/` layout): listed in §13.2,
   not decided here. The examples in §6 still use them as illustrations.
6. **Reviewer questions re-checked** (§14): R1 (imports per file) and R6
   (the extension rule) are settled by the decisions and dropped; R2-R5 are
   updated; R7-R11 are new.

This note can be read without knowing the codebase. Code references were
checked against the source at commit `c65023e` for draft 2, and those in
§4.9 and §9.1 again at `d3fb97a`. Claims about other languages cite a
source ([Sources](#sources)); in §4.9 each one is labelled **checked**
(with its source), **inferred** (reasoned from checked facts), or
**unverified**.

## Contents

0. [Summary](#0-summary)
1. [What the user wants and has decided](#1-what-the-user-wants-and-has-decided)
2. [What exists today](#2-what-exists-today)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design) (§4.9: [`auto` across files and namespaces](#49-auto-across-files-and-namespaces-d9))
5. [Tests and proofs next to what they're about](#5-tests-and-proofs-next-to-what-theyre-about)
6. [What `aoc/` would look like](#6-what-aoc-would-look-like)
7. [Errors](#7-errors)
8. [Hashing and caching](#8-hashing-and-caching)
9. [The CLI, the playground and JavaScript](#9-the-cli-the-playground-and-javascript)
10. [`include "file"`](#10-include-file)
11. [The obstacles in the code, re-assessed](#11-the-obstacles-in-the-code-re-assessed)
12. [Stages](#12-stages)
13. [Questions for Matt](#13-questions-for-matt)
14. [Questions for the reviewer](#14-questions-for-the-reviewer)
- [Sources](#sources)

## 0. Summary

**In plain words.** A project is a folder with a `stitchwort.yaml`. Every
`.sw` file in it starts by saying which namespace it adds to:

```
-- aoc/lib/range.sw                  -- the file's name and folder are only for people
namespace Aoc

type Range = { lo : Nat, hi : Nat }
def Range.parse (t : Text) : Maybe Range := …
```

```
-- aoc/day05.sw
namespace Day05
import Aoc (Range)

def main () : {IO} () := …
def solvePart2 (db : Database) : Nat := merge db.fresh |> .sumBy Range.size
```

```
-- aoc/day05-merge.sw                -- also Day05: sees main, Database, … with no import
namespace Day05
import Aoc (Range)

def merge (ranges : List Range) : List Range := …
```

All files that say `namespace Day05` together make up `Day05`, and see each
other's definitions by their short names, in any order. Another namespace is
reached by `import Aoc (Range)` or by writing `Aoc.Range`. You run a
function by its full name: `stitchwort run Day05.main`. Running a file by
its path, `stitchwort run hello.sw`, works as today, anywhere, for a file
that uses only the standard library.

(The name `Aoc` and the layout are illustrations; the AoC choices are
parked, §13.2.)

**The decisions.** "Matt" means decided by Matt; "Rec." means recommended
here and open until reviewed.

| | Decision | Design | Status |
|---|---|---|---|
| D1 | The namespace line | `namespace Day05` or `namespace Aoc.Day05` (capitalised components). **Exactly one, at the top** (after comments, before imports). §4.2 | Matt (the line); Rec. (placement details) |
| D2 | A project file without one | **Error**, `E-NO-NAMESPACE`. No default namespace. §4.2 | Matt |
| D3 | File mode | `run path/file.sw` loads that file and `Std` only, inside a project or not. A namespace line is optional there; imports of anything but `Std` are `E-FILE-MODE`; it needs a runnable `main`. §4.3 | Matt (for `run`); Rec. for `check`/`test` (Q1) |
| D4 | `stitchwort.yaml` | One key for now, `sources` (default `[src]`); unknown keys are errors. Parsed with **`serde-saphyr`**, strictly. §4.1 | Matt |
| D5 | Names within a namespace | Every file of a namespace sees all its declarations, in any order, as one module. A name declared twice is `E-DUPLICATE`, naming both files. File names mean nothing. §4.4 | Matt |
| D6 | Other namespaces | `import N (a, b)` **per file**; qualified names `N.a` need no import. No `import N` without a list. `import N (..)` in stage 2. Imports aren't passed on. §4.5 | Matt (per file, by namespace); Rec. (the rest) |
| D7 | Cycles between namespaces | **Refused for now** (`E-NAMESPACE-CYCLE`). Namespaces are checked one at a time in dependency order. §4.6 | Matt |
| D8 | Adding to another namespace | **Deferred**: needs its own design. Until then `E-FOREIGN-NAMESPACE`; `Std` stays closed. §4.7 | Matt |
| D9 | `auto` | Candidates: same file above the use, every namespace this one depends on, and `Std`; **not** sibling files at first. A fixed order that never depends on file paths or read order. The same rule is meant to serve interfaces later. §4.9 | Rec. |
| D10 | Hashes | A type hashes its **namespace's full name** plus its own path (`Day05.Database`, `Aoc.Range`). File paths never enter. §8 | Rec. |
| D11 | CLI | `run Day05.main` (project mode): any function `() -> {IO, Partial} ()` or less. `check` and `test` with no target cover the whole project; `test Day05` covers `Day05` and what it depends on. §9.1 | Matt (`run`); Rec. (the rest) |
| D12 | Playground | The user's own code stays one file, unchanged. How the shipped AoC examples load is parked. §9.2 | Rec.; AoC part parked |
| D13 | JavaScript | `build --js Day05` exports `Day05`'s `export`s only. §9.3 | Rec. |
| D14 | `include "file"` | Path relative to the including file, inside the project folder; contents hashed, path not. §10 | Rec. |
| D15 | Test cache | `.stitchwort/cache` in the **project folder**, with a `.gitignore` written inside it. File mode keeps today's location. §8.2 | Matt (location); Rec. (the `.gitignore`) |

**Smallest useful stage** (§12): `stitchwort.yaml`, the namespace line,
loading a whole project, qualified names and `import N (names)` across
namespaces, project-mode and file-mode `run`, `auto` by §4.9, and a shared
namespace for code that days 2 and 5 now copy. Stage 2 splits a day over
several files and adds `import N (..)`. Adding to another namespace waits
for its own design.

## 1. What the user wants and has decided

From Matt (19 October 2026), for Advent of Code (`aoc/day01.sw` …
`aoc/day05.sw`):

1. **A shared library across days**: parsing helpers, grids, ranges.
   Today it's copied: `aoc/day02.sw:34-39` and `aoc/day05.sw:22-27`
   declare the same `type Range = { lo : Nat, hi : Nat }` and the same
   `Range.parse`, character for character.
2. **One day split over several files**, split either by kind (proofs
   apart) or by topic (tests and proofs next to their subject). The design
   mustn't assume either.

**Decided by Matt** (19 October 2026, after drafts 1 and 2):

- **Files declare their namespace** (`namespace X`), as Kotlin and Scala
  packages do. Several files may share a namespace; file names and paths
  mean nothing. **Every file in a project must have one**: no default.
- **A project is a folder with a `stitchwort.yaml`** listing source roots
  (`sources`, default `src/`), parsed strictly with `serde-saphyr`. All
  `.sw` files under them are loaded together.
- **Imports are per file and name namespaces.**
- **Cycles between namespaces are refused** for now.
- **Adding definitions to another namespace is deferred**: it needs its own
  design, and stays a later stage only.
- **The test cache lives in the project folder**, gitignored.
- **`stitchwort run Ns.fn`** (project mode) runs any function with a
  main-compatible type. **`stitchwort run path/file.sw`** is always file
  mode: the file may import only the standard library and must have a
  suitable `main`, else it's an error.
- **`stitchwort test X` also runs the tests of everything `X` depends on.**
- **Staged delivery is fine.**
- **Long term, type-class-style interfaces are planned** (TODO, "Interfaces
  design note"), so `auto`'s search across files should extend to them.

**Not goals for now:** packages, versions and dependencies between projects,
downloading code, separate compilation into stored files, privacy
(`private`), adding to another namespace, and making the playground a
multi-file editor.

## 2. What exists today

**Every command loads one file.** `check` accepts several files but gives
each its own session ("Files can't refer to each other yet, so each gets its
own session", `crates/cli/src/main.rs:118-129`). Draft 1 checked this with
the release build: with `a.sw` defining `double` and `b.sw` using it,
`stitchwort check a.sw b.sw` gives `[E-UNKNOWN-NAME] unknown name double`
for `b.sw`.

**A session can already hold several modules in sequence.** The prelude is
a module, loaded first with `loading_prelude` set
(`crates/driver/src/driver.rs:65-83`), then the user's file
(`driver.rs:87-118`). One call of `elaborate_module`
(`crates/elab/src/module.rs:141`) takes a list of declarations, enters all
their names, works out who refers to whom, and checks them in dependency
order, so declarations may refer to each other in any order and groups that
call each other are checked together (module.rs:1-32,
[mutual-recursion.md](mutual-recursion.md)).

**Source spans already carry a file.** `Span { file: FileId, start, end }`
(`crates/syntax/src/source.rs:9-13`), so declarations from several files
can sit in one list and errors still point at the right file.

The places that assume "one program module" are listed, and re-assessed
under the new model, in §11. Briefly: every program module is called `Main`
(`module.rs:153`), the program's names have the empty prefix
(`crates/elab/src/scope.rs:151-155`), `main` is found as the last definition
named `main` (`crates/driver/src/run.rs:142`), JavaScript exports every
`export` in the session (`crates/js/src/lib.rs:478-498`), and abilities in
rows are ordered by load order (`crates/elab/src/lib.rs:761-766`, sorted at
`crates/elab/src/effects.rs:832`).

**`import` exists for library namespaces**: `import N (a, b)` at the top of
a file, with at least one item (`crates/syntax/src/parser.rs:478-516`).
`import N` without a list and `import N ()` are parse errors (checked for
draft 1), which leaves both free.

**`namespace` isn't a word the language uses yet.** No `.sw` file in the
repository uses `namespace` outside comments and strings (`grep -w`), so
making it a keyword breaks nothing. namespaces.md §8 reserved a *block*
form, `namespace Geometry … end Geometry`; §4.2 below keeps that possible.

**The playground** compiles one string (`crates/web/src/lib.rs:19`), and
since `c65023e` it also offers the AoC days with their example input, by
copying `aoc/day*.sw` into the web build (`web/build.sh:14-27`,
`flake.nix:119-133`).

**The test cache** keys a result by the test's content hash, the compiler's
version and fingerprint, and the evaluation modes (`driver.rs:166-219`), in
`.stitchwort/cache` under the working directory (`main.rs:37-38`). The
repository's own `.gitignore` lists `/.stitchwort` (line 4), which covers
only the repository root.

**`auto`** is described in §4.9.1.

## 3. How other languages do it

| Language | Where a file's names go | Namespace across files? | Cycles between units? | Source |
|---|---|---|---|---|
| **Kotlin** | The file's `package` header; no header means the root package | Yes: a package is "a container for one or more Kotlin files" | Allowed within a module (**unverified**) | [K2] |
| **Scala 3** | The file's `package` clause; directories by convention | Yes | Allowed within one compilation (**unverified**) | [S1] |
| **Go** | The file's `package` clause; one directory per package | Yes: declarations "are accessible in all files of the same package" | **Refused**: "illegal for a package to import itself, directly or indirectly" | [G2] |
| **Lean 4** | `namespace X … end X` blocks, anywhere | Yes: "Source files may add names to any namespace" | Refused between files (**unverified**) | [L1, L2] |
| Agda, Idris 2, Haskell, OCaml, Gleam | The file's path is its module | No | Refused (Haskell: only with `hs-boot` files) | [A1, I1, H1, O1, G1] |
| Rust | The module tree, mirrored by paths | No | Allowed inside a crate (**unverified**) | [R1] |
| Unison | No files: definitions are stored by hash; "names are just separately stored metadata" | n/a | n/a | [U1] |

**Running a function by name.** GHC's `-main-is` accepts `A.foo` ("GHC
assumes that the main function is `A.foo`"), a module name `A` (meaning
`A.main`), or a bare `foo` [H2]. Unison's `run myProgram` "takes a delayed
computation", looked up "in the most recent typechecked file, or in the
codebase", which "can return any type, and may perform the IO and
Exception abilities" [U2]. Both precedents for D11.

Instance search (for `auto`) is compared in §4.9.3.

### 3.1 Why files declare their namespace (the record of draft 1's choice)

Draft 1 weighed "a file is a module, its path is its name" (Agda, Haskell,
Idris, OCaml, Gleam) against "files and namespaces are independent" (Lean,
Kotlin, Scala) and chose the former. Its reasons, and what happened to them:

- *For paths:* no project file needed to find a file. **Now moot**: a
  project is a folder with a `stitchwort.yaml`, and all its files are loaded.
- *For paths:* each file's own names outrank imports, so a helper called
  `parseLine` in a library can't clash with a day's own. **Still true under
  the new model**, as long as each day and each library uses its own
  namespace, which the namespace line makes explicit.
- *Against paths:* moving a definition between files renamed it; a proofs
  file couldn't add `Range.mergeDisjoint` next to `Range.merge`; splitting a
  day meant capitalised file names and `Day05/` directories next to
  `Day05.sw`. **These were the user's real use cases**, and declaring the
  namespace in the file removes all three: moving a definition between two
  files of `Day05` changes nothing, not even its full name.

What the new model costs: you can't tell from a file's name what namespace
it's in (convention: name files after their namespace, like Kotlin's
recommended layout [K1]), and the compiler must read every file of the
project to know what each namespace contains. For projects the size of
`aoc/` that's a few milliseconds of parsing.

## 4. The design

### 4.1 Projects and `stitchwort.yaml` (D4)

A **project** is a folder containing a file named `stitchwort.yaml`. It
lists the **source roots**, folders relative to the project folder:

```yaml
# aoc/stitchwort.yaml
sources: [.]
```

- **`sources`** (optional): a list of folders. Default `[src]`. Every `.sw`
  file under each one, at any depth, belongs to the project. A source
  folder that doesn't exist, or lies outside the project folder, is an
  error. A file reached through two overlapping roots (`[., src]`) counts
  once.
- **An empty file is valid** and means all defaults.
- **No other keys for now.** An unknown key is `E-PROJECT-CONFIG`
  ("unknown key `source`; the known key is `sources`"). Later keys (a
  project `name` for dependencies) are additions, so refusing unknown keys
  now keeps them free.
- **Nested projects.** A folder under a source root that has its own
  `stitchwort.yaml` is `E-PROJECT-CONFIG` ("a project inside a project").
  Simpler than deciding who owns its files; relax later if needed.
- **Skipped while searching for files:** folders whose name starts with `.`
  (so `.stitchwort/` and `.git/`). Files other than `.sw` are ignored, so
  `aoc/inputs/` and `aoc/examples/` can stay where they are.

**Which YAML library.** `serde_yaml` is deprecated: its latest version is
`0.9.34+deprecated` and its repository was archived in March 2024 [Y1].
The candidates, checked on crates.io and GitHub on 19 October 2026:

| Crate | Latest | Status | Notes |
|---|---|---|---|
| `serde_yaml` | 0.9.34+deprecated (Mar 2024) | Archived | [Y1] |
| `serde_yml` | 0.0.13 (May 2026) | **Deprecated**, its description says so; RustSec advisory RUSTSEC-2025-0068 (unsound, unmaintained) | [Y2, Y3] |
| `serde_norway` | 0.9.42 (Dec 2024) | Fork of `serde_yaml` over a C-derived `unsafe-libyaml-norway`; no release in 22 months | [Y3, Y4] |
| `noyalib` | 0.0.58 (Oct 2026) | New (first release May 2026), pre-1.0; `serde_yml` now forwards to it | [Y5] |
| **`serde-saphyr`** | **2.0.0 (13 Oct 2026)** | Active (repository pushed 14 Oct 2026, not archived), pure Rust, MIT/Apache-2.0, ~8.5 million downloads in 90 days | [Y6, Y7] |
| `saphyr`, `yaml-rust2` | 0.2.2, 0.13.0 | Active YAML 1.2 parsers, but no serde layer | [Y8] |

**Matt chose `serde-saphyr`.** It's maintained, pure Rust, built for
Serde, and has exactly the strictness switches this needs:

- **The Rust types are the schema**: "the target Rust types serve as an
  explicit schema", so a field typed `String` keeps `no` as the text `"no"`
  rather than turning it into `false` [Y6, "Booleans"].
- **`strict_booleans: true`**: "interpret only the exact literals `true` and
  `false` as booleans. YAML 1.1 forms like `yes`/`no`/`on`/`off` will be
  rejected" [Y7].
- **`no_schema: true`**: "values that can be parsed as booleans or numbers
  are rejected as unquoted strings" [Y7]. So `sources: [no, 2025]` is an
  error telling you to quote them, rather than a guess.
- **Duplicate keys are an error by default** [Y6, "Duplicate keys"].
- `legacy_octal_numbers` is off by default [Y7].
- Unknown keys are refused by Serde's own `#[serde(deny_unknown_fields)]`
  on the config struct.
- Errors carry line and column. WASM support doesn't matter: the playground
  has no project files.

The whole schema is one struct with one optional `Vec<String>` field, so if
`serde-saphyr` ever went away, swapping the library is a small change. The
version must be pinned in `Cargo.lock` and built through the flake as usual.

### 4.2 The namespace line (D1, D2)

```
-- Day 5: ranges of fresh ids.
namespace Day05
import Aoc (Range)

def main () : {IO} () := …
```

- **Syntax:** `namespace` followed by a namespace path: one or more
  components separated by `.`, each starting with a capital letter, as for
  any namespace (namespaces.md §4.13). `namespace Aoc.Day05` is fine.
- **Where:** the first thing in the file, after comments and blank lines,
  before any `import`. **Exactly one per file.** A second one, or one after
  an import or declaration, is `E-PARSE` with a note.
- **Why one per file, at the top:** a reader sees on line one where every
  name in the file goes, and nothing below changes it. It's also what
  Kotlin, Scala and Go do [K2, S1, G2].
- **The block form stays possible.** namespaces.md §8 reserved
  `namespace Geometry … end Geometry` *inside* a file, as a shorthand for
  prefixing declarations. The header has no `end`, so the two never look
  alike to the parser: a `namespace` line at the top without a matching
  `end` is the header; any later one must be a block. Not proposed now.
- **Dotted names don't open their parents.** In `namespace Aoc.Day05`, the
  names of `Aoc` are not visible by short name; they're imported like any
  other namespace's. Each namespace is self-contained, which keeps "where
  does this name come from" answerable from the file alone. Kotlin's
  subpackages behave the same way (**unverified**).
- **Reserved names.** `namespace Std` (or `Std.…`) is `E-STD-NAMESPACE`. A
  namespace whose first component names a library namespace (`namespace
  List`, `namespace Text.Extra`) is `E-NAMESPACE-RESERVED`, because
  `List.map` must keep meaning the library's in every file (library
  qualifiers are always available, namespaces.md §4.6).
- **A project file without a namespace line is `E-NO-NAMESPACE`** (D2,
  decided), with the note "start the file with `namespace Name`". A default
  (Kotlin puts such a file in the root package [K2]) would put every
  headerless file in one namespace, so two days each declaring `main` would
  clash with a confusing `E-DUPLICATE`.

**Namespaces nest by name only.** `Aoc` and `Aoc.Grid` are two namespaces.
If `Aoc` also declares `type Grid`, then `Aoc.Grid` would be both the type's
namespace and a namespace with files of its own: `E-NAMESPACE-CLASH`.

### 4.3 File mode (D3)

There are two ways to load code, and the command line says which:

- **Project mode**: the argument is a name (`Day05.main`, `Day05`) or there
  is no argument. The project is found by walking up from the current
  directory (§9.1), and its files are loaded together.
- **File mode**: the argument is a path to a `.sw` file. That file is
  loaded **on its own, with `Std`**, whether or not it lies inside a
  project. No `stitchwort.yaml` is read.

For `run`, Matt decided this (19 October 2026). For `check` and `test` it's
recommended here (Q1, §9.1).

**In file mode:**

- **A namespace line is optional.** Without one the file's names have the
  empty prefix and its types hash as `Main.…` (`module.rs:153`), exactly as
  today; `examples/accept/*.sw` (74 programs) and the playground's editor
  are unchanged. With one, the names go in that namespace and its types
  hash with it, so a project file that uses only `Std` means the same in
  both modes and gets the same hashes (and cached results).
- **Only `Std` can be imported or named.** `import Aoc (Range)`, or a
  qualified name whose first component isn't a library namespace, is
  `E-FILE-MODE` ("`aoc/day05.sw` is run as a single file, which can use
  only the standard library, but it imports `Aoc`"), with the note naming
  the project-mode command when the file is inside a project ("to use the
  project, run a function by name: `stitchwort run Day05.main`").
- **`run` needs a runnable `main`**: `E-NO-MAIN` and `E-MAIN-TYPE` as today
  (`run.rs:144`, `run.rs:164`). With a namespace line, `main` means the
  file's `Day05.main`; there's only one file, so it's the last-`main` rule
  of today narrowed to one name.
- **A file in a project that uses only `Std`** (today's `aoc/day01.sw`,
  given a `namespace Day01` line) runs both ways: `stitchwort run
  aoc/day01.sw` and `stitchwort run Day01.main`.

**Why this split is easy to explain:** the argument alone decides what's
loaded. A path means "this file"; a name means "the project". Nothing
depends on whether a `stitchwort.yaml` happens to sit above the file.

The repository root must not get a `stitchwort.yaml`, or `examples/` would
become one project for project-mode commands run from the root. A test pins
that.

### 4.4 Names within a namespace (D5)

**All files of a namespace are one module.** Their declarations are put
into one list (each keeps its file in its span) and elaborated together by
the existing `elaborate_module`. So:

- Every declaration of `Day05`, in any of its files, is visible by its
  short name in all of them, in any order: level 2 of namespaces.md §4.4
  becomes "the namespace's own declarations" instead of "the file's own".
- Definitions in different files can call each other: mutual recursion
  across files works exactly as it does within one file (module.rs:20-31).
- `Range.size` declared in one file of `Aoc` and used by dot notation in
  another is the same as today within one file.

**Imports are per file** (decided), as in Go and Kotlin. `import Aoc
(Range)` in `day05.sw` doesn't make `Range` visible in `day05-merge.sw`;
each file writes its own imports. So a file's meaning can be read from the
file plus its namespace, and adding an import to one file can't change a
name in a sibling. (A sibling's *declarations* can, by design: that's what
sharing a namespace means.)

**Duplicates.** Two declarations of the same name in one namespace are
`E-DUPLICATE` (the existing code, `module.rs:410-427`), now pointing at both
places, in whichever files they are. **An import in one file clashing with
a declaration in a sibling file** is `E-IMPORT-CLASH`, as within one file
today: the namespace's own declaration would hide the import completely.

**Between namespaces there are no clashes.** `Day02.main` and `Day05.main`
are different names. Short names only collide where they're *used*: two
imports of `merge` from different namespaces are `E-AMBIGUOUS` at the use
(namespaces.md §4.4).

### 4.5 Other namespaces: qualified names and imports (D6)

**Qualified names need no import.** In any file of the project,
`Aoc.Range.parse t` works, as `List.map` works today without an import.
The first component is resolved by namespaces.md §4.4's levels, then, if
nothing local matches, as a project namespace, then as a library namespace
(`List`). Because §4.2 keeps project and library namespaces apart, the
last two can't both match.

**`import N (a, b)`** is the existing form, now also for project
namespaces: the listed names become visible by short name in this file
(level 3). Importing a type brings its constructors (namespaces.md §4.4).

**`import N` with no list: not added.** Everything is loaded and qualifiers
are free, so it would add nothing. It stays a parse error, free for later.

**`import N (..)`**: every name declared directly in `N`, at a level below
explicit imports, as namespaces.md §8 planned. Useful for a proofs file in
another namespace. Stage 2.

**Imports are not passed on.** `import Aoc (Range)` in `Day05` doesn't let
a file that imports from `Day05` write `Range`. Same rule as Go, Haskell,
Agda, Gleam.

**Visibility of declarations: everything.** There's no `private` yet, so
every declaration of a namespace can be imported or named from any other.
A proof in another namespace sees function bodies exactly as a proof in the
same file does; there is no Idris-style `export` that hides a body [I1].

### 4.6 Order and cycles between namespaces (D7)

Namespaces are checked **one at a time, each completely**, in dependency
order. `N` depends on `M` if any file of `N` imports from `M` or writes a
qualified name starting with `M`. Both are visible in the syntax, so the
order is known before anything is checked (the namespace lines say which
names are namespaces).

**A cycle between namespaces is refused** (decided): `E-NAMESPACE-CYCLE`,
listing the chain and one place where each link is made. Within a
namespace, any order and any cycle among its declarations is fine.

- **Why.** Each namespace is checked once, completely, before any namespace
  that uses it, which is the shape the elaborator already has (prelude
  first, then the program). The meaning of `Aoc` never depends on a day
  that uses it. `auto`'s candidate rule (§4.9) and a future per-namespace
  elaboration cache (§8.3) both rely on this order. Go makes the same
  choice [G2].
- **What it costs.** Two definitions in different namespaces can't call each
  other: put them in one namespace (now easy, since a namespace can span
  files) or move what both need into a third.
- **Allowing cycles later** (one project-wide dependency graph of
  declarations, each with its own namespace prefix) only turns errors into
  programs. It would need `root()` (`scope.rs:151-155`) and level 2 of name
  lookup to vary per declaration rather than per module, and §4.9's rule
  to be restated for namespaces in one cycle.

**Dot notation reaches only checked namespaces.** `r.size` with `r :
Aoc.Range` looks in `Aoc`. A file can only get a value of type `Aoc.Range`
through something it names, and everything it names is in a namespace it
depends on, directly or through others; so `Aoc` is in its dependency
closure and already checked. (This is the reasoning behind R2.)

**Canonical order.** Several orders can respect the dependencies. The one
used is fixed: repeatedly take, among the namespaces whose dependencies are
all done, the one whose full name sorts first. It's used for checking,
reporting and `auto` (§4.9.5), and never depends on file paths or the order
files are read.

**Failures.** If `Aoc` has errors, they're reported once, and the
namespaces that depend on it aren't checked (`E-NAMESPACE-FAILED`, pointing
at the import or qualified name). Namespaces that don't depend on it are
checked normally. So a broken day doesn't stop the other days.

### 4.7 Adding to another namespace (D8): deferred

Now that many files share a namespace, **adding to your own namespace from
another file is the normal case** and needs nothing special. The deferred
question is a declaration in `Day02` such as

```
def Range.invalid (w : Nat -> Int) (r : Range) : Int := …
```

where `Range` is the imported `Aoc.Range`. Today's `day02.sw` does exactly
this (`Range.repeated`, `Range.invalid`, used as `r.repeated k n` and
`.map (.invalid w)`), with its own `Range`.

**Decided: deferred to its own design.** Until then:

- **Refused** with `E-FOREIGN-NAMESPACE` ("`Range` belongs to namespace
  `Aoc`"). Day 2 names them `repeated` and `invalidIds` and calls them as
  functions, a three-line change (§6).
- **`Std`, and any future library, stay closed**: `E-STD-NAMESPACE`, as
  now (namespaces.md §4.3).

**What that design will have to answer** (recorded so the work isn't
lost): where the added name lives (draft 2 suggested `Day02.Range.invalid`,
visible only in `Day02`, with the type's own namespace winning, like
Kotlin's extension functions [K1]); whether it can be imported elsewhere;
how it interacts with namespaces.md §4.8's alias rules for dot notation;
and, with interfaces, whether an instance for another namespace's type is
the same question (§4.9.6, "orphans"). Refusing now keeps every answer
open: all of them only turn errors into programs.

### 4.8 Dot notation across files

`x.f` with `x : T` looks for `f` in `T`'s namespace, which is every
declaration `T.f` in any file of the namespace that declares `T`. That set
is complete once `T`'s namespace is checked, so the answer can't depend on
which other namespaces exist. Within `T`'s own namespace, the existing
over-approximating dependency edges for dot notation (namespaces.md §5)
now span all its files, which is what lets `r.size` in one file depend on
`Range.size` in another.

### 4.9 `auto` across files and namespaces (D9)

This section answers: when `auto` looks for a decision procedure, which
definitions in which files and namespaces may it use, in what order, and
what if several fit? It also checks the answer against how Lean 4,
Haskell, Agda and Idris 2 find *instances*, because interfaces are planned
and should reuse the same rule.

#### 4.9.1 What `auto` does today

`[auto ok : p]` asks the compiler to find a proof of `p` (DESIGN §6). The
search (`crates/elab/src/auto.rs:1-22`, `prove` at `auto.rs:82-118`,
`decide` at `auto.rs:122-192`) tries, in order:

1. **A hypothesis in scope** whose type is `p`, such as the `h` in `if h :
   d != 0 then n / d else 0`.
2. **A decision procedure**: any definition whose result type is
   `Decidable …`. There's no marker: every such definition is a candidate
   (`decision_procedures`, `auto.rs:215-229`). They're tried **most
   recently defined first**, so a file's own come before the prelude's.
   **The first one whose type fits** the goal (by unification, with its own
   `Decidable` arguments found recursively, up to depth 8) is chosen.
   There's no check for a second one that would also fit.
3. The chosen procedure is **run at compile time**: `Yes` gives the proof,
   `No` is `E-AUTO-FALSE`, and a procedure that can't finish because its
   inputs aren't known is `E-AUTO-STUCK`. A stuck procedure is **not**
   followed by trying the next candidate (`auto.rs:89-117`).

The same search decides propositions used as `Bool`s: `x == y`, `if x <
3`, `List.filter (\n => n <= k)` (`check.rs:1452-1488`,
`logic.rs:125-148`, `bind.rs:187-192`). There the chosen procedure isn't
run at compile time; it becomes part of the program.

**Which candidates are allowed** (`auto_eligible`, `module.rs:1111-1124`):
a definition that has finished checking, and, if it's in the module being
checked, one declared above the use. The "above" rule exists because
declarations are checked in dependency order, not source order, so a
procedure below the use may or may not be finished in time; "above" makes
the answer independent of that. When nothing is found, `auto_hints`
(`module.rs:1018-1058`) explains why each procedure of the module couldn't
be used ("below the use", "has errors", "in the same cycle", "not checked
yet").

Today everything outside the module is the prelude, so "every finished
definition" is unambiguous. With a project it isn't: other namespaces may
or may not have been checked yet, depending on an order the user didn't
choose.

#### 4.9.2 Words used here

- **Instance**: in languages with type classes, a declaration saying "here
  is how type `T` supports interface `C`" (for example, how to compare or
  print a `T`). The compiler finds instances by type, as `auto` finds
  decision procedures. In this section, a decision procedure plays the role
  of an instance, and `Decidable` the role of the interface.
- **Candidate**: a definition the search may consider for a goal.
- **Coherence**: every way the compiler could solve a goal gives the same
  program behaviour. Global uniqueness is a stronger form: at most one
  instance for each interface and type in the whole program [E1].
- **Orphan**: an instance declared in a module that declares neither the
  interface nor the type it's for (Haskell's term [H4]).
- **Scoped / local instance**: one that counts only where its namespace is
  opened, or only in one section of code (Lean's terms [L6]).

#### 4.9.3 How the four languages do it

| | **Lean 4** | **Haskell (GHC)** | **Agda** | **Idris 2** |
|---|---|---|---|---|
| What's a candidate | Definitions marked `instance`, plus any local variable whose type is a class (**checked** [L7]) | `instance` declarations (**checked** [H3]) | Definitions in an `instance` block, plus variables bound as instance arguments (**checked** [A2]) | Local variables of the right type, the type's constructors, local functions, then global functions marked `%hint` (**checked** [I2]); interface implementations are found the same way: "this is exactly how interface resolution works" (**checked** [I2]) |
| From where | Global instances are "in effect whenever the module in which they're established is transitively imported" (**checked** [L6]) | An instance is in scope "if and only if a chain of import declarations leads to the module"; import and export lists can't name or hide instances (**checked** [H3]) | Every instance in scope, even if only under a qualified name; modules imported but not opened count (**checked** [A2]). Instances in modules not imported at all aren't in scope, so don't count (**inferred**) | Not stated on the pages read (**unverified**) |
| Order | Higher priority first (default 1000); then "more recent instances taking precedence over earlier ones with the same priority" (**checked** [L7]); local instances win over global ones in the reference's example (**checked** [L7]) | No order: "exactly one instance must match" (**checked** [H5]) | No order by default (**checked** [A2]) | Fixed by the list in the first row (**checked** [I2]); among several `%hint`s, **unverified** |
| Several fit | The first success is used; the reference describes instances as "morally canonical" ("any discovered instance should be considered as good as any other") (**checked** [L7]) | Error, reported lazily, when a goal is solved, not when instances are declared (**checked** [H5]); `OVERLAPPING`/`INCOHERENT` pragmas relax this | Error by default: "if there are multiple candidates that could be used to solve an instance goal, a type error is raised"; `OVERLAPPABLE`/`OVERLAPPING`/`INCOHERENT` pragmas relax it (**checked** [A2]) | "Only one implementation of an interface can be given for a type"; others must be *named* and passed explicitly (**checked** [I3]) |
| Scoped / local | `scoped` (counts where the namespace is opened) and `local` (counts in the current section) (**checked** [L6]) | None (**inferred** from [H3]: imports can't control instances) | Instance arguments in a signature are local candidates (**checked** [A2]); `--no-qualified-instances` limits candidates to unqualified names (**checked** [A2]) | Local variables come first (**checked** [I2]) |
| Depth limit | (not checked) | (not checked) | Limited; `--instance-search-depth` (**checked** [A2]) | 100 (**checked** [I2]) |

**What the comparison shows:**

1. **Where candidates come from: "what this module imports, transitively"**
   in Lean and Haskell, and nearly so in Agda. None of them uses "every
   module that happens to be loaded". Draft 2's rule, "the namespaces this
   one depends on", is the same idea, with "depends on" (imports or
   qualified names, §4.6) in place of "imports".
2. **Several candidates fitting is handled two ways.** Lean takes the first
   by priority and recency and treats instances as interchangeable;
   Haskell, Agda and Idris refuse ambiguity by default. Which is right
   depends on whether the instances really are interchangeable.
3. **Explicit markers.** All four mark candidates explicitly (`instance`,
   `%hint`). Stitchwort doesn't: any `Decidable`-returning definition is
   one. That's convenient for `Decidable`, and §4.9.6 recommends markers
   for interfaces.
4. **Haskell's orphan problem** is about modules that never meet: two
   orphan instances for the same type in different modules, each locally
   coherent, can produce a program where a `Data.Set` built with one
   ordering is used with another, giving `fromList [X,Y,X]` (**checked**
   [E1]). GHC warns about orphans (`-Worphans`) partly because it "must
   pro-actively read the interface files for all orphan modules" (**checked**
   [H4]).

#### 4.9.4 Why `Decidable` is the easy case, and where it isn't

**The answer can't differ.** If `p` is true, no procedure can say `No`,
because `No` carries a refutation of `p`, which would be a proof of
something false. If `p` is false, none can say `Yes`. So any two
procedures that answer agree on the answer. (**Inferred**, from the type
`Decidable p = Yes p | No (Not p)` in DESIGN §6; it assumes the logic is
consistent, which the kernel exists to ensure.) That's Lean's "morally
canonical" situation, so taking the first candidate that fits, without an
ambiguity check, is safe for *answers*.

**But the choice is still visible**, in three ways:

1. **Proofs see the term.** `aoc/day02.sw:337-344` defines `decIsTrue`
   just so that `if IsTrue c` decides with `Bool.decTrue c`, the same term
   `if lo <= hi` produces; its comment notes that `if c = True` would use
   `Bool.decEq`, "a different term". A proof by computation that unfolds
   the `if` only goes through when the procedures match. So changing which
   procedure `auto` picks can break a proof, even though the `Bool` is the
   same.
2. **Speed.** For `==` and `if`, the chosen procedure runs in the program.
   A slow hand-written `decEq` found before a fast derived one makes the
   program slow.
3. **Stuck or not.** For `[auto …]`, a procedure that can't compute at
   compile time is `E-AUTO-STUCK`, even if a later candidate could have
   answered (§4.9.1, step 3).

And since the chosen procedure is part of the elaborated definition, it
reaches the definition's hash and so the test cache (DESIGN §11 already
notes "adding or changing a decision procedure can also change what `auto`
finds").

So the order must be **deterministic** (same input, same choice, on every
machine) and **local** (adding code that a namespace doesn't depend on
can't change its choice). It doesn't have to be clever.

#### 4.9.5 The rule (D9)

**Candidates**, for a use of `auto` in file `F` of namespace `N`:

| Where the procedure is | Used by `auto`? |
|---|---|
| A hypothesis in scope, or a procedure passed in as an argument | Yes, first (unchanged) |
| Same file `F`, above the use | Yes (unchanged) |
| Same file `F`, below the use | No, as now; the hint says to move it or pass it |
| **Another file of `N`** | **No, at first.** The hint says "`decX` is in another file of `Day05` (`day05-merge.sw`): pass it explicitly" |
| A namespace `N` depends on, directly or through others | Yes, all its procedures |
| `Std` | Yes |
| A namespace `N` doesn't depend on | **No**, even if it was checked earlier |

**Order** (the first that fits is chosen):

1. hypotheses and procedures passed as arguments (unchanged);
2. same file, most recent first (unchanged);
3. the depended-on namespaces, **latest in the canonical order (§4.6)
   first**, so a namespace's procedures come before those of the
   namespaces it builds on; within one namespace, by full name;
4. `Std`, most recent first (unchanged; the prelude is one module, loaded
   the same way every time).

Never by file path, file read order or load order.

**Several fit: first wins, no ambiguity error**, as today and as Lean
does. §4.9.4 says why that's safe for answers; passing a procedure
explicitly (`[ok := …]`, or `if x == y` via an explicitly named procedure)
pins the choice where a proof depends on it.

**Why not sibling files.** "Above the use" has no meaning across files,
and the order sibling files are checked in comes from the dependency
pre-pass, not anything the user wrote. Using them would make the answer
depend on details the user can't see. Passing a procedure explicitly makes
it a dependency, checked first, as today. *Later, compatible:* order
sibling files by their *file-level* dependencies (if nothing in file `G`
depends on file `F`, `G`'s procedures are usable in `F` and `G` is checked
first). That only turns `E-AUTO-NONE` into programs.

**Why not every loaded namespace** (today's rule, and namespaces.md §7.1's
"imports never change which proofs are found")? Inside one project,
namespaces that don't depend on each other are checked in an order that
only breaks ties, and `run Day05.main` checks only what `Day05` needs
(§9.1). A procedure in `Day02` would be found by `Day05` in one command and
not in another. The dependency rule is Lean's and Haskell's "transitively
imported" (§4.9.3). It also means a namespace's elaborated terms depend
only on itself and what it depends on, which a per-namespace cache needs
(§8.3).

**What changes from namespaces.md §7.1.** That note said imports decide
which names you can write and never which proofs are found. That still
holds for *which names* an import lists: `import Aoc (Range)` and `import
Aoc (Range, merge)` give the same candidates. What now matters is
*whether* `N` depends on `Aoc` at all. Adding the first import from (or
qualified use of) a namespace adds its procedures; since they come after
`N`'s own file and only answer as any other would (§4.9.4), this can change
the term chosen only where no earlier candidate fitted.

**Cost.** Today the search scans every definition per goal
(`auto.rs:219`). The filter adds one check per definition (is its
namespace in the closure?). An index by the goal's head, built per
namespace, can come later if `auto` shows up in timings
(namespaces.md §7.1 flagged this; not measured, **unverified**).

#### 4.9.6 Extending the rule to interfaces

Interfaces (TODO: "an interface is a record (laws as proof fields),
instances found by generalising the `Decidable` auto search") are the case
§4.9.4 doesn't cover: two instances of `Ord Range` can order differently,
and two of `Show Range` print differently. A `Set Range` built with one
and searched with the other is Haskell's `Data.Set` bug [E1]. So:

- **Where candidates come from: the same rule** as §4.9.5 (own file above
  the use, depended-on namespaces, `Std`). Recommended so that one piece of
  code answers both questions.
- **Explicit markers** for instances (`instance def …` or similar), as all
  four languages have, rather than "anything returning the interface's
  type". The interfaces note decides the syntax.
- **Several fit: an error for interfaces that carry data**, as Haskell,
  Agda and Idris do by default (§4.9.3), rather than Lean's first-wins.
  Interfaces made only of propositions (like `Decidable`'s answers) can
  keep first-wins.
- **Checked when instances are declared, not only when used.** Haskell
  reports overlap only when a goal is solved (**checked** [H5]), which is
  why two modules that never meet can disagree. A Stitchwort project is
  loaded whole, so overlapping instances anywhere in the project (and
  `Std`) can be refused when the second is checked, giving global
  uniqueness within a project. (**Inferred**; cost not estimated.)
- **Named alternatives passed explicitly**, Idris's answer to "I want a
  different ordering here" [I3]: a second `Ord Range` is an ordinary
  definition, not an instance, passed by name.
- **Local instances**: an interface argument in a signature (`[ord : Ord
  a]`) is a candidate inside the body, as hypotheses are today, and as in
  Lean, Agda and Idris (§4.9.3).
- **Orphans**: within a project, the declaration-time check above makes
  them harmless, so they needn't be refused. Instances for `Std` types and
  interfaces declared in a project namespace are orphans in Haskell's
  sense, and are needed, since `Std` is closed. Whether an instance counts
  as "adding to another namespace" (§4.7) is for that design.
- **Scoped instances** (Lean's `scoped`) are not proposed: they make an
  `open` or import change which instance is found, which goes against the
  rule above. If ever added, they'd be a separate, explicitly marked kind.

Nothing in §4.9.5 needs changing for this: interfaces add a marker, an
ambiguity check and a declaration-time overlap check on top of the same
candidate set.

## 5. Tests and proofs next to what they're about

The rules make every split work:

- **A test or theorem may live in any file of any namespace that can name
  its subject.** In the subject's own namespace it uses short names; in
  another, it imports or qualifies them.
- **A theorem in the same namespace can sit in any file**, before or after
  the definitions it's about, since a namespace is one module.
- **A namespace can't use a theorem from a namespace that depends on it**
  (§4.6). A proof the program needs goes in the program's namespace or one
  below it.
- **Moving a test or theorem between files of a namespace changes nothing**:
  same full name, same hash, same cached result. Moving it to another
  namespace changes its name but not its hash (§8). (One exception: an
  `auto` in it may pick a different procedure, §4.9.4, if the move changes
  which procedures are above it or depended on.)
- **`stitchwort test Day05` runs the tests of `Day05` and of every namespace
  it depends on** (decided), grouped by namespace and then file. Library
  (`Std`) tests are excluded, as now. Results come from the cache when
  nothing they depend on changed, so `Aoc`'s tests cost nothing the second
  time.
- **`theorem`s are checked, not run**, as now.

## 6. What `aoc/` would look like

**The AoC-specific choices are parked** (§13.2): the shared namespace's
name, the folder layout, and how the playground loads the days. This
section shows one way it could look, to check the design works for the
real use cases; it decides none of them.

**Two layouts** for the project file; both work, since paths mean nothing:

```yaml
# aoc/stitchwort.yaml, keeping today's layout
sources: [.]
```

```yaml
# aoc/stitchwort.yaml, files under aoc/src/ (or omit `sources`: src is the default)
sources: [src]
```

**A shared namespace.** A namespace per topic (`namespace Range`) makes the
type `Range.Range`; one namespace for all shared code (`Aoc` below) avoids
that. Either works with this design.

```
-- aoc/lib/range.sw
namespace Aoc

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

**Day 5, unsplit** (stage 1):

```
-- aoc/day05.sw
namespace Day05
import Aoc (Range)

def main () : {IO} () := …
type Database = { fresh : List Range, available : List Nat }
def parseDatabase (lines : List Text) : Database :=
  { fresh = lines.mapMaybe Range.parse, available = lines.mapMaybe Text.toNat }
…
```

Run with `cd aoc && stitchwort run Day05.main < inputs/day05.txt`.
`stitchwort run aoc/day05.sw` is now `E-FILE-MODE` (it imports `Aoc`),
with a note giving that command. Days that use only `Std` (days 1, 3 and 4
today) keep running both ways (§4.3).

**Day 2** (stage 1): `namespace Day02`, `import Aoc (Range)`, its own
`Range` and `Range.parse` deleted. Its `Range.repeated` and `Range.invalid`
become `repeated` and `invalidIds` (§4.7), so `.map (.invalid w)` becomes
`.map (invalidIds w)` and `r.repeated k n` becomes `repeated r k n`. If
adding to another namespace is designed later, they can go back to dot
notation.

**Day 5 split over three files, tests and proofs next to their subject**
(stage 2):

```
aoc/day05.sw          namespace Day05   main, Database, parseDatabase, solvePart1/2, example tests
aoc/day05-merge.sw    namespace Day05   merge, absorb, their tests, theorems about merge
aoc/day05-proofs.sw   namespace Day05   theorem part2Correct (solvePart2 equals the brute-force count)
```

No file imports another: they're one namespace. Each file that writes
`Range` has `import Aoc (Range)`.

**Day 5 split by kind** (proofs apart, in their own namespace):

```
aoc/day05.sw          namespace Day05          the program and its tests
aoc/day05-merge.sw    namespace Day05          merge, absorb
aoc/day05-proofs.sw   namespace Day05.Proofs   import Day05 (merge, solvePart2, Database)
                                               theorem mergeDisjoint …; theorem part2Correct …
```

The difference: in the second, `Day05` can't use the proofs (that would be
a cycle, §4.6), and the proofs file names what it uses. In the first, the
program could use a proof (a proof field, a termination lemma) from any of
its files. Both are fine; it's the user's choice. In both, a decision
procedure in `day05-merge.sw` isn't found by `auto` in `day05.sw` (§4.9.5);
in the second, `Day05.Proofs` finds all of `Day05`'s.

**Real-input tests** (with `include`, §10):

```
-- aoc/day04-real.sw
namespace Day04.Real
import Day04 (parseGrid, solvePart1, solvePart2)

def input : List Text := (include "inputs/day04.txt").lines

test "real input" := (solvePart1 (parseGrid input), solvePart2 (parseGrid input)) == (1435, 8623)
```

(Numbers are placeholders.) Inputs are gitignored, so on a fresh clone
this namespace fails with `E-INCLUDE-MISSING`. Because it's its own
namespace that nothing depends on, `run Day04.main` and `test Day04` are
unaffected (§4.6's failure rule; §9.1 checks only what's needed).

## 7. Errors

New codes, each with a one-line shape (wording for implementation):

```
error[E-PROJECT-CONFIG]: aoc/stitchwort.yaml: unknown key `source`
 1 | source: [.]
   | ^^^^^^ the known key is `sources`
```
(Also: not valid YAML, a value of the wrong kind, an unquoted `no`/`2025`
where text is expected, a missing or outside source folder, a nested
project.)

```
error[E-NO-NAMESPACE]: aoc/day05-merge.sw is in the project aoc/ but doesn't say its namespace
   = note: start the file with `namespace Name`, e.g. `namespace Day05`
```

```
error[E-FILE-MODE]: aoc/day05.sw is run as a single file, so it can use only the standard library
 3 | import Aoc (Range)
   |        ^^^ `Aoc` is a namespace of the project aoc/
   = note: to use the project, run a function by name: `stitchwort run Day05.main`
```
(For a file outside any project, the note is "a file run on its own can
use only the standard library".)

```
error[E-NAMESPACE-CYCLE]: these namespaces use each other: Day05 → Aoc → Day05
 2 | import Day05 (merge)
   |        ^^^^^ in aoc/lib/range.sw (namespace Aoc)
   = note: Day05 uses Aoc at aoc/day05.sw:2
   = note: put what both need into one namespace, or into a third that both use
```

```
error[E-NAMESPACE-RESERVED]: `List` is a namespace of the standard library
 1 | namespace List
```

```
error[E-NAMESPACE-CLASH]: `Aoc.Grid` is both the type `Grid` in namespace Aoc and a namespace of its own
```

```
error[E-FOREIGN-NAMESPACE]: `Range` belongs to namespace Aoc, and Day02 can't add to it
 4 | def Range.invalid …
   |     ^^^^^ `Range` here means `Aoc.Range`
   = note: name it in Day02, e.g. `invalidIds`
```
(Until adding to another namespace is designed, §4.7. `E-STD-NAMESPACE`
stays for the library.)

```
error[E-NAMESPACE-FAILED]: namespace Aoc has errors, so Day05 isn't checked
 2 | import Aoc (Range)
   |        ^^^ aoc/lib/range.sw: 2 errors (shown above)
```

```
error[E-RUN-TYPE]: `Day05.solvePart1` can't be run: it has type `Database -> Nat`
   = note: a function to run takes `()` and returns `()`, with abilities among IO and Partial:
           `() -> {IO} ()`, `() -> {IO, Partial} ()`, `() -> {Partial} ()` or `() -> ()`
```
(Today's `E-MAIN-TYPE`, generalised, `run.rs:163-171`.)

```
error[E-RUN-UNKNOWN]: there's no `Day5.main` in project aoc/
   = note: did you mean `Day05.main`?
```

**New notes on `E-AUTO-NONE`** (§4.9.5): "`decX` is in another file of
`Day05` (`day05-merge.sw`): pass it explicitly", and "`decX` is in
`Day02`, which `Day05` doesn't use".

**Unchanged codes** that now also cover projects: `E-DUPLICATE` (both
places, any files of a namespace), `E-IMPORT-CLASH` (an import against a
declaration in any file of the namespace), `E-IMPORT-UNKNOWN`,
`E-AMBIGUOUS`, `E-STD-NAMESPACE`, `E-EXPORT`, and in file mode `E-NO-MAIN`
and `E-MAIN-TYPE`. `include` errors are in §10.

Draft 2's `E-RUN-FILE` (refusing `run` on a project file) is gone: running
a file by path is always file mode.

## 8. Hashing and caching

### 8.1 Hashes (D10)

- **Definitions: no change.** Names aren't hashed (DESIGN §11), so neither
  is the file or namespace a definition is in. Moving `merge` between files
  of `Day05`, or to another namespace, keeps its hash (unless an `auto` in
  it then picks a different procedure, §4.9.4).
- **Data types hash their namespace's full name plus their own path**:
  `Aoc.Range`, `Day05.Database`, `Aoc.Grid.Cell` (DESIGN §11: "a nominal
  type's hash includes its logical module name and its own name"; the
  namespace *is* the logical module name now). Today every program type is
  `Main.…` (`module.rs:153`, read by `crates/core/src/globals.rs:196-203`,
  hashed at `crates/core/src/hash.rs:138`).
- **Moving a file changes nothing**: the namespace comes from the file's
  first line, not its path. Moving a type between two files of `Aoc` keeps
  its hash; moving it to another namespace makes a new type, as DESIGN §11
  accepts.
- **The same in both modes**: a project file with a namespace line that
  uses only `Std` hashes the same whether run as a file or by name (§4.3).
- **Two projects with identically named types** (`Aoc.Range` in two
  checkouts, or two people's projects) get **the same hash** if the
  declarations are identical. That doesn't matter today: only one project
  and `Std` are ever in a session, so the two can't meet, and a shared test
  cache entry is correct because identical content gives identical results.
  When projects can depend on each other, a project name (a future
  `stitchwort.yaml` key) would go in front: `aoc:Aoc.Range`. Not now.
- **Standalone files without a namespace line keep `Main`**, so
  `crates/driver/tests/hash_stability.rs` and the examples' hashes don't
  move.
- **AoC programs' types change hash once** (`Main.Range` becomes
  `Aoc.Range`), so their cached test results are recomputed once.
- **Ability order in rows** must not depend on load order (§11, item 7):
  sort by the ability's full name instead. Std's rows may then change hash
  once. *Whether row order reaches hashes is from reading the code
  (labels are sorted at `effects.rs:832` before the row is built); not
  confirmed by a test.*
- **Groups are already order-independent.** Mutually recursive definition
  groups are hashed in a canonical order by shape, and data groups by name
  (`hash.rs:8-23`), so which file a group's members come from, or the order
  files are read in, doesn't reach those hashes.

### 8.2 The test cache (D15)

Unchanged mechanism: keyed by test hash, compiler fingerprint and modes
(`driver.rs:166-219`). So `Aoc`'s tests run by `test Day02` are found in
the cache by `test Day05`; a test moved between files keeps its result; an
edit to `aoc/lib/range.sw` reruns exactly the tests that depend on what
changed.

**Location (decided):** in project mode, `.stitchwort/cache` in the
**project folder**, whatever directory the command runs from. In file
mode, as today: `.stitchwort/cache` under the working directory
(`main.rs:37-38`; `--cache-dir` still overrides both).

**Gitignored (recommended how):** when it creates `.stitchwort/`,
`stitchwort` writes `.stitchwort/.gitignore` containing `*`, so the folder
ignores itself in any repository without the user editing their own
`.gitignore`. pytest does the same for `.pytest_cache` (**checked**, via a
mirror of the commit and the follow-up issue [P1]); that issue records one
objection (a tool writing VCS files), which seems minor here. The
alternative is a line in each project's `.gitignore` by hand; the
repository's root `.gitignore` covers only `/.stitchwort` at the root
today.

### 8.3 Elaboration is still redone

Every command re-elaborates what it needs (no elaboration cache exists;
DESIGN §11 "Later"). AoC days check in 0.11-0.28 s each (TODO). A later
per-namespace cache would key on the namespace's files' text and the
results of the namespaces it depends on; the acyclic order (§4.6) and
`auto`'s dependency-only candidates (§4.9.5) are what make that possible.

## 9. The CLI, the playground and JavaScript

### 9.1 The CLI (D11)

**Mode from the argument.** An argument ending in `.sw` or containing `/`
is a file (file mode, §4.3); anything else is a name (project mode). In
project mode the project is found by walking up from the current
directory; `--project DIR` overrides that. No `stitchwort.yaml` found is
an error naming the folder searched from.

**`stitchwort run NAME`** (decided): `NAME` is a fully qualified function
name, `Day05.main` or `Aoc.Tools.demo`. Any function may be run if
calling it with `()` checks against today's runnable type:

- Today the rule is: `main ()` must check at `{IO, Partial} ()`, through a
  lambda that lets a pure or total `main` through (`run.rs:37`,
  `MAIN_TYPE = "() -> {IO, Partial} ()"`; `run.rs:136`, `MAIN_CALL`). So
  `() -> ()`, `() -> {IO} ()`, `() -> {Partial} ()` and `() -> {IO,
  Partial} ()` are all accepted; any other ability (`{State Nat}`,
  `{Fail}`) is refused, since nothing outside the program could handle it.
- The same rule applies to any named function. A function of another type
  is `E-RUN-TYPE`, naming its type and the four accepted ones (§7).
- Only the function's namespace and what it depends on are checked (§4.6),
  so a broken unrelated day, or a real-input file whose input is missing,
  doesn't stop the run. All files are still *parsed*, to read their
  namespace lines.
- Replaces `run.rs:142` ("the last definition called `main`") with a lookup
  by full name.
- **`run Day05`, meaning `Day05.main`, is not proposed now.** A compatible
  convenience later (GHC's `-main-is A` means `A.main` [H2]).

**`stitchwort run FILE.sw`** (decided): file mode, inside a project or
not (§4.3). Runs the file's `main`; `E-FILE-MODE` if it uses anything but
`Std`.

**`stitchwort test [TARGET]`:**

- No target, inside a project: every test of every namespace.
- `test Day05`: the tests of `Day05` and every namespace it depends on,
  grouped by namespace (canonical order, §4.6), then by file, then source
  order (decided).
- `test FILE.sw`: **recommended: file mode**, like `run` (Q1). The file's
  own tests, with `Std` only.

**`stitchwort check [TARGET…]`:** no target means the whole project; a
namespace name means it and what it depends on; a file means **file mode
(recommended, Q1)**. `check a.sw b.sw` keeps one session per file.

*Why recommend file mode for `check FILE` and `test FILE` too:* the same
argument should mean the same thing in every command, and the rule "a path
means just this file" is the easiest to remember. The cost: in a project,
`check aoc/day05.sw` fails with `E-FILE-MODE`, and the user types `check
Day05` instead. The alternative (draft 2's): a file inside a project means
"its namespace and dependencies" for `check`/`test`, which is handier from
an editor but makes `run` the odd one out. The VS Code extension
(`editors/vscode`) is syntax colouring only and calls no command, so
neither choice affects it today.

**`eval` and `repl`** inside a project load it and resolve names as a file
with no namespace and no imports would: qualified project names
(`Day05.solvePart1 Day05.example`) and the library's defaults.

**`build --js`**: §9.3.

### 9.2 The playground (D12)

**The user's own editor is unchanged**: one string, in file mode. `import
Aoc (…)` there is `E-FILE-MODE` with the note "the playground has only this
file". `include` is `E-INCLUDE-UNAVAILABLE`.

**The AoC examples are parked** (§13.2). Since `c65023e` the web build
copies `aoc/day*.sw` into the playground (`web/build.sh:14-27`,
`flake.nix:119-133`). Days that use only `Std` keep working as they are
(file mode). Once a day imports a shared namespace it can't compile alone.
Draft 2's suggestion, kept for when this is decided: the driver reads
source through a small interface ("the files of this project"), backed by
the disk in the CLI and by an in-memory list in tests and the browser, and
the web build passes each day with what it depends on as an in-memory
project. The in-memory interface is worth building in stage 1 anyway, for
the driver's own multi-file tests.

### 9.3 JavaScript (D13)

- **`build --js Day05`** (a namespace) exports `Day05`'s `export`
  definitions only. Today it exports every `export` in the session
  (`crates/js/src/lib.rs:478-484` and `:494-498`), which in a project would
  export every namespace's. Everything the exports use, from any namespace,
  goes into the one generated module, as now. `build --js FILE.sw` is file
  mode, unchanged.
- **Internal names don't collide**: generated names encode the full logical
  name (DESIGN §12 "Names"; namespaces.md §7.3), and full names now start
  with the namespace (`Day05.merge`, `Aoc.Range.size`).
- **Export names are short names**, and `E-EXPORT` refuses two with the
  same short name. Since only one namespace is exported, a clash can come
  only from two files of that namespace, which `E-DUPLICATE` already
  refuses (same namespace, same name), unless the names differ only in a
  sub-namespace (`Day05.A.f`, `Day05.B.f`): `E-EXPORT` as today.
- **`run --js Day05.main`**: as `run`, compiled to JS.

## 10. `include "file"`

Unchanged from draft 1 except for "inside the project":

- **Paths are relative to the file that contains the `include`**, as Rust's
  `include_str!` ("The file is located relative to the current file") [R2]
  and Dhall's relative imports [D1]. Whatever directory the command runs
  from.
- **Inside the project folder only** (`E-INCLUDE-OUTSIDE`), so a project's
  meaning doesn't depend on files outside it. In file mode: inside the
  file's own folder.
- **Hashing: the contents, not the path.** The included text is a literal
  in the definition's hash, so moving or renaming the input changes nothing
  and editing it reruns exactly the tests that use it (Dhall's integrity
  idea [D1]).
- **Errors:** `E-INCLUDE-MISSING` (with the path tried), `E-INCLUDE-NOT-TEXT`
  (not UTF-8), `E-INCLUDE-OUTSIDE`, `E-INCLUDE-UNAVAILABLE` (the
  playground).
- **Independent of the rest**; can be built before or after stage 1.

## 11. The obstacles in the code, re-assessed

Draft 1 found six places that assume one program module. Under the new
model:

| # | Today | Draft 1 needed | Now | Easier or harder? |
|---|---|---|---|---|
| 1 | Every program module is called `Main` (`module.rs:153`) | The file's path-based name | The namespace from the file's header; `Main` stays for file-mode files without one | **Easier**: the name is written in the source, no path rules, no capitalised file names |
| 2 | The program's key prefix is empty (`scope.rs:151-155`, `root()`; level 2 at `scope.rs:279-295`) | A prefix per file | A prefix per **namespace**, i.e. per `elaborate_module` call, which is what `root()` already is (per module) | **Easier**: one module per namespace, not per file. Level 2 needs the namespace's prefix in place of the `root.is_empty()` branch |
| 3 | A qualified name may reach any namespace in scope (`scope.rs:169-178`) | Must be restricted to imported files | **Mostly wanted now**: qualified names need no import. Restrict to project namespaces already checked plus `Std`, which the dependency order guarantees | **Easier** |
| 4 | `auto` uses any finished definition outside the module (`module.rs:1111-1124`) | Filter by the import closure | Filter by the namespaces this one depends on and order them (§4.9.5); within a module, "above" becomes "same file and above" | Similar. Items need their file next to their position; definitions need their namespace |
| 5 | `main` is the last definition named `main` (`run.rs:142`) | The root file's `main` | Lookup by full name (project mode); the file's `main` (file mode) | **Easier** |
| 6 | JS exports every `export` (`js/src/lib.rs:478-498`) | The root file's exports | The target namespace's exports | Same |
| 7 | Ability order by `(module counter, position)` (`lib.rs:761-766`, `effects.rs:832`) | By (logical file name, position) | By full name | Same; simpler key |
| 8 | Tests sorted by `span.start` (`module.rs:206`) | n/a | Spans from several files: sort by (file, start) | **New**, small |
| 9 | `check` gives each file its own session (`main.rs:118-129`) | Load imports on demand | Read `stitchwort.yaml`, parse every file, group by namespace, order namespaces | Same size; no import-path search, but a YAML dependency |

What makes the new model **easier** overall: `elaborate_module` already
handles "a set of declarations, in any order, possibly mutually recursive",
and a namespace is exactly that set; spans already carry their file
(`source.rs:9-13`); and def/data group hashes already ignore source order
(`hash.rs:8-23`). What makes it **harder**: every project file must be
parsed for every project-mode command (to read namespace lines); the
namespace order must be computed from the syntax (imports and qualified
names) before checking.

## 12. Stages

Each stage is one lane, merged on its own, with `nix flake check`.

**Stage 1: a project and a shared namespace.**

- `stitchwort.yaml` with `sources`, via `serde-saphyr` in strict mode;
  finding the project (§4.1, §9.1).
- The namespace line, `E-NO-NAMESPACE`, `E-NAMESPACE-RESERVED`,
  `E-NAMESPACE-CLASH`; file mode with or without a line, `E-FILE-MODE`.
- Load every file; group by namespace; canonical order by imports and
  qualified names; `E-NAMESPACE-CYCLE`, `E-NAMESPACE-FAILED`. One
  `elaborate_module` per namespace with its prefix (§11 rows 1-3).
- Qualified names and `import N (names)` across namespaces; per-file
  imports; `E-DUPLICATE` and `E-IMPORT-CLASH` across files.
- `E-FOREIGN-NAMESPACE`; `auto` by §4.9.5, with the new hints.
- Type hashes from the namespace; ability order by full name.
- CLI: `run NAME` with `E-RUN-TYPE`, `E-RUN-UNKNOWN`; `run FILE` in file
  mode; `test`/`check` of a project or a namespace with its dependencies;
  `build --js NAMESPACE`. The source interface (disk and in-memory). The
  cache in the project folder with its `.gitignore`.
- AoC (pending the parked questions): a `stitchwort.yaml`, a shared
  namespace with `Range`, used by days 2 and 5; every day gets a namespace
  line; headers, `web/build.sh`, `flake.nix` updated as needed.
- **Tests:**
  - accept: a two-namespace project; one namespace over three files with
    mutual recursion across files and dot notation across files; a type's
    function found by dot notation from another namespace; qualified use
    without import;
  - reject, one per new code, each asserting its code; a three-namespace
    cycle; an import in one file not visible in a sibling; `E-DUPLICATE`
    across two files naming both;
  - `stitchwort.yaml`: empty file; unknown key; `sources: [no]` (refused,
    not `false`); duplicate key; missing folder; nested project;
  - file mode: every `examples/accept` program unchanged (the existing
    suite); a file with a namespace line; a project file using only `Std`
    runs both ways with the same hashes; a project file importing a project
    namespace is `E-FILE-MODE`;
  - `auto`: doesn't use a procedure from a sibling file or an unrelated
    namespace, and does use one from a dependency; with two fitting
    procedures in two depended-on namespaces, the same one is chosen
    whatever order the files are read in; the hints name the file or
    namespace;
  - **stable identity**: renaming or moving a file (same namespace line)
    changes no hash, so the second run is all cache hits; two namespaces
    each declaring an identical `type Range` get different hashes;
  - `run Day05.main`; `run` of a pure `() -> ()`, a `{Partial}` one; a
    function of the wrong type; an unrelated broken namespace doesn't stop
    `run`;
  - `test Day05` runs `Aoc`'s tests too, grouped; the cache lands in the
    project folder from a subdirectory, with its `.gitignore`;
    `build --js` exports only the target namespace's; `run --js` across
    namespaces;
  - abilities from two namespaces get the same row order whatever order
    the files are read in.

**Stage 2: splitting a day.** `import N (..)` (wildcard level, below
explicit imports). AoC: day 5 split both ways of §6 as a trial (no new
compiler work beyond stage 1 and `(..)`). **Tests:** precedence (own >
explicit > wildcard > default); two wildcards ambiguous only at use; a
wildcard doesn't bring the imported namespace's own imports.

**Stage `include`** (any time; §10).

**Later, each when needed:** adding to another namespace (its own design
first, §4.7); cycles between namespaces (one project-wide graph); `auto`
across sibling files by file-level order; interfaces on §4.9.6's rule (its
own note); `run Day05` as `Day05.main`; `import N as M`; re-exports;
`private`; namespace blocks; dependencies between projects (and a project
name in type hashes); a per-namespace elaboration cache.

## 13. Questions for Matt

### 13.1 Open

Short; each has a recommendation.

- **Q1. `check FILE` and `test FILE` inside a project**: file mode, like
  `run` (recommended: one meaning for a path everywhere), or the file's
  namespace and its dependencies (handier, but unlike `run`)? §9.1.
- **Q2. `auto` and sibling files**: not used at first, pass explicitly
  (recommended), or used once file-level ordering exists (later, more
  work)? §4.9.5.
- **Q3. Direction for interfaces** (§4.9.6): same candidate rule as
  `auto`, explicit instance markers, an error when two data-carrying
  instances fit, and a project-wide overlap check when instances are
  declared. Agree as the starting point for the interfaces note?
- **Q4. The cache's `.gitignore`**: `stitchwort` writes
  `.stitchwort/.gitignore` itself (recommended, as pytest does), or each
  project lists `.stitchwort` in its own `.gitignore`? §8.2.

### 13.2 Parked (AoC-specific, not decided here)

- **P1. The shared namespace's name**: one `Aoc` for all shared code, or a
  namespace per topic (`namespace Range`, giving `Range.Range`)? (Draft 2's
  Q1.)
- **P2. The playground's AoC examples** once a day imports a shared
  namespace: load each day as a small in-memory project, or stop shipping
  such days? (Draft 2's Q6, §9.2.)
- **P3. `aoc/` layout**: `sources: [.]` keeping files where they are, or
  move them under `aoc/src/`? (Draft 2's Q7.)

## 14. Questions for the reviewer

Draft 2's R1 (is "imports per file, declarations per namespace"
confusing?) is dropped: Matt decided imports are per file. R6 (stage 3's
extension rule) is dropped: adding to another namespace is deferred.

- **R2. Namespace order from syntax (§4.6).** Is "imports plus qualified
  names whose first component is a project namespace not hidden by a local
  or own declaration" exact enough, given that a qualifier's first
  component can be the namespace's own type? Over-approximating gives false
  cycles; under-approximating checks a namespace before one it uses. Is the
  claim that dot notation only ever reaches namespaces in the dependency
  closure (§4.6) right, including through type synonyms and records'
  fields?
- **R3. `auto` (§4.9).** Is excluding sibling files too restrictive for
  split days? Is the order of §4.9.5 deterministic in every case (ties in
  the canonical order; procedures within one depended-on namespace by full
  name)? Is "first that fits wins" acceptable given §4.9.4's point that
  proofs see which procedure was chosen, or should a namespace's own
  procedures and a dependency's both fitting be a warning?
- **R4. Ability row order by full name (§8.1).** Does row order reach
  hashes, and is any code relying on the current (module, position) order
  for something other than determinism?
- **R5. Same-named types in two projects hashing alike (§8.1).** Acceptable
  until projects can depend on each other?
- **R7. File mode (§4.3).** Is "a path always means just this file" clear,
  given that `run aoc/day01.sw` works and `run aoc/day05.sw` doesn't, in
  the same folder? Any case where a file's meaning differs between file
  mode and project mode (it shouldn't: same names, same hashes)?
- **R8. The agreement argument (§4.9.4).** Is "any two decision procedures
  that answer agree" sound here? In particular: can a `partial` definition
  be a candidate (its type would end in `{Partial} Decidable …`; whether
  `decision_procedures` skips it is **unverified**), and do natively
  implemented procedures (`Nat.decEq`) need anything extra?
- **R9. Dependencies decide candidates (§4.9.5).** A single qualified name
  `Aoc.x` makes all of `Aoc`'s procedures candidates. Is that surprising
  enough to need a hint, or a stricter rule (only namespaces actually
  imported from)?
- **R10. Interfaces (§4.9.6).** Is the declaration-time overlap check over
  a whole project practical (what counts as "overlap" for dependent types,
  where instance heads can mention values)? Is refusing ambiguity for data
  but not for propositions a coherent line?
- **R11. Anything a newcomer would find confusing**, in this note or in
  the error messages of §7.

## Sources

- [K1] Kotlin coding conventions:
  https://kotlinlang.org/docs/coding-conventions.html
  ("The recommended directory structure follows the package structure with
  the common root package omitted"; file naming; extension functions for
  one client "next to the code of that client"). Verified 19 Oct 2026.
- [K2] Kotlin, "Packages and imports":
  https://kotlinlang.org/docs/packages.html
  ("A source file may start with a package header"; "If a file has no
  package header, its contents belong to the root package"; a package is
  "a container for one or more Kotlin files"). Verified 19 Oct 2026.
- [S1] Scala 3 Book, "Packaging and Imports":
  https://docs.scala-lang.org/scala3/book/packaging-imports.html
  (package clauses; names "typically follow directory structure", not
  required). From draft 1.
- [G2] The Go Programming Language Specification, "Packages" and "Import
  declarations": https://go.dev/ref/spec#Packages
  ("accessible in all files of the same package"; "It is illegal for a
  package to import itself, directly or indirectly"). Verified 19 Oct
  2026.
- [H2] GHC User's Guide, `-main-is`:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/phases.html
  ("A qualified name `A.foo`. GHC assumes that the main function is
  `A.foo`"; "A module name `A`. GHC assumes that the main function is
  `A.main`"). Verified 19 Oct 2026.
- [H3] Haskell 2010 Report, §5.4 "Importing and Exporting Instances":
  https://www.haskell.org/onlinereport/haskell2010/haskellch5.html
  ("Instance declarations cannot be explicitly named on import or export
  lists"; "All instances in scope within a module are always exported and
  any import brings all instances in from the imported module"; an
  instance is in scope "if and only if a chain of import declarations
  leads to the module"). Verified 19 Oct 2026.
- [H4] GHC User's Guide, warnings, `-Worphans`:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html
  (an orphan instance is one in a module that declares neither the class
  nor the type; "GHC must pro-actively read the interface files for all
  orphan modules"). Verified 19 Oct 2026.
- [H5] GHC User's Guide, "Instance declarations and resolution",
  overlapping instances:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/instances.html
  ("exactly one instance must match the constraint it is trying to
  resolve"; "If more than one non-incoherent candidate remains, the search
  fails"; "Errors are reported lazily (when attempting to solve a
  constraint), rather than eagerly (when the instances themselves are
  defined)"). Verified 19 Oct 2026.
- [E1] Edward Z. Yang, "Type classes: confluence, coherence and global
  uniqueness" (2014):
  http://blog.ezyang.com/2014/07/type-classes-confluence-coherence-global-uniqueness/
  (definitions of coherence and global uniqueness; the `Data.Set` example
  printing `fromList [X,Y,X]` with orphan instances). Verified 19 Oct 2026.
- [L6] Lean Language Reference, "Attributes":
  https://lean-lang.org/doc/reference/latest/Attributes/
  (global attributes "are in effect whenever the module in which they're
  established is transitively imported"; "Scoped declarations are in
  effect whenever the namespace in which they are established is opened";
  local ones "only for the extent of the section scope"; "These scope
  indications are also used to control … type class instances"). Verified
  19 Oct 2026.
- [L7] Lean Language Reference, "Instance Synthesis" and "Instance
  Declarations":
  https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/
  and https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/
  ("Instance synthesis uses both local and global instances"; "any local
  variable whose type is a type class is a candidate"; priorities and
  "more recent instances taking precedence over earlier ones with the same
  priority"; default priority 1000; instances "morally canonical"; "any
  discovered instance should be considered as good as any other").
  Verified 19 Oct 2026.
- [A2] Agda, "Instance Arguments":
  https://agda.readthedocs.io/en/latest/language/instance-arguments.html
  (candidates are definitions in an `instance` block and variables bound as
  instance arguments; "Agda considers all instances as candidates, even if
  they are only in scope under a qualified name"; imported but not opened
  modules count; "if there are multiple candidates … a type error is
  raised"; `OVERLAPPABLE`, `OVERLAPPING`, `INCOHERENT`; limited search
  depth, `--instance-search-depth`; `--no-qualified-instances`). Verified
  19 Oct 2026.
- [I2] Idris 2 tutorial, "Miscellany", auto implicit arguments:
  https://idris2.readthedocs.io/en/latest/tutorial/miscellany.html
  (the search order: local variables, constructors up to depth 100, local
  functions, `%hint` functions; "this is exactly how interface resolution
  works"). Verified 19 Oct 2026.
- [I3] Idris 2 tutorial, "Interfaces":
  https://idris2.readthedocs.io/en/latest/tutorial/interfaces.html
  ("Only one implementation of an interface can be given for a type -
  implementations may not overlap"; named implementations). Verified 19
  Oct 2026.
- [P1] pytest: the cache folder ignores itself (pull request #3982, "the
  `.pytest_cache` directory is now automatically ignored by Git"; seen via
  a mirror of the commit, f53eff9) and the objection in issue #4886:
  https://github.com/pytest-dev/pytest/pull/3982,
  https://github.com/pytest-dev/pytest/issues/4886. Checked 19 Oct 2026
  through search results and a mirror; the GitHub pages themselves weren't
  opened.
- [U2] Unison, `run`:
  https://www.unison-lang.org/docs/ucm-commands/run
  ("takes a delayed computation"; "can return any type, and may perform
  the IO and Exception abilities"). Verified 19 Oct 2026.
- [Y1] crates.io, `serde_yaml`: https://crates.io/crates/serde_yaml
  (latest `0.9.34+deprecated`, 25 Mar 2024); repository archived:
  https://github.com/dtolnay/serde-yaml. Verified 19 Oct 2026 via the
  crates.io and GitHub APIs.
- [Y2] crates.io, `serde_yml`: https://crates.io/crates/serde_yml
  (description: "DEPRECATED — `serde_yml` is unmaintained … Please migrate
  to `noyalib`"). Verified 19 Oct 2026.
- [Y3] RustSec, RUSTSEC-2025-0068:
  https://rustsec.org/advisories/RUSTSEC-2025-0068.html
  (`serde_yml` unsound and unmaintained). Verified 19 Oct 2026.
- [Y4] crates.io, `serde_norway`: https://crates.io/crates/serde_norway
  (latest 0.9.42, 21 Dec 2024). Verified 19 Oct 2026.
- [Y5] crates.io, `noyalib`: https://crates.io/crates/noyalib
  (0.0.58; first published May 2026). Verified 19 Oct 2026.
- [Y6] `serde-saphyr` README:
  https://github.com/bourumir-wyngs/serde-saphyr
  (sections "Booleans", "Duplicate keys"); crates.io:
  https://crates.io/crates/serde-saphyr (2.0.0, 13 Oct 2026, MIT OR
  Apache-2.0, MSRV 1.89). Verified 19 Oct 2026.
- [Y7] `serde-saphyr` `Options`:
  https://docs.rs/serde-saphyr/latest/serde_saphyr/options/struct.Options.html
  (`strict_booleans`, `no_schema`, `legacy_octal_numbers`,
  `duplicate_keys`). Verified 19 Oct 2026.
- [Y8] crates.io, `saphyr` (https://crates.io/crates/saphyr) and
  `yaml-rust2` (https://crates.io/crates/yaml-rust2): YAML 1.2 parsers,
  updated Oct and Sep 2026. Verified 19 Oct 2026.
- [L1] Lean Language Reference, "Source Files and Modules":
  https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/
  ("Source files may add names to any namespace"). From draft 1.
- [L2] Lean Language Reference, "Namespaces and Sections":
  https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/
  ("Namespaces are orthogonal to modules"). From draft 1.
- [A1] Agda, "Module System":
  https://agda.readthedocs.io/en/latest/language/module-system.html. From
  draft 1.
- [I1] Idris 2, "Modules and Namespaces":
  https://idris2.readthedocs.io/en/latest/tutorial/modules.html
  (`export` versus `public export`). From draft 1.
- [H1] GHC User's Guide, "Filenames and separate compilation":
  https://downloads.haskell.org/ghc/latest/docs/users_guide/separate_compilation.html
  (cycles need `hs-boot` files). From draft 1.
- [O1] OCaml manual, compilation units:
  https://ocaml.org/manual/latest/moduleexamples.html. From draft 1.
- [R1] The Rust Reference, "Modules":
  https://doc.rust-lang.org/reference/items/modules.html. From draft 1.
- [R2] Rust, `include_str!`:
  https://doc.rust-lang.org/std/macro.include_str.html
  ("The file is located relative to the current file"). From draft 1.
- [G1] Gleam language tour: https://tour.gleam.run/everything/. From
  draft 1.
- [U1] Unison, "The big idea":
  https://www.unison-lang.org/docs/the-big-idea/. From draft 1.
- [D1] Dhall, "Safety guarantees":
  https://docs.dhall-lang.org/discussions/Safety-guarantees.html. From
  draft 1.

**Not checked against a source**, and marked **unverified** where used:
whether Kotlin and Scala allow cycles between packages of one module
(believed so); whether Kotlin subpackages see their parent package's names
without an import (believed not); whether Lean refuses import cycles;
Rust's cycles within a crate; where Idris 2 looks for `%hint` functions
across modules and how it orders several; whether Agda counts instances
from modules it doesn't import (inferred not); whether a `partial`
definition can be an `auto` candidate today; the cost of `auto`'s scan.
