# Proposal: programs in several files

**Status:** draft 2, 19 October 2026. Design only, nothing is built. It
waits for an independent review and then the user
([§13](#13-questions-for-matt), [§14](#14-questions-for-the-reviewer)).

**What changed from draft 1, and why.** Matt decided (19 October 2026):

1. **Files declare their namespace** (`namespace Day05` at the top), as
   Kotlin and Scala packages do. Files and namespaces are independent: any
   number of files may declare the same namespace, and file names and paths
   mean nothing. Draft 1's D1 ("a file is a module, its path is its
   namespace") is dropped. §3.1 keeps the comparison that led here.
2. **A project is a folder with a `stitchwort.yaml`** listing source
   folders (default `src/`). All `.sw` files under them are loaded together.
   Without a `stitchwort.yaml`, a file is a standalone program, exactly as
   today. Draft 1's `stitchwort.toml` marker and "find the file by its
   import path" are dropped.
3. **Staged delivery is fine**, including adding definitions to another
   namespace (§4.7).
4. **`stitchwort test X` also runs the tests of everything `X` depends on.**
5. **`stitchwort run` takes a fully qualified function name**
   (`stitchwort run Day05.main`). Any function with a type `main` could
   have may be run; `main` is only a convention (§9.1).

Draft 1's design (`import` loads a file; visibility only through direct
imports; `E-FOREIGN-NAMESPACE`; capitalised file names) mostly falls away.
What stays: hashing by logical name, never by path (§8), the test cache,
`include` (§10), JavaScript exports per target (§9.3), and the playground
staying one file for the user's own code (§9.2).

This note can be read without knowing the codebase. Code references were
checked against the source at commit `c65023e`. Claims about other
languages cite a source ([Sources](#sources)), or are marked
**unverified**.

## Contents

0. [Summary](#0-summary)
1. [What the user wants and has decided](#1-what-the-user-wants-and-has-decided)
2. [What exists today](#2-what-exists-today)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design)
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
function by its full name: `stitchwort run Day05.main`. A single file
outside any project still works as today: `stitchwort run hello.sw`.

**The decisions, each with a recommendation.**

| | Decision | Recommendation |
|---|---|---|
| D1 | The namespace line | `namespace Day05` or `namespace Aoc.Day05` (capitalised components). **Exactly one, at the top** (after comments, before imports). §4.2 |
| D2 | A project file without one | **Error**, `E-NO-NAMESPACE`. No hidden default namespace. §4.2 |
| D3 | A file outside any project | **Unchanged.** A namespace line is optional; without one its names are at the root as today, and types hash as `Main.…`. §4.3 |
| D4 | `stitchwort.yaml` | One key for now, `sources` (default `[src]`); unknown keys are errors. Parsed with **`serde-saphyr`**, strictly. §4.1 |
| D5 | Names within a namespace | Every file of a namespace sees all its declarations, in any order, as one module. A name declared twice is `E-DUPLICATE`, naming both files. §4.4 |
| D6 | Other namespaces | `import N (a, b)` per file; qualified names `N.a` need no import. **No `import N` without a list** (it would add nothing). `import N (..)` in stage 2. Imports aren't passed on. §4.5 |
| D7 | Cycles between namespaces | **Refused for now** (`E-NAMESPACE-CYCLE`), as Go refuses import cycles. Namespaces are checked one at a time in dependency order. Allowing them later is compatible. §4.6 |
| D8 | Adding to another namespace | Within the project: **stage 3**, visible only in the namespace that adds it. `Std` stays closed (`E-STD-NAMESPACE`), and so would any future library. §4.7 |
| D9 | `auto` | Same file above the use (unchanged), every namespace this one depends on, and `Std`. **Not** other files of the same namespace at first (pass it explicitly). §4.8 |
| D10 | Hashes | A type hashes its **namespace's full name** plus its own path (`Day05.Database`, `Aoc.Range`). File paths never enter. §8 |
| D11 | CLI | `run Day05.main`: any function `() -> {IO, Partial} ()` or less (§9.1). `check` and `test` with no target cover the whole project; `test Day05` covers `Day05` and what it depends on. The project is found by walking up from the current directory. |
| D12 | Playground | The user's code stays one file, unchanged. The **AoC examples** it now ships become small in-memory projects (§9.2). |
| D13 | JavaScript | `build --js Day05` exports `Day05`'s `export`s only. §9.3 |
| D14 | `include "file"` | Path relative to the including file, inside the project folder; contents hashed, path not. Unchanged from draft 1. §10 |

**Smallest useful stage** (§12): `stitchwort.yaml`, the namespace line,
loading a whole project, qualified names and `import N (names)` across
namespaces, run-by-name, and a shared `Aoc` namespace holding `Range` for
days 2 and 5. Stage 2 splits day 5 over three files and adds `import N (..)`.
Stage 3 lets day 2 add `r.invalid` to the shared `Range`.

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

Decisions taken after draft 1 are listed at the top of this note. The two
that shape everything: **files declare their namespace** (Kotlin/Scala
packages; Lean is similar in that namespaces are independent of files), and
**a project is a folder with a `stitchwort.yaml`**, all of whose source
files are loaded together.

**Not goals for now:** packages, versions and dependencies between projects,
downloading code, separate compilation into stored files, privacy
(`private`), and making the playground a multi-file editor.

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
`flake.nix:119-133`). §9.2 deals with what happens when a day imports a
shared namespace.

**The test cache** keys a result by the test's content hash, the compiler's
version and fingerprint, and the evaluation modes (`driver.rs:166-219`), in
`.stitchwort/cache` under the working directory (`main.rs:37-38`).

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

### 3.1 Why files now declare their namespace (the record of draft 1's choice)

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
  project `name` for dependencies, the cache location) are additions, so
  refusing unknown keys now keeps them free.
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

**Recommendation: `serde-saphyr`.** It's maintained, pure Rust, built for
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
- **A project file without a namespace line is `E-NO-NAMESPACE`** (D2),
  with the note "start the file with `namespace Name`". *Why not a default
  (Kotlin puts such a file in the root package [K2])?* Every headerless
  file would then share one namespace, so two days each declaring `main`
  would clash with a confusing `E-DUPLICATE`. The error is clearer, costs
  one line per file, and allowing a default later turns errors into
  programs.

**Namespaces nest by name only.** `Aoc` and `Aoc.Grid` are two namespaces.
If `Aoc` also declares `type Grid`, then `Aoc.Grid` would be both the type's
namespace and a namespace with files of its own: `E-NAMESPACE-CLASH`.

### 4.3 A file outside any project (D3)

The project is found by walking up from the file (for a file argument) or
from the current directory (for a name argument, §9.1) until a folder with
`stitchwort.yaml` is found. If none is, the file is **standalone**, exactly
as today: `examples/accept/*.sw` (74 programs), the playground's own
editor, and anything run from outside a project. Nothing about them
changes:

- Its names have the empty prefix, its types hash as `Main.…`
  (`module.rs:153`), and `stitchwort run hello.sw` runs its `main`.
- **A namespace line is allowed** and is honoured: the file's names go in
  that namespace and its types hash with it. That lets a file move into a
  project unchanged. `run file.sw` then runs that namespace's `main`.
- **Importing a project namespace from a standalone file** is
  `E-IMPORT-UNKNOWN` with the note "this file isn't in a project (no
  `stitchwort.yaml` above it)".

The repository root must not get a `stitchwort.yaml`, or `examples/` would
become one project. A test pins that.

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

**Imports are per file**, as in Go and Kotlin. `import Aoc (Range)` in
`day05.sw` doesn't make `Range` visible in `day05-merge.sw`; each file
writes its own imports. So a file's meaning can be read from the file plus
its namespace, and adding an import to one file can't change a name in a
sibling. (A sibling's *declarations* can, by design: that's what sharing a
namespace means.)

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

**`import N` with no list: not added.** In draft 1 it meant "load this file
and allow the qualifier". Now everything is loaded and qualifiers are free,
so it would add nothing. It stays a parse error, free for later.

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

**A cycle between namespaces is refused** for now: `E-NAMESPACE-CYCLE`,
listing the chain and one place where each link is made. Within a
namespace, any order and any cycle among its declarations is fine.

- **Why refuse.** Each namespace is checked once, completely, before any
  namespace that uses it, which is the shape the elaborator already has
  (prelude first, then the program). The meaning of `Aoc` never depends on a
  day that uses it. And a future per-namespace elaboration cache needs this
  order (§8.3). Go makes the same choice [G2].
- **What it costs.** Two definitions in different namespaces can't call each
  other: put them in one namespace (now easy, since a namespace can span
  files) or move what both need into a third.
- **Could the whole project be one dependency graph instead?** Yes, in
  principle: the pre-pass (module.rs:12-31) already orders declarations by
  what they refer to, and could take every declaration of the project at
  once, each with its own namespace prefix. Cycles between namespaces would
  then be allowed exactly where cycles between declarations are. It's not
  recommended now because `root()` (`scope.rs:151-155`) and level 2 of name
  lookup would have to vary per declaration rather than per module, and
  `auto`'s "above the use" rule needs rethinking. It only turns errors into
  programs, so it can come later.

**Failures.** If `Aoc` has errors, they're reported once, and the
namespaces that depend on it aren't checked (`E-NAMESPACE-FAILED`, pointing
at the import or qualified name). Namespaces that don't depend on it are
checked normally. So a broken day doesn't stop the other days.

### 4.7 Adding to another namespace (D8)

Now that many files share a namespace, **adding to your own namespace from
another file is the normal case** and needs nothing special. The question
is a declaration in `Day02` such as

```
def Range.invalid (w : Nat -> Int) (r : Range) : Int := …
```

where `Range` is the imported `Aoc.Range`. Today's `day02.sw` does exactly
this (`Range.repeated`, `Range.invalid`, used as `r.repeated k n` and
`.map (.invalid w)`), with its own `Range`.

- **`Std`, and any future library, stay closed**: `E-STD-NAMESPACE`, as
  now (namespaces.md §4.3). A library can't change under its users.
- **Stage 1: refused** with `E-FOREIGN-NAMESPACE` ("`Range` belongs to
  namespace `Aoc`"). Day 2 names them `repeated` and `invalidIds` and calls
  them as functions, a three-line change (§6).
- **Stage 3: allowed within the project, visible only where it's added.**
  `Day02`'s `Range.invalid` lives in namespace `Day02` (full name
  `Day02.Range.invalid`, so it can't collide with `Aoc`'s own names or
  another day's). Dot notation `r.invalid` on an `Aoc.Range` finds it **only
  in files of `Day02`**, after the type's own namespace: `Aoc.Range.f` wins
  over `Day02.Range.f` if both exist. Kotlin's extension functions work
  similarly: declared anywhere, used where they're in scope [K1]. Making an
  extension usable from other namespaces (`import Day02 (Range.invalid)`)
  is a later addition.

**Why not allow it fully from the start**, as Lean does [L1]? Then what
`r.invalid` means would depend on which other days happen to be in the
project. Visible-where-declared keeps every file's meaning local.

### 4.8 `auto` and dot notation across files (D9)

**Dot notation:** `x.f` with `x : T` looks for `f` in `T`'s namespace,
which is every declaration `T.f` in any file of the namespace that declares
`T`. That set is complete once `T`'s namespace is checked, so the answer
can't depend on which other namespaces exist. Stage 3 adds the namespace's
own extensions (§4.7). Within `T`'s own namespace, the existing
over-approximating dependency edges for dot notation (namespaces.md §5)
now span all its files, which is what lets `r.size` in one file depend on
`Range.size` in another.

**`auto`** searches definitions whose result is `Decidable …`, most
recently checked first (`crates/elab/src/auto.rs:1-21`), and only those
`auto_eligible` allows (`module.rs:1055-1066`). Today that's "finished, and
if in this module, above the use". With namespaces:

| Where the procedure is | Used by `auto`? |
|---|---|
| Same file, above the use | Yes (unchanged) |
| Same file, below the use | No, as now; the hint says to move it or pass it |
| **Another file of the same namespace** | **No, at first.** The hint says "`decX` is in another file of `Day05`: pass it explicitly". |
| A namespace this one depends on, directly or not | Yes |
| `Std` | Yes |
| A namespace this one doesn't depend on | **No**, even if it was checked earlier |

- **Why not sibling files.** "Above the use" has no meaning across files,
  and the order sibling files are checked in comes from the dependency
  pre-pass, not anything the user wrote. Using it would make `auto`'s
  answer depend on details the user can't see. Passing a procedure
  explicitly makes it a dependency, checked first, as today.
- **Why not unrelated namespaces.** They're checked in an order that only
  breaks ties, so their procedures would be found or not by accident.
- **Priority** is deterministic: same file (most recent first), then
  depended-on namespaces in reverse dependency order with ties broken by
  full name, then `Std`. Never by load order or file path.
- **Later, compatible:** sibling files ordered by their *file-level*
  dependencies (if nothing in file `F` depends on file `G`, `G`'s
  procedures are usable in `F` and `G` is checked first). This only turns
  `E-AUTO-NONE` into programs.

This is the same question as instances for the planned interfaces (TODO,
"Interfaces design note"); that note should reuse this candidate rule.

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
  namespace changes its name but not its hash (§8).
- **`stitchwort test Day05` runs the tests of `Day05` and of every namespace
  it depends on** (user decision 4), grouped by namespace and then file.
  Library (`Std`) tests are excluded, as now. Results come from the cache
  when nothing they depend on changed, so `Aoc`'s tests cost nothing the
  second time.
- **`theorem`s are checked, not run**, as now.

## 6. What `aoc/` would look like

**Two layouts** for the project file; both work, since paths mean nothing:

```yaml
# aoc/stitchwort.yaml, keeping today's layout
sources: [.]
```

```yaml
# aoc/stitchwort.yaml, files under aoc/src/ (or omit `sources`: src is the default)
sources: [src]
```

**Recommendation: `sources: [.]`**, keeping `aoc/day05.sw` where it is, so
the headers' `stitchwort run` instructions, `web/build.sh` and `flake.nix`
need the smallest change. `aoc/inputs/` and `aoc/examples/` hold no `.sw`
files, so they're ignored.

**The shared namespace.** The task asked for "a shared `namespace Range`
file". That works, but the type is then `Range.Range` and its function
`Range.Range.parse`; outside the file you'd write `import Range (Range)`
and then `Range.parse`, while `Range.parse` without the import fails
(`Range` is then the namespace, which has no `parse`). **Recommended
instead: one namespace `Aoc` for all shared AoC code**, which can grow over
several files (ranges now, grids and parsing later):

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

```
-- aoc/lib/grid.sw (later)
namespace Aoc

type Grid = …
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

**Day 2** (stage 1): `namespace Day02`, `import Aoc (Range)`, its own
`Range` and `Range.parse` deleted. Its `Range.repeated` and `Range.invalid`
become `repeated` and `invalidIds` (§4.7), so `.map (.invalid w)` becomes
`.map (invalidIds w)` and `r.repeated k n` becomes `repeated r k n`. In
stage 3 they can go back to dot notation.

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
its files. Both are fine; it's the user's choice.

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
error[E-FOREIGN-NAMESPACE]: `Range` belongs to namespace Aoc, and Day02 can't add to it (yet)
 4 | def Range.invalid …
   |     ^^^^^ `Range` here means `Aoc.Range`
   = note: name it in Day02, e.g. `invalidIds`
```
(Stage 1 and 2 only. `E-STD-NAMESPACE` stays for the library.)

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

```
error[E-RUN-FILE]: aoc/day05.sw is part of the project aoc/
   = note: run a function by name: `stitchwort run Day05.main`
```

**Unchanged codes** that now also cover projects: `E-DUPLICATE` (both
places, any files of a namespace), `E-IMPORT-CLASH` (an import against a
declaration in any file of the namespace), `E-IMPORT-UNKNOWN` (with a
project-aware note), `E-AMBIGUOUS`, `E-STD-NAMESPACE`, `E-EXPORT`.
`include` errors are in §10.

## 8. Hashing and caching

### 8.1 Hashes (D10)

- **Definitions: no change.** Names aren't hashed (DESIGN §11), so neither
  is the file or namespace a definition is in. Moving `merge` between files
  of `Day05`, or to another namespace, keeps its hash.
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
- **Two projects with identically named types** (`Aoc.Range` in two
  checkouts, or two people's projects) get **the same hash** if the
  declarations are identical. That doesn't matter today: only one project
  and `Std` are ever in a session, so the two can't meet, and a shared test
  cache entry is correct because identical content gives identical results.
  When projects can depend on each other, a project name (a future
  `stitchwort.yaml` key) would go in front: `aoc:Aoc.Range`. Not now.
- **Standalone files keep `Main`**, so `crates/driver/tests/hash_stability.rs`
  and the examples' hashes don't move, unless the file has a namespace line.
- **AoC programs' types change hash once** (`Main.Range` becomes
  `Aoc.Range`), so their cached test results are recomputed once.
- **Ability order in rows** must not depend on load order (§11, item 6):
  sort by the ability's full name instead. Std's rows may then change hash
  once. *Whether row order reaches hashes is from reading the code
  (labels are sorted at `effects.rs:832` before the row is built); not
  confirmed by a test.*
- **Groups are already order-independent.** Mutually recursive definition
  groups are hashed in a canonical order by shape, and data groups by name
  (`hash.rs:8-23`), so which file a group's members come from, or the order
  files are read in, doesn't reach those hashes.

### 8.2 The test cache

Unchanged mechanism: keyed by test hash, compiler fingerprint and modes
(`driver.rs:166-219`). So `Aoc`'s tests run by `test Day02` are found in
the cache by `test Day05`; a test moved between files keeps its result; an
edit to `aoc/lib/range.sw` reruns exactly the tests that depend on what
changed. The cache stays at `.stitchwort/cache` under the working directory
(`main.rs:37-38`); moving it to the project folder is a small separate
choice (Q5).

### 8.3 Elaboration is still redone

Every command re-elaborates what it needs (no elaboration cache exists;
DESIGN §11 "Later"). AoC days check in 0.11-0.28 s each (TODO). A later
per-namespace cache would key on the namespace's files' text and the
results of the namespaces it depends on; the acyclic order (§4.6) is what
makes that possible.

## 9. The CLI, the playground and JavaScript

### 9.1 The CLI (D11)

**Finding the project.** With a file argument, walk up from the file; with
a name argument, walk up from the current directory; `--project DIR`
overrides both. The first folder with a `stitchwort.yaml` is the project.
An argument ending in `.sw` or containing `/` is a file; anything else is a
name.

**`stitchwort run NAME`** (user decision 5): `NAME` is a fully qualified
function name, `Day05.main` or `Aoc.Tools.demo`. Any function may be run if
calling it with `()` checks against today's runnable type:

- Today the rule is: `main ()` must check at `{IO, Partial} ()`, through a
  lambda that lets a pure or total `main` through
  (`run.rs:37`, `MAIN_TYPE = "() -> {IO, Partial} ()"`; `run.rs:136`,
  `MAIN_CALL`). So `() -> ()`, `() -> {IO} ()`, `() -> {Partial} ()` and
  `() -> {IO, Partial} ()` are all accepted; any other ability (`{State
  Nat}`, `{Fail}`) is refused, since nothing outside the program could
  handle it.
- The same rule applies to any named function. A function of another type
  is `E-RUN-TYPE`, naming its type and the four accepted ones (§7).
- Only the function's namespace and what it depends on are checked (§4.6),
  so a broken unrelated day, or a real-input file whose input is missing,
  doesn't stop the run. All files are still *parsed*, to read their
  namespace lines.
- Replaces `run.rs:142` ("the last definition called `main`") with a lookup
  by full name.
- **`run Day05`, meaning `Day05.main`, is not proposed now.** It would be a
  compatible convenience later (GHC's `-main-is A` means `A.main` [H2]):
  today a bare namespace name isn't a valid target, so it's an error that
  would become a program.

**`stitchwort run FILE.sw`:**

- **Standalone file:** runs its `main`, as today.
- **A file inside a project:** `E-RUN-FILE`, with the note naming the
  function to run (`Day05.main`, from the file's namespace line).
  Recommended over guessing, since a namespace may have several files and
  a file may hold no `main`. (Running the file's namespace's `main` would
  be a compatible later convenience.)

**`stitchwort test [TARGET]`:**

- No target, inside a project: every test of every namespace.
- `test Day05`: the tests of `Day05` and every namespace it depends on,
  grouped by namespace (dependencies first), then by file, then source
  order (user decision 4).
- `test FILE.sw`: standalone, as today; inside a project, the tests of the
  file's namespace and its dependencies.

**`stitchwort check [TARGET…]`:** no target means the whole project; a
namespace name or file means it and what it depends on. A standalone file
as today. `check a.sw b.sw` on standalone files keeps one session each.

**`eval` and `repl`** inside a project load it and resolve names as a file
with no namespace and no imports would: qualified project names
(`Day05.solvePart1 Day05.example`) and the library's defaults.

**`build --js`**: §9.3.

### 9.2 The playground (D12)

**The user's own editor is unchanged**: one string, a standalone file.
`import Aoc (…)` there is `E-IMPORT-UNKNOWN` with the note "the playground
has only this file". `include` is `E-INCLUDE-UNAVAILABLE`.

**The AoC examples need a decision.** Since `c65023e` the web build copies
`aoc/day*.sw` into the playground (`web/build.sh:14-27`,
`flake.nix:119-133`). Once `day05.sw` imports `Aoc`, it can't compile on
its own. Recommended:

- The driver reads source through a small interface ("the files of this
  project"), backed by the disk in the CLI and by an in-memory list in
  tests and the browser. The driver's own multi-file tests use the
  in-memory list, so they don't touch the disk.
- The web build writes, for each day, the list of files it needs (the day's
  namespace and what it depends on), and the playground passes them as an
  in-memory project, showing the day's main file in the editor and the rest
  read-only (or not at all). Running uses `Day05.main`.
- The alternative, flattening a day and its library into one generated
  standalone file, works only while no two namespaces declare the same
  short name, so isn't recommended.

This touches the playground, which the task said should stay unchanged
(Q6). Matt's memory note says the playground is viewed locally via
`web/serve.sh` and not republished; nothing here changes that.

### 9.3 JavaScript (D13)

- **`build --js Day05`** (a namespace) exports `Day05`'s `export`
  definitions only. Today it exports every `export` in the session
  (`crates/js/src/lib.rs:478-484` and `:494-498`), which in a project would
  export every namespace's. Everything the exports use, from any namespace,
  goes into the one generated module, as now. `build --js` on a standalone
  file is unchanged.
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
  meaning doesn't depend on files outside it. For a standalone file: inside
  the file's own folder (a standalone file has no project to bound it).
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
| 1 | Every program module is called `Main` (`module.rs:153`) | The file's path-based name | The namespace from the file's header; `Main` stays for standalone files without one | **Easier**: the name is written in the source, no path rules, no capitalised file names |
| 2 | The program's key prefix is empty (`scope.rs:151-155`, `root()`; level 2 at `scope.rs:279-295`) | A prefix per file | A prefix per **namespace**, i.e. per `elaborate_module` call, which is what `root()` already is (per module) | **Easier**: one module per namespace, not per file. Level 2 needs the namespace's prefix in place of the `root.is_empty()` branch |
| 3 | A qualified name may reach any namespace in scope (`scope.rs:169-178`) | Must be restricted to imported files | **Mostly wanted now**: qualified names need no import. Restrict to project namespaces already checked plus `Std`, which the dependency order guarantees | **Easier** |
| 4 | `auto` uses any finished definition outside the module (`module.rs:1055-1066`) | Filter by the import closure | Filter by the namespaces this one depends on; within a module, "above" becomes "same file and above" | Similar. Items need their file next to their position |
| 5 | `main` is the last definition named `main` (`run.rs:142`) | The root file's `main` | Lookup by full name given on the command line | **Easier** |
| 6 | JS exports every `export` (`js/src/lib.rs:478-498`) | The root file's exports | The target namespace's exports | Same |
| 7 | Ability order by `(module counter, position)` (`lib.rs:761-766`, `effects.rs:832`) | By (logical file name, position) | By full name | Same; simpler key |
| 8 | Tests sorted by `span.start` (`module.rs:206`) | n/a | Spans from several files: sort by (file, start) | **New**, small |
| 9 | `check` gives each file its own session (`main.rs:118-129`) | Load imports on demand | Read `stitchwort.yaml`, parse every file, group by namespace, order namespaces | Same size; no import-path search, but a YAML dependency |

What makes the new model **easier** overall: `elaborate_module` already
handles "a set of declarations, in any order, possibly mutually recursive",
and a namespace is exactly that set; spans already carry their file
(`source.rs:9-13`); and def/data group hashes already ignore source order
(`hash.rs:8-23`). What makes it **harder**: every project file must be
parsed for every command (to read namespace lines); the namespace order
must be computed from the syntax (imports and qualified names) before
checking; and the playground's AoC examples now need several files.

## 12. Stages

Each stage is one lane, merged on its own, with `nix flake check`.

**Stage 1: a project and a shared namespace.**

- `stitchwort.yaml` with `sources`, via `serde-saphyr` in strict mode;
  finding the project (§4.1, §4.3, §9.1).
- The namespace line, `E-NO-NAMESPACE`, `E-NAMESPACE-RESERVED`,
  `E-NAMESPACE-CLASH`; standalone files unchanged, with or without a line.
- Load every file; group by namespace; order namespaces by imports and
  qualified names; `E-NAMESPACE-CYCLE`, `E-NAMESPACE-FAILED`. One
  `elaborate_module` per namespace with its prefix (§11 rows 1-3).
- Qualified names and `import N (names)` across namespaces; per-file
  imports; `E-DUPLICATE` and `E-IMPORT-CLASH` across files.
- `E-FOREIGN-NAMESPACE`; `auto` by §4.8's table.
- Type hashes from the namespace; ability order by full name.
- CLI: `run NAME` with `E-RUN-TYPE`, `E-RUN-UNKNOWN`, `E-RUN-FILE`;
  `test`/`check` of a project or a namespace with its dependencies;
  `build --js NAMESPACE`. The source interface (disk and in-memory).
- AoC: `aoc/stitchwort.yaml` (`sources: [.]`), `namespace Aoc` with
  `Range`, used by days 2 and 5; every day gets a namespace line; headers,
  `web/build.sh`, `flake.nix` and the playground's AoC entries updated
  (§9.2, pending Q6).
- **Tests:**
  - accept: a two-namespace project; one namespace over three files with
    mutual recursion across files and dot notation across files; a type's
    function found by dot notation from another namespace; qualified use
    without import;
  - reject, one per new code, each asserting its code; a three-namespace
    cycle; an import in one file not visible in a sibling;
    `E-DUPLICATE` across two files naming both;
  - `stitchwort.yaml`: empty file; unknown key; `sources: [no]`
    (refused, not `false`); duplicate key; missing folder; nested project;
  - standalone: every `examples/accept` program unchanged (the existing
    suite); a standalone file with a namespace line;
  - `auto` doesn't use a procedure from a sibling file or an unrelated
    namespace, and does use one from a dependency;
  - **stable identity**: renaming or moving a file (same namespace line)
    changes no hash, so the second run is all cache hits; two namespaces
    each declaring an identical `type Range` get different hashes;
  - `run Day05.main`; `run` of a pure `() -> ()`, a `{Partial}` one; a
    function of the wrong type; an unrelated broken namespace doesn't stop
    `run`;
  - `test Day05` runs `Aoc`'s tests too, grouped; `build --js` exports only
    the target namespace's; `run --js` across namespaces;
  - abilities from two namespaces get the same row order whatever order
    the files are read in.

**Stage 2: splitting a day.** `import N (..)` (wildcard level, below
explicit imports). AoC: day 5 split both ways of §6 as a trial (no new
compiler work beyond stage 1 and `(..)`). **Tests:** precedence (own >
explicit > wildcard > default); two wildcards ambiguous only at use; a
wildcard doesn't bring the imported namespace's own imports.

**Stage 3: extending another namespace of the project** (§4.7): `Day02`
adds `Range.invalid` to `Aoc.Range`, found by dot notation only in
`Day02`. Day 2 goes back to `r.repeated k n` and `.map (.invalid w)`.
**Tests:** the type's own namespace wins; an extension isn't visible in
another namespace; two namespaces each adding `Range.f` don't clash; `Std`
still closed.

**Stage `include`** (any time; §10).

**Later, each when needed:** cycles between namespaces (one project-wide
graph); `auto` across sibling files by file-level order; `run Day05` as
`Day05.main`; `import N as M`; re-exports; `private`; namespace blocks;
dependencies between projects (and a project name in type hashes); a
per-namespace elaboration cache; the cache at the project folder.

## 13. Questions for Matt

Short; each has a recommendation.

- **Q1. Shared namespace name**: one `Aoc` namespace for all shared AoC
  code (`Aoc.Range`, later `Aoc.Grid`), or a namespace per topic
  (`namespace Range`, giving `Range.Range`)? *Recommendation: `Aoc`.*
- **Q2. Project files without a namespace line**: error (recommended), or
  a default namespace?
- **Q3. Cycles between namespaces**: refused for now (recommended), or
  allowed from the start (one project-wide graph, more work)?
- **Q4. `run file.sw` inside a project**: error naming the function to run
  (recommended), or run the file's namespace's `main`?
- **Q5. Test cache location**: stay at `.stitchwort/cache` in the working
  directory, or move to the project folder? *Recommendation: the project
  folder*; minor.
- **Q6. The playground's AoC examples**: load each day as a small
  in-memory project (recommended), or stop shipping days that use `Aoc`?
- **Q7. `aoc/` layout**: `sources: [.]` keeping files where they are
  (recommended), or move them under `aoc/src/`?

## 14. Questions for the reviewer

- **R1. Imports per file, declarations per namespace (§4.4).** Is it
  confusing that a sibling file's declarations are visible but its imports
  aren't? (Go and Kotlin do the same.)
- **R2. Namespace order from syntax (§4.6).** Is "imports plus qualified
  names whose first component is a project namespace not hidden by a local
  or own declaration" exact enough, given that a qualifier's first
  component can be the namespace's own type? Over-approximating gives
  false cycles; under-approximating checks a namespace before one it uses.
- **R3. `auto` (§4.8).** Is excluding sibling files too restrictive for
  split days? Is the priority order (same file, dependencies by reverse
  dependency order then name, `Std`) deterministic in all cases?
- **R4. Ability row order by full name (§8.1).** Does row order reach
  hashes, and is any code relying on the current (module, position) order
  for something other than determinism?
- **R5. Same-named types in two projects hashing alike (§8.1).** Acceptable
  until projects can depend on each other?
- **R6. Stage 3's extension rule (§4.7).** Visible only in the adding
  namespace, with the type's own namespace winning: does that interact
  badly with namespaces.md §4.8's alias rules for dot notation?

## Sources

- [K1] Kotlin coding conventions:
  https://kotlinlang.org/docs/coding-conventions.html
  ("The recommended directory structure follows the package structure with
  the common root package omitted"; file naming; extension functions for
  one client "next to the code of that client"). Verified 19 Oct 2026.
- [K2] Kotlin, "Packages and imports":
  https://kotlinlang.org/docs/packages.html
  ("A source file may start with a package header"; "All contents of the
  source file … belong to this package"; "If a file has no package header,
  its contents belong to the root package"; a package is "a container for
  one or more Kotlin files"). Verified 19 Oct 2026.
- [S1] Scala 3 Book, "Packaging and Imports":
  https://docs.scala-lang.org/scala3/book/packaging-imports.html
  (package clauses; names "typically follow directory structure", not
  required). From draft 1.
- [G2] The Go Programming Language Specification, "Packages" and "Import
  declarations": https://go.dev/ref/spec#Packages
  ("A package in turn is constructed from one or more source files that
  together declare constants, types, variables and functions belonging to
  the package and which are accessible in all files of the same package";
  "It is illegal for a package to import itself, directly or indirectly").
  Verified 19 Oct 2026.
- [H2] GHC User's Guide, `-main-is`:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/phases.html
  ("A qualified name `A.foo`. GHC assumes that the main function is
  `A.foo`"; "A module name `A`. GHC assumes that the main function is
  `A.main`"). Verified 19 Oct 2026.
- [U2] Unison, `run`:
  https://www.unison-lang.org/docs/ucm-commands/run
  ("takes a delayed computation"; looked up "in the most recent typechecked
  file, or in the codebase"; "can return any type, and may perform the IO
  and Exception abilities"). Verified 19 Oct 2026.
- [Y1] crates.io, `serde_yaml`: https://crates.io/crates/serde_yaml
  (latest `0.9.34+deprecated`, 25 Mar 2024); repository archived:
  https://github.com/dtolnay/serde-yaml. Verified 19 Oct 2026 via the
  crates.io and GitHub APIs.
- [Y2] crates.io, `serde_yml`: https://crates.io/crates/serde_yml
  (description: "DEPRECATED — `serde_yml` is unmaintained … Please migrate
  to `noyalib`"). Verified 19 Oct 2026.
- [Y3] RustSec, RUSTSEC-2025-0068:
  https://rustsec.org/advisories/RUSTSEC-2025-0068.html
  (`serde_yml` unsound and unmaintained; suggests `serde_norway` or
  `serde_yaml_ng`). Verified 19 Oct 2026.
- [Y4] crates.io, `serde_norway`: https://crates.io/crates/serde_norway
  (latest 0.9.42, 21 Dec 2024). Verified 19 Oct 2026.
- [Y5] crates.io, `noyalib`: https://crates.io/crates/noyalib
  (0.0.58; first published May 2026). Verified 19 Oct 2026.
- [Y6] `serde-saphyr` README:
  https://github.com/bourumir-wyngs/serde-saphyr
  (sections "Booleans", "Duplicate keys", budgets; "not a fork of the older
  `serde-yaml`"); crates.io: https://crates.io/crates/serde-saphyr (2.0.0,
  13 Oct 2026, MIT OR Apache-2.0, MSRV 1.89). Verified 19 Oct 2026.
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

Not checked against a source, and marked **unverified** where used: whether
Kotlin and Scala allow cycles between packages of one module (believed so);
whether Kotlin subpackages see their parent package's names without an
import (believed not); whether Lean refuses import cycles; Rust's
cycles within a crate.
