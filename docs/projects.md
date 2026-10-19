# Projects: several files and namespaces

**Status:** describes multi-file stage 1, being implemented (19 October 2026); details may change.

A **project** is a folder with a `stitchwort.yaml`. It says where the `.sw`
files are. Every file says which namespace it belongs to. Several files can
share one namespace. Imports name namespaces, not files.

## A project on disk

The smallest project is a folder with an empty `stitchwort.yaml`. That means
one source folder, `src/`:

```
my-project/
  stitchwort.yaml       -- empty: sources default to src/
  src/
    range.sw            -- namespace Aoc
    day05.sw            -- namespace Day05
    day05-merge.sw      -- namespace Day05
```

Write the source folders out when they differ:

```yaml
# my-project/stitchwort.yaml
sources: [src]
```

`sources` is a list of folders relative to the project folder. Every `.sw`
file under them, at any depth, belongs to the project. Folders whose names
start with `.` are skipped, so `.stitchwort/` and `.git/` are ignored. Files
that aren't `.sw` are ignored. A folder that doesn't exist, or lies outside
the project folder, is an error. So is a `stitchwort.yaml` inside another
project. `sources` is the only key for now; an unknown key is an error.

A flat layout uses `sources: [.]`.

## Namespaces

Every file in a project starts with a namespace line. Comments and blank
lines may come before it. Imports come after it.

```
-- src/range.sw
namespace Aoc

-- A range of ids, both ends included.
type Range = { lo: Nat, hi: Nat }

def Range.parse (t: Text): Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

def Range.size (r: Range): Nat := r.hi + 1 - r.lo
```

```
-- src/day05.sw
namespace Day05
import Aoc (Range)

type Database = { fresh: List Range, available: List Nat }

def parseDatabase (lines: List Text): Database :=
  { fresh = lines.mapMaybe Range.parse,
    available = lines.mapMaybe Text.toNat }

def solvePart1 (db: Database): Nat :=
  (db.fresh.map Range.size).sum

def main(): {IO} () :=
  let lines := IO.readAllLines()
  print (Nat.toText (solvePart1 (parseDatabase lines)))
```

The rules:

- **Exactly one namespace line per file**, at the top. A second one, or one
  after an import or a declaration, is `E-PARSE` with a note.
- **Several files may share a namespace.** All files that say
  `namespace Day05` together make one namespace.
- **File names and folders mean nothing.** `range.sw` could be called
  `helpers.sw` and nothing would change. A file's namespace comes from its
  first line, not its path.
- **Every declaration of a namespace is visible to all its files by short
  name**, in any order. Definitions in different files can call each other,
  including mutual recursion.
- **A name declared twice in one namespace is `E-DUPLICATE`**, naming both
  places and both files when they differ.
- **Dotted names make separate namespaces.** `namespace Aoc.Day05` is a
  namespace; it does not make the names of `Aoc` visible. Import them or
  write them qualified.
- **Library names are reserved.** `namespace Std` is `E-STD-NAMESPACE`. A
  namespace whose first component is a library namespace, such as
  `namespace List` or `namespace Text.Extra`, is `E-NAMESPACE-RESERVED`.
- **You can't add to another namespace.** In namespace `Day02`, writing
  `def Range.invalid …` for an `Aoc.Range` is `E-FOREIGN-NAMESPACE`. Give
  the function a name in `Day02` instead.

A sibling file's declarations are visible without an import:

```
-- src/day05-merge.sw
namespace Day05

def countFresh (db: Database): Nat :=
  (db.fresh.map Aoc.Range.size).sum
```

`Database` comes from `day05.sw`. `Aoc.Range` is a qualified name. Neither
needs an import here.

## Imports

Imports are per file:

```
import Aoc (Range)
```

The listed names become visible by short name in that file. Importing a type
also brings its constructors.

- **Qualified names need no import.** Anywhere in the project,
  `Aoc.Range.parse t` works.
- **Imports aren't passed on.** `import Aoc (Range)` in `day05.sw` does not
  let `day05-merge.sw` write `Range`. To use the short name there, that file
  writes its own import. The file above writes `Aoc.Range.size` instead.
- **Sibling files share declarations, not imports.** `day05-merge.sw` can
  see everything declared in `Day05`. It cannot see `day05.sw`'s imports.
- **`import N` with no list is not allowed.** Write at least one name.
  `import N (..)` is planned for stage 2, not available now.
- **There is no `private`.** Every declaration of a namespace can be
  imported or named from any other namespace.

## Cycles between namespaces

Namespaces are checked one at a time, each completely, in dependency order.
`N` depends on `M` if a file of `N` imports from `M`, or writes a qualified
name that resolves into `M`.

- **Cycles are refused for now** (`E-NAMESPACE-CYCLE`). Two definitions in
  different namespaces can't call each other. Put them in one namespace,
  which may span files, or move what both need into a third namespace.
- **Cycles inside one namespace are fine.** Its files and declarations may
  refer to each other in any order.
- **A broken namespace doesn't stop unrelated ones.** If `Aoc` has errors,
  namespaces that depend on it aren't checked and get `E-NAMESPACE-FAILED`.
  Namespaces that don't depend on it are checked normally.

## `auto` across files

`auto` looks for decision procedures in this order:

1. hypotheses in scope and procedures passed as arguments;
2. the same file, above the use;
3. every namespace this one depends on, then `Std`.

It does **not** look in sibling files of the same namespace, and it does not
look in namespaces this one doesn't depend on. Moving a decision procedure
to another file of the same namespace can therefore break an `auto` that
found it. The `E-AUTO-NONE` hint names the file; pass the procedure
explicitly to fix it.

A namespace `M` counts as depended on if a file of this namespace imports
from `M` or writes a qualified name that resolves into `M`. One such use is
enough to make all of `M`'s decision procedures candidates.

## Running and testing

The project is found by walking up from the current directory.
`--project DIR` overrides that. With a name argument, Stitchwort loads the
project:

```
stitchwort run Day05.main
```

`Day05.main` is a fully qualified function name. Any function may be run if
it has a main-like type: `() -> {IO, Partial} ()` or less, meaning one of

```
() -> ()
() -> {IO} ()
() -> {Partial} ()
() -> {IO, Partial} ()
```

Only the function's namespace and what it depends on are checked. A broken
unrelated namespace doesn't stop the run.

A path argument is always **file mode**:

```
stitchwort run path/file.sw
```

File mode loads that file and the standard library only, inside a project or
not. The file must have a `main`. A namespace line is optional. An import
from anything but `Std`, or a qualified name reaching outside the file and
`Std`, is `E-FILE-MODE`. File mode is a reading of the file on its own, so
its meaning can differ from the project's when the file has sibling files.

The same path rule applies to the other commands:

```
stitchwort check                  -- the whole project
stitchwort check Day05            -- Day05 and what it depends on
stitchwort check path/file.sw     -- file mode

stitchwort test                   -- every test in the project
stitchwort test Day05             -- Day05's tests and its dependencies'
stitchwort test path/file.sw      -- file mode
```

`stitchwort test Day05` runs the tests of `Day05` and of every namespace it
depends on, grouped by namespace; `Std`'s own tests aren't run. A test moved
between files of one namespace keeps its result.

Results are cached in `.stitchwort/cache` in the **project folder**,
whatever directory the command runs from. When Stitchwort creates
`.stitchwort/`, it writes `.stitchwort/.gitignore` containing `*`, so you
don't edit your own `.gitignore`. File mode keeps today's location: under
the working directory. `--cache-dir` overrides both.

## Errors you may see

| Code | Meaning |
|---|---|
| `E-PROJECT-CONFIG` | `stitchwort.yaml` is invalid: unknown key, bad value, missing or outside source folder, or a nested project. |
| `E-NO-NAMESPACE` | A file in a project has no namespace line. |
| `E-FILE-MODE` | A file run, checked or tested on its own uses something outside `Std`. |
| `E-NAMESPACE-CYCLE` | Namespaces depend on each other in a cycle. |
| `E-NAMESPACE-RESERVED` | A namespace's first component is a library namespace. |
| `E-NAMESPACE-CLASH` | A dotted namespace name is also a type declared in its parent namespace. |
| `E-FOREIGN-NAMESPACE` | A file adds a declaration to another namespace. |
| `E-NAMESPACE-FAILED` | A namespace wasn't checked because a namespace it depends on has errors. |
| `E-RUN-TYPE` | The named function doesn't have a main-like type. |
| `E-RUN-UNKNOWN` | There's no function with that full name. |

`E-STD-NAMESPACE` is unchanged: it covers `namespace Std` and its children.
Older codes also now cover projects: `E-DUPLICATE` names both files,
`E-IMPORT-CLASH` checks an import against every file of the namespace, and
`E-IMPORT-UNKNOWN`, `E-AMBIGUOUS` and `E-EXPORT` work as before.

## Not in stage 1

Adding definitions to another namespace waits for its own design; `import N (..)` is stage 2, and interfaces are planned but not designed yet.
