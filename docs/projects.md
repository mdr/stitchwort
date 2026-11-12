# Projects: several files and namespaces

**Status:** describes multi-file stages 1 and 2 (`import N (..)`).

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
file under them, at any depth, belongs to the project; symlinks are skipped.
Folders whose names start with `.` are skipped, so `.stitchwort/` and `.git/`
are ignored. Files that aren't `.sw` are ignored. A folder that doesn't
exist, or a source path that is absolute or contains `..`, is an error. So is
a `stitchwort.yaml` inside another project. `sources` must be a list:
`sources: src` (a bare string) is `E-PROJECT-CONFIG`. The other keys are
`audit:`, whose `allowed-axioms:` lists the axioms `stitchwort audit` allows
(default `Quot.sound`), and `check:`, whose `open-goals:` is `warn` or `fail`
(default): with `warn`, `stitchwort check` reports each open goal `?` as a
warning and exits 0 if nothing else fails, and `stitchwort test` runs the tests
that don't use an unfinished declaration and reports the others as skipped,
naming the declaration with the open goal, exiting 0 if nothing else fails
(`audit` still fails unfinished theorems). An unknown key, or a value other
than those, is an error.

A flat layout uses `sources: [.]`.

## Namespaces

Every file in a project starts with a namespace line. Comments and blank
lines may come before it. Imports come after it.

```
-- src/range.sw
namespace Aoc
import Std (Text)

-- A range of ids, both ends included.
type Range = { from: Nat, to: Nat }

def Range.parse (t: Text): Option Range :=
  match (t.split '-').map Text.toNat with
    | [Some from, Some to] => Some { from, to }
    | _                  => None

def Range.size (r: Range): Nat := r.to + 1 - r.from
```

```
-- src/day05.sw
namespace Day05
import Aoc (Range)
import Std (IO, Nat, Text)

type Database = { fresh: List Range, available: List Nat }

def parseDatabase (lines: List Text): Database :=
  { fresh = lines.filterMap Range.parse,
    available = lines.filterMap Text.toNat }

def solvePart1 (db: Database): Nat :=
  (db.fresh.map Range.size).sum

def main(): {IO} () :=
  let lines := IO.readAllLines()
  IO.print (Nat.toText (solvePart1 (parseDatabase lines)))
```

The rules:

- **Exactly one namespace line per file**, and it must come first; only
  comments and blank lines may come before it. A namespace line after an
  import or a declaration is `E-NAMESPACE-NOT-FIRST`, pointing at it. A
  second namespace line is `E-PARSE` with a note.
- **Several files may share a namespace.** All files that say
  `namespace Day05` together make one namespace.
- **File names and folders mean nothing.** `range.sw` could be called
  `helpers.sw` and nothing would change. A file's namespace comes from its
  first line, not its path. (The `aoc/` project, by convention, keeps folders matching namespaces:
  `Aoc.Year2025.Day02.Tests` and `Aoc.Year2025.Day02.Proofs` live in `src/Aoc/Year2025/Day02/Tests/` and `.../Proofs/`, and hold the tests and theorems that
  `Aoc.Year2025.Day02` leaves out so that running the day does not check them.)
- **Every declaration of a namespace is visible to all its files by short
  name**, in any order. Definitions in different files can call each other,
  including mutual recursion.
- **A name declared twice in one namespace is `E-DUPLICATE`**, naming both
  places and both files when they differ.
- **Dotted names make separate namespaces.** `namespace Aoc.Year2025.Day05` is a
  namespace; it does not make the names of `Aoc` visible. Import them or
  write them qualified.
- **Library names are reserved.** `namespace Std` is `E-STD-NAMESPACE`. A
  namespace whose first component is a library namespace, such as
  `namespace List` or `namespace Text.Extra`, is `E-NAMESPACE-RESERVED`.
  `Main` is also reserved: a namespace whose first component is `Main`, such
  as `namespace Main` or `namespace Main.Extra`, is `E-NAMESPACE-RESERVED`,
  because `Main` is the implicit namespace of a file without a namespace
  line.
- **A namespace may add functions to another namespace's type.** In
  namespace `Aoc.Year2025.Day02`, with `Aoc.Range` imported, `def
  Range.invalid (range: Range) …` declares an *extension*. It belongs to the
  namespace that wrote it: its full name is `Aoc.Year2025.Day02.Range.invalid`.
  `range.invalid` and `Range.invalid range` find it only in that namespace's
  own files and in files that import that namespace with `(..)`. Imports
  aren't passed on, and importing names by name doesn't bring extensions.
  The type's own namespace, other namespaces and `Std` don't see it, whatever
  else the command loaded; the full name works anywhere. Details:
  - The type's own function comes first, so a type whose namespace already
    has `Range.invalid` makes the extension `E-EXTENSION-CLASH`, where the
    extension is declared.
  - A namespace's own extension comes before an imported one. Two imported
    extensions of the same name are `E-AMBIGUOUS` where one is used.
  - Only functions and theorems can be added: `type Range.Part …` there is
    `E-FOREIGN-NAMESPACE`, and so is writing another namespace's name as the
    qualifier (`def Aoc.Range.invalid`; write `Range.invalid`).
  - `Std`'s types stay closed: `def List.sum2 …` is `E-STD-NAMESPACE`.
  Design: [extending-types.md](proposals/extending-types.md).

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
- **`import N` with no list is not allowed.** Write the names, or `(..)`.
- **An import's namespace is found without the other imports.**
  `import Cat (f)` means the namespace `Cat` (this namespace's own, the
  project's, or the library's), even if the file also imports a type `Cat`;
  write `import Lib.Cat (f)` for that one. Import order never matters.
- **There is no `private`.** Every declaration of a namespace can be
  imported or named from any other namespace.

### Importing everything: `import N (..)`

```
import Aoc (..)
```

brings every name declared directly in `Aoc`, from all its files: its
types (with their constructors), abilities (with their operations) and
definitions. It doesn't bring names inside them (`Range.size` is still
written `Range.size`, or `size` after `import Aoc.Range (size)`), `Aoc`'s
own imports, or namespaces under it such as `Aoc.Grid` (import one by name
for that, `import Aoc (Grid)`: see below).

- **Lowest priority among imports.** A short name means, first found: a
  local variable; a declaration of this namespace (any file); a name this
  file imports by name; a name a `(..)` import brings; the default names
  (`Nat`, `Option`, `not`, ...). So your own declarations and named imports
  win silently, and a `(..)` import can hide a default name.
- **Two `(..)` imports may bring the same name.** That's only an error
  (`E-AMBIGUOUS`) where the name is used. Write it in full, or import the
  one you mean by name: `import Aoc (merge)` beats any `(..)`.
- **It names a namespace with its own namespace line, or one of the
  library's** (`import List (..)` works in single files too). Not the
  file's own namespace, not `Std` itself, and not a type or other part of a
  namespace (`import Aoc.Range (..)`): those are `E-IMPORT-WILDCARD`.
- **`(..)` goes alone**: `import Aoc (Range, ..)` is `E-PARSE`.
- **Per file, and not passed on**, like any import.
- **It counts as using `N`**: `N` is checked first, a cycle through it is
  `E-NAMESPACE-CYCLE`, and `N`'s decision procedures become `auto`
  candidates.
- **A wildcard name can also be a qualifier.** If `Aoc` declares `Range`,
  `Range.parse` means `Aoc.Range.parse`; if it declared a type `Text`,
  `Text.split` would mean `Aoc.Text.split` (write `Std.Text.split`).

### Importing a namespace by its last name: `import P (S)`

```
namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day13 (Spec)

theorem withinCorrect (machine: Machine):
  machine.fewestTokensWithin 100 = Spec.fewestTokens machine := …
```

An import item may be a namespace under the import's namespace. Then the
item's name is a qualifier for that namespace in this file: `Spec.x` means
`Aoc.Year2024.Day13.Spec.x`. Nothing in it is imported: `x` alone still
needs `import Aoc.Year2024.Day13.Spec (x)` or `(..)`. The library works the
same way (`import Std (Eq)`, then `Eq.sym`).
([import-aliases.md](proposals/import-aliases.md))

- **It counts as using the namespace**, which is checked first, whatever
  the order of the namespaces' names (`Day13.Proofs` sorts before
  `Day13.Spec`). A cycle through it is `E-NAMESPACE-CYCLE`.
- **The module's own names come first.** If this namespace declares `Spec`,
  or has a namespace `Spec` of its own (from `def Spec.f`), the item is
  `E-IMPORT-CLASH`.
- **It never hides another meaning silently.** If `Spec` also means
  something else here (a second `import Day12 (Spec)`, a type `Spec` from
  an import or a `(..)`, a root namespace `Spec`, or a prelude name such as
  `List`), each use of `Spec.x` is `E-AMBIGUOUS`, which lists the full
  names. Write one in full, or import only one `Spec`.
- **`Spec` alone names nothing** (`E-UNKNOWN-NAME`, with a note).
- **Per file, and not passed on**, like any import. `(..)` doesn't bring
  sub-namespaces: `import Aoc.Year2024.Day13 (..)` gives no `Spec.`.
- **Goals print it short.** A goal writes `Spec.fewestTokens` where that
  means the same declaration in the file, so it can be pasted back. Hashes
  don't depend on how a name was written.
- **There is no `import M as A`.** It is `E-PARSE`, with a note giving the
  item form. To use another name, rename the item: `import
  Aoc.Year2024.Day13 (Spec as S)`, then `S.fewestTokens`.

### Importing a name under another name: `import M (x as y)`

`import Aoc (Range as Span)` makes `Span` mean `Aoc.Range` in this file
(and `Span.size` mean `Aoc.Range.size`); it doesn't bring `Range`. A
type's constructors keep their own names. Clashes are as for any import:
`E-IMPORT-CLASH` with a declaration of the file's, `E-AMBIGUOUS` where a
name two items share is used. Goals and messages print `Span`, and hashes
are as if the name were written in full. See
[syntax.md](syntax.md#namespaces-and-imports).

## Cycles between namespaces

Namespaces are checked one at a time, each completely, in dependency order.
`N` depends on `M` if a file of `N` imports from `M` (by name or with `(..)`), or writes a qualified
name that resolves into `M`.

- **Cycles are refused for now** (`E-NAMESPACE-CYCLE`). Two definitions in
  different namespaces can't call each other. Put them in one namespace,
  which may span files, or move what both need into a third namespace.
- **Cycles inside one namespace are fine.** Its files and declarations may
  refer to each other in any order.
- **An error stops only what needs it** (D3524, D3527). If a declaration in
  `Aoc` has an error, every namespace is still checked, declaration by
  declaration, those that import `Aoc` included. A `def` or `theorem` whose
  statement checked but whose body didn't (a type error, or a syntax error
  after its `:=`) stands in for its statement, as a `?` does: what uses it is checked against the statement, its own mistakes
  are reported, and it's counted as relying on the broken declaration
  ("relies on a declaration with an error, checked assuming its
  statement"), never as finished. A declaration that has to compute through
  the broken one (`rfl` on `beats Rock Paper` while `beats` has an error),
  or uses one whose statement is broken (or a type, interface, ability or
  instance with an error), can't be checked until it's fixed; it reports
  nothing itself. Instead each file with such declarations gets one
  `E-USES-FAILED` per broken name, on its import of the name (or on the
  first declaration that waits, if the file doesn't import it by name),
  listing what waits. Everything else is checked as usual, its goals are
  shown and its tests run: a test that only cites a broken theorem as a
  proof runs, and says what it assumed. `check` still exits 1, and ends
  with a summary of the errors: which declarations have one, how many rely
  on one, and which can't be checked until one is fixed, and what each needs
  (`stitchwort test` and `audit` print the same, and `audit` still gives
  every theorem its verdict). A
  namespace with a *syntax* error may have lost a declaration altogether:
  an import of a name it no longer declares then says so once, on the
  import (`E-USES-FAILED`: "`A` has a syntax error, so `beats` can't be
  found"), pointing at the syntax error, and what uses the name waits for
  it rather than being told it is unknown. In the editor, while a namespace
  has a syntax error, the namespaces that use it aren't checked
  (`E-NAMESPACE-FAILED`) and keep the answers they had, so they don't change
  with every keystroke.

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
from `M` (by name or with `(..)`) or writes a qualified name that resolves into `M`. One such use is
enough to make all of `M`'s decision procedures candidates.

## Running and testing

The project is found by walking up from the current directory.
`--project DIR` overrides that. With a name argument, Stitchwort loads the
project:

```
stitchwort run Day05.main
```

`Day05.main` is a fully qualified function name. Any function may be run if
it has a main-like type: `() -> {IO, Fail, Partial} ()` or less, meaning a
function from `()` to `()` whose abilities are among `IO`, `Fail` and `Partial`:

```
() -> ()
() -> {IO} ()
() -> {IO, Fail} ()
() -> {IO, Partial} ()
() -> {IO, Fail, Partial} ()
```

Only the function's namespace and what it depends on are type-checked. A
namespace with type errors that the function doesn't use doesn't stop the
run. Problems found for the project as a whole before checking (a file with no
namespace line, a reserved namespace, a namespace/type clash, or a bad
`stitchwort.yaml`) stop every command, `run` included.

There is no entry-point annotation, and `main` is only a convention. In a
project a function is run by its full name, `stitchwort run Shop.report`, so
a namespace can have several programs; a type that can't be run is
`E-RUN-TYPE`, and a name that isn't in the project is `E-RUN-UNKNOWN`. A
namespace name alone (`run Day05`) names no function and is `E-RUN-UNKNOWN`
([syntax.md](syntax.md#entry-points)).

A path argument is always **file mode**:

```
stitchwort run path/file.sw
```

File mode loads that file and the standard library only, inside a project or
not. The file must have a `main`, which is the only function file mode runs. A namespace line is optional. An import
from anything but `Std`, or a qualified name reaching outside the file and
`Std`, is `E-FILE-MODE`. File mode is a reading of the file on its own, so
its meaning can differ from the project's when the file has sibling files.

The same path rule applies to the other commands:

```
stitchwort check                  -- the whole project
stitchwort check Day05            -- Day05 and what it depends on
stitchwort check Day05.Proofs --only Day05.Proofs.sumSpec,...
                                  -- only those theorems and what they use
stitchwort check path/file.sw     -- file mode

stitchwort test                   -- every test in the project
stitchwort test Day05             -- Day05's tests, its children's, and its dependencies'
stitchwort test path/file.sw      -- file mode
```

One command reads a path in the project rather than in file mode:
`stitchwort search --at path/file.sw:LINE`, what closes the goal `?` there,
reads the file in its project (found from the file's folder up), with its
namespace and imports, and searches the project's lemmas as well as the
library's ([syntax.md](syntax.md#what-closes-this--stitchwort-search---at)).

`check` accepts several names at once. `test` and `run` take a single target.
A namespace target may be dotted, as in `check Aoc.Year2025.Day05`. On success `check` prints one line to standard error, `checked 43 namespaces of aoc` (a file: `checked path/file.sw`); errors print as before and the exit status is unchanged.

`stitchwort test Day05` runs the tests of `Day05`, of every namespace under
it (`Day05.Tests`, `Day05.Proofs`), and of every namespace they depend on,
grouped by namespace. A target that matches no tests prints
`warning: no tests matched 'Day05'` and exits non-zero; `Std`'s own tests aren't run. A test moved
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
| `E-NAMESPACE-NOT-FIRST` | A namespace line comes after an import or a declaration. |
| `E-FILE-MODE` | A file run, checked or tested on its own uses something outside `Std`. |
| `E-NAMESPACE-CYCLE` | Namespaces depend on each other in a cycle. |
| `E-NAMESPACE-RESERVED` | A namespace's first component is a library namespace or `Main`. |
| `E-NAMESPACE-CLASH` | A dotted namespace name is also a type declared in its parent namespace. |
| `E-FOREIGN-NAMESPACE` | A file adds something other than a function to another namespace's type, or names another namespace as a declaration's qualifier. |
| `E-EXTENSION-CLASH` | A function added to another namespace's type has the name of one of the type's own. |
| `E-USES-FAILED` | Declarations of this file use a declaration of another namespace that has an error, so they can't be checked until it's fixed: one per broken name per file, listing what waits. Also an import of a name that namespace no longer declares because it has a syntax error (`A` has a syntax error, so `beats` can't be found). |
| `E-NAMESPACE-FAILED` | In the editor only: a namespace wasn't checked because a namespace it depends on has a syntax error. |
| `E-NAMESPACE-UNKNOWN` | A command named a namespace the project doesn't have. |
| `E-UNKNOWN-THEOREM` | `check --only` named something that is not a theorem of the namespaces being checked. |
| `E-IMPORT-WILDCARD` | `import N (..)` names the file's own namespace, `Std`, or a part of a namespace instead of a whole one. |
| `E-RUN-TYPE` | The named function doesn't have a main-like type. |
| `E-RUN-UNKNOWN` | There's no function with that full name. |

`E-STD-NAMESPACE` is unchanged: it covers `namespace Std` and its children.
Older codes also now cover projects: `E-DUPLICATE` names both files,
`E-IMPORT-CLASH` checks an import against every file of the namespace, and
`E-IMPORT-UNKNOWN`, `E-AMBIGUOUS` and `E-EXPORT` work as before. `W-IMPORT-TWICE`
also covers `(..)` written twice for the same namespace.

## Not yet

Instances for another namespace's type (orphan instances) aren't decided, and interface features beyond the current design (see [syntax.md](syntax.md#interfaces)) are not designed yet.
