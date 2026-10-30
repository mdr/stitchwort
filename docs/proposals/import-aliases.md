# Import aliases: `Spec.x` for a namespace you import

**Status:** draft 1, 30 October 2026 (SW-804, D2071). Design only; nothing
is built. Decisions for Matt are D2072-D2074 (§9). A brief for an outside
reviewer is [import-aliases/review-brief.md](import-aliases/review-brief.md).

**In one paragraph.** The ticket asked for `import M as A`. The evidence for
it is four lines, and none of them needed a full name: the two
`fewestTokens` they tell apart don't clash (§2.1, probed). What the evidence
*does* show is that agents reach for `Spec.fewestTokens` and get
`E-UNKNOWN-NAME`. The language already has a way to say this, for the
library only: `import Std (Eq)`, then `Eq.sym`. docs/syntax.md says an
import item "may be any sub-namespace", but for a project namespace the
import is accepted and does nothing, or is refused, depending on the order
the namespaces happen to be checked in (§3.4). **Recommendation:** make that
documented form work for project namespaces (`import Aoc.Year2024.Day13
(Spec)`, then `Spec.fewestTokens`), with no new syntax (D2072); let `import
N (..)` also bring `N`'s sub-namespaces as qualifiers, as Agda's `open` does
(D2073); and don't add `as` or per-name renaming now. Instead `as` gets an
error that points at the item form (D2074). Nothing here changes a hash.

Contents: 1 Problem · 2 Evidence · 3 Current system · 4 Other languages ·
5 Options · 6 Recommendation · 7 Plan · 8 Risks · 9 Decisions · 10 Sources

## 1. Problem

A file imports names (`import Aoc.Year2024.Day13.Spec (part1,
winningCosts)`) or all of a namespace's names (`(..)`). If it needs a name
it hasn't imported, or two imported names clash, the only way to write it is
the full name, `Aoc.Year2024.Day13.Spec.fewestTokens`. The middle way,
`Spec.fewestTokens`, is `E-UNKNOWN-NAME`. AoC correctness theorems compare a
program with its spec, and in those the qualified spelling reads well:
`machine.fewestTokensWithin 100 = Spec.fewestTokens machine` says which side
is the spec.

## 2. Evidence

### 2.1 Full names written today

Method: every `.sw` file under `aoc/`, `games/`, `examples/` and
`crates/elab/src/std/`. Lines starting `import`, `namespace` or `--` are
skipped, and so are strings and trailing comments. Counted: names starting
with `Aoc.`, `Rogue.` or `Std.` that have at least one more component
(script `fullnames.py`, run 30 Oct).

| Where | Full names | Lines |
|---|---|---|
| aoc | 4 | `Aoc/Year2024/Day13/Proofs/Part1.sw:89`, `:102`; `Aoc/Year2024/Day13/Tests/Examples.sw:88`, `:95`, all `Aoc.Year2024.Day13.Spec.fewestTokens` |
| games/rogue | 0 | |
| std | 0 | |
| examples | 14 | `projects/accept/no-false-cycle/src/n.sw:7,9` (`Aoc.MkAoc`, a test of the dependency pre-pass); 12 `Std.…` in `accept/namespaces.sw:26,38,39,71`, `accept/not-equal-bool-in-statement.sw:10`, `accept/proofs-under-lambda.sw:9`, `accept/std-qualified-eq.sw:2`, `goals/sections.sw:14`, `reject/hidden-constructor.sw:8`, `reject/microtype-map-custom-order.sw:13`, `reject/std-namespace-qualified.sw:4`. These test the full-name rules themselves |

So **four lines in real code**, all on day 13.

**None of the four is a clash.** Day 13's program defines
`Machine.fewestTokens`, a method (`Day13.sw:114`), and its spec defines a
plain function, `fewestTokens` (`Spec/Spec.sw:28`). The short name
`fewestTokens` names only the spec's. I added `fewestTokens` to each file's
`import Aoc.Year2024.Day13.Spec (…)` and wrote the short name. Both
namespaces then check, and day 13's 25 tests pass ("25 passed, 0 failed").
Both edits were reverted. The day 13 lane believed there was a clash
(aoc/NOTES-2024.md:3825-3828: "the spec's `fewestTokens` and the program's
clash in the tests, and `import Aoc.Year2024.Day13.Spec as Spec` gives
`[E-PARSE]`"). Ranked item 10 asks for an alias form (:3997).

### 2.2 Clashes in the agents' notes

Searched: aoc/NOTES-2024.md (8,051 lines), games/rogue/NOTES.md,
games/rogue/PROOFS.md, docs/aoc-2025.md, and docs/research/agentic-proving.md
§5. Search terms: clash, ambiguous, rename, qualif, alias, `as`,
E-AMBIGUOUS, E-IMPORT.

| Where | What | Would an alias have helped? |
|---|---|---|
| NOTES-2024.md:3825, 3997 | Day 13, above: not a real clash | The lane's first try was `import … as Spec` |
| NOTES-2024.md:7926-7930 | Day 24: `Carries` was both a constructor of the program's `BitCheck` and the spec's relation. `E-AMBIGUOUS`; the constructor was renamed `Passes` | Yes: `Spec.Carries` |
| NOTES-2024.md:1785-1793, 3878-3879, 7574-7578, 7950-7952 | `W-LAMBDA-SHADOW`: a parser name brought in by `(..)` (`equation`, `machine`, `computer`, `gate`, `wire`) was hidden by a lambda parameter; renamed | No. A qualified import would avoid bringing the name in, but these files want the rest of `(..)` |
| NOTES-2024.md:7915-7925 | `And` hidden by a spec's `And`; message didn't say which | No (a message issue) |
| rogue NOTES.md:107-118 | Two constructors named `Quit` in one file | No (resolution by expected type) |
| agentic-proving.md §5 | Friction categories A-K over all lanes: none is names or imports | |

How names are kept apart today: 138 files import a day's `Spec`, 115 of them
with `(..)`, usually next to `import <day> (..)` for the program. That works
because the spec and the program use different names (`part1` and
`solvePart1`). Only 1 of 33 days declares a short name in both (day 23,
`password`), and no proof uses it.

**Strength of the evidence: weak.** One real clash (day 24), worked around
by a rename. One false belief in a clash (day 13), which ended with a full
name. One failed attempt at `as`. The lanes avoid clashes by naming, and
the counts don't show that this costs much. The stronger signal is
discoverability: an agent's first guess was `import … as Spec`, and the
orchestrator's was `Spec.fewestTokens` (SW-804).

## 3. The current system

### 3.1 Syntax

- `Import { path, items, everything, span }` (crates/syntax/src/ast.rs:919-933).
  The parser takes `import`, an upper-case path, then `(` and either `..`
  or one or more names (parser.rs:1099-1157). Imports must come before the
  first declaration (parser.rs:152-166).
- A qualified name is **one token** (`Tok::Upper`/`Tok::Lower` with dots;
  lexer.rs:380-388). `as` is not a keyword (lexer.rs:389-425), so it lexes
  as an ordinary lower-case name, and `import M as A` fails with
  `E-PARSE: expected `(` and the names to import, but found `as``.

### 3.2 Keys and the five levels

- Every declaration has a **key**, its full name (`Std.List.length`,
  `Aoc.Year2024.Day13.Spec.fewestTokens`). A type or ability owns the
  namespace of its name (scope.rs:1-21).
- A short name is looked up at levels Module, Import, Wildcard, Default
  (`Level`, scope.rs:75-87; `resolve_short_in`, :787-843; `candidates`,
  :847-950). The first level that has it decides. Two different things at
  one level are `E-AMBIGUOUS`, but only where the name is used.
- Per-file tables: `imports` (short name to keys) and `wildcards`
  (scope.rs:113-135). Imports are per file and never passed on.

### 3.3 Qualifiers

`qualifier` (scope.rs:180-220) reads the first component `A` of `A.b.c` in
this order:

1. `Std`;
2. a short name at the levels above (a type or ability, so `Machine.x`
   works after `import … (Machine)` or `(..)`);
3. a namespace of the file's own (not a project namespace nested under
   it: `Grid.f` inside `Aoc` doesn't reach `Aoc.Grid`, tested by
   `examples/projects/reject/nested-short-name`; multi-file.md:370);
4. a root project namespace (`Aoc`);
5. a library namespace, **only if this file imports it by name**
   (`library_namespace`, scope.rs:528-544). This is how `import Std (Eq)`
   followed by `Eq.sym` works.

The rest of the name is resolved by longest prefix (`resolve_any`,
scope.rs:693-778). The dependency pre-pass uses the same `qualifier`
routine through the trait `QualifierLevels` (project.rs:425-480), so
checking and the namespace order agree.

### 3.4 Namespace items: documented for all, built for `Std` only

docs/syntax.md:275 says "An item may be any sub-namespace, including one
that declares no name of its own (`import Std (Eq)`, then `Eq.sym`)".
`add_imports` does accept a namespace as an item (scope.rs:1668-1672: the
key is a declaration *or* `is_namespace`) and records `Spec ↦
Shop.Spec`. But a short name is only found if its key is a declaration
(`candidates` calls `scope.entry`), and step 5 above only looks for
`Std.<first>`. Two bugs follow, both run on 30 October:

- **Accepted, then unknown.** With `import Shop (Spec, total)` and `import
  Shop.Spec (..)`, the import is accepted and `Spec.total` is
  `E-UNKNOWN-NAME`. The same happens in aoc with `import Aoc.Year2024.Day13
  (Spec)` (probed, reverted).
- **The order of checking decides.** Without the second import, the same
  item is `E-IMPORT-UNKNOWN: `Shop` has no `Spec``. The pre-pass makes an
  edge only to the import's path (project.rs:326-333), not to an item that
  is a namespace. So `Shop.Spec` may be checked after `Shop.Proofs`
  (namespaces are taken by full name: `Proofs` < `Spec`), and is then not
  yet a namespace when the import is read.

### 3.5 `(..)`

`import N (..)` brings every name declared directly in `N`, at the Wildcard
level. docs/projects.md:179 states that it does *not* bring "namespaces
under it such as `Aoc.Grid`". A type it brings works as a qualifier
(projects.md:196-199). `(..)` of a project namespace also makes that
namespace's extensions (`def Grid.probe` declared in another namespace)
visible to dot calls (scope.rs:1179-1212).

### 3.6 Dot calls and methods

`x.f` takes `x`'s type head and looks for `T.f` by key
(docs/proposals/namespaces.md §4.8). It never reads a written qualifier,
so aliases can't affect it. Extensions are visible through `(..)` only
(scope.rs:1181).

### 3.7 Printing names (SW-918)

`Printer::short_name` (crates/core/src/pretty.rs:427-456) takes a
declaration's full name and tries its trailing parts, shortest first
(`fewestTokens`, `Spec.fewestTokens`, …). It prints the first one that
`NameScope::names` says means that declaration in this file. The
elaborator's `names` is `resolve_any` plus an identity check
(scope.rs:2000-2018). `full_name` is `declaration_key_of` (scope.rs:1396-1412).
Goals use the same scope (`GoalScope`, goals.rs:99-104). So **any qualifier
that resolves to the namespace by its own last name is printed with no
change to the printer.** A qualifier with a *different* name (`as S`)
would not be found: the printer would fall back to the full name. That is
still correct, just long. Messages use a simpler routine, `written`
(scope.rs:1384-1393), which tries only the key without `Std.`, then the
full key. Today `E-AMBIGUOUS` prints `Shop.Spec.total` (run).

### 3.8 Tools

- **LSP** (crates/cli/src/lsp.rs:83-100): definition, hover, references,
  symbols, formatting. Completion offers only named arguments (:355-388).
  There is no rename. A qualified name is one token and one reference in the
  index, so `Spec.x` will hover and jump like `x`. An import item is
  recorded only if it is a declaration (`note_import`, nav.rs:521-529), so
  a namespace item has no hover today.
- **`fmt`** works on tokens and has no import-specific layout
  (crates/fmt/src/layout.rs:569-572). No new tokens means no change.
- **Hashes.** A definition's hash leaves out its name, and a data type's
  includes its full key (namespaces.md §0). Resolution only chooses the key,
  so a spelling can't change a hash. The check cache's key for a namespace
  includes its files' text (check-cache.md D279), so changing an import
  re-checks the namespace.

## 4. Other languages

What I read (§10): 11 pages of primary documentation, each through a
summarising fetch, with quoted passages. "Stated" means the text says it.
"Inferred" means I concluded it from what the text says. "Unverified"
means the pages I read don't settle it.

| Language | Rename a module | Use a sub-module by its last name | Glob brings sub-modules? | Rename one name | Clash rule |
|---|---|---|---|---|---|
| Haskell 2010 | `import qualified M as N`; then only `N.x` (§5.3.2, 5.3.4). Several modules may share one `as` name "provided that all names can still be resolved unambiguously" (§5.3.3) | No (hierarchical names are just names) | n/a | No | Error "only reported if y is actually mentioned" (§5.5.2). One entity reached two ways isn't ambiguous |
| Rust | `use a::b as c` ("change the name of an imported entity") | Yes: `use crate::stuff::{self}` then `stuff::bar()`; `use path::m` binds `m` | "all importable entities" (stated); modules are items, so yes (inferred) | `use m::f as g` | Items and named imports shadow glob names (stated); duplicate named bindings are an error |
| Lean 4 | **None** on the pages read; `export` aliases single names "completely transparent[ly]" | Inside `namespace A`, `B.x` is tried as `A.B.x` ("a prefix of the current namespace appended to the identifier"); `open A` then `B.x`: unverified | `open A.B` makes `A.B.x` visible as `x` (stated) | `open X renaming a → b` | Several candidates: elaborate each, error unless exactly one succeeds (overloading by type) |
| Scala 3 | `import scala.annotation as ann`, `import java as j` | Yes: import a package or object by name | `*` excludes givens and extensions; `given` selector imports them | `import A.{min as minimum}`; hide with `as _` | (not read) |
| OCaml | `module M = A.B` is a type-level alias; with `-no-alias-deps` no link dependency until used | Via aliases or `open` | `open M` "simply affects the parsing of the following items"; `include` re-exports | No | (not read) |
| Python | `import a.b.c as d` binds `d` to the leaf | `from a.b import c` binds the sub-module `c` (stated: it tries "a submodule with that name") | `from m import *`: public names (`__all__`) | `from a import b as c` | Last binding wins |
| Agda | `import M as M'` "when the name of an imported module clashes with a local module" | After `open A`, "`qname` can itself be a qualified name", so `B.x` for `A.B.x` (stated) | Yes (same rule) | `open A renaming (ys to zs)`; `using`, `hiding` | "allow the introduction of ambiguous names, but give an error if an ambiguous name is used" |
| Idris 2 | `import Data.List as L`; `import public` re-exports, and combines with `as` | Unverified | n/a | No | Ambiguity resolved by qualification or by type |

**What the comparison says** (inferred):

1. Renaming a whole module (`as`) is common: Haskell, Rust, Scala, Python,
   Agda, Idris 2, OCaml. Lean 4, the closest relative in purpose, has none.
   It relies on namespace-relative names and `open` instead.
2. **Reaching a sub-module by its own last name** is in Rust (`use
   path::m`), Python (`from pkg import sub`), Scala, and Agda (`open A`,
   then `B.x`). Stitchwort already has this for `Std`.
3. **Renaming single names** (Lean `renaming`, Agda `renaming`, Rust,
   Scala, Python) gives one declaration two spellings in one file. No
   language I read treats it as more than a convenience.
4. Every language except Lean (which overloads) reports a clash only where
   the name is used. Stitchwort already does this.

## 5. Options

| | Form | For | Against |
|---|---|---|---|
| (a) | `import Aoc.Year2024.Day13.Spec as Spec`, then `Spec.x` | What the lane tried first. Familiar from Haskell, Python, Idris, Agda. Allows any name | New syntax (`as` becomes a contextual keyword in imports). One namespace gets different names in different files (`S`, `Sp`, `Spec`). The printer needs a new step to print `S.x`, or prints the full name (§3.7). It overlaps the item form, which must work anyway (§3.4) |
| (b) Lean-style | `Spec.x` resolved through the enclosing namespaces, with no import | Nothing to write | Was decided against: nesting is by name, not scope (multi-file.md:370, `nested-short-name`). Silent, and changes the meaning of existing names. The pre-pass would need to try every prefix |
| (b′) item | `import Aoc.Year2024.Day13 (Spec)`, then `Spec.x` | **No new syntax.** Already documented (syntax.md:275), and already works for `Std`: fixes two bugs (§3.4). One spelling per namespace, its own last name, so `grep Spec.` finds every use. Goals print `Spec.x` with no printer change (§3.7). Matches Rust `use path::m` and Python `from pkg import m` | Can't pick a different name. Two namespaces with the same last name (`Day12.Spec`, `Day13.Spec`) are ambiguous at use, and one of them must be written in full |
| (b″) | (b′), plus `import N (..)` brings `N`'s sub-namespaces as qualifiers | Day 13's proofs already have `import Aoc.Year2024.Day13 (..)`, so `Spec.fewestTokens` would just work, as the orchestrator expected. Agda's rule | More implicit names. Reverses projects.md:179. Needs a pre-pass edge when such a qualifier is used |
| (c) | `import M (x as y)` | Fixes a clash of two short names in place | One declaration, two names in a file: `grep` and readers must know both. Goals must print `y` (an alias in the printer's table). No evidence of need |
| (d) | Nothing | No work | Leaves the §3.4 bugs, and the documented rule false |

## 6. Recommendation

**(b′) now; (b″) as stage 2; not (a) or (c) for now.** The rest of this
section specifies (b′) and (b″).

### 6.1 Syntax and grammar

No change. An import item is already `Upper | Lower` without dots
(parser.rs:1131-1139):

```
import_decl ::= "import" Path "(" ( ".." | item ("," item)* ) ")"
item        ::= Name            -- a declaration, or (new for projects) a namespace
```

### 6.2 Resolution rules

R1. **A namespace item.** `import P (S)`, where `P.S` is a namespace and
not a declaration, binds `S` in this file as a qualifier for `P.S`. `P.S`
may have files of its own (`Aoc.Year2024.Day13.Spec`) or only be a prefix
of keys (`Std.Eq`). The library's case is unchanged. It is per file and
not passed on, like every import.

R2. **Where it sits.** At the Import level, among the candidates of step 2
of `qualifier` (§3.3). One mechanism then serves `Std` and project items.
`library_namespace` (step 5) is folded into it. That moves `Std` items from
last to the Import level, which matters only where R3 now refuses.

R3. **Clashes, refused at the import** (`E-IMPORT-CLASH`, which exists):
the item `S` is refused if `S.` already means something as a qualifier in
this file at a level that would hide or be hidden by it:
- the module declares `S` (as today for any item);
- the module's own namespace has `S` under it (`Own.S`, step 3);
- `S` is a root project namespace (step 4);
- `S` is a default name (the prelude's `List`, `Option`, …).

The note says what `S.` means today and gives the full name to write. A
name brought by `(..)` is lower and loses silently, as a named import
beats any `(..)` today (projects.md:186-188). Another import item with the
same short name (a namespace and a type, or two namespaces) is
`E-AMBIGUOUS` at use, by the same-level rule.

R4. **Order of checking.** An item that names a project namespace adds a
dependency edge to it (project.rs:326-333 gains a loop over items). A cycle
through it is `E-NAMESPACE-CYCLE`, as for any import. An item that is
neither a declaration nor a namespace is `E-IMPORT-UNKNOWN`, whatever the
order.

R5. **What `S.rest` means.** `rest` is resolved inside `P.S` by longest
prefix, as for any qualifier (`Spec.Machine.cost`, `Spec.Carries` in a
pattern). `S` alone (not followed by `.`) names nothing: `E-UNKNOWN-NAME`,
with a note that `S` is a namespace.

R6. **Dot calls** are unaffected (§3.6). A namespace item doesn't make
`P.S`'s extensions visible to dot calls. `(..)` still does that. Written
qualified, `S.Grid.probe` finds the extension by its key (scope.rs:741-760).

R7. **Re-exports:** none, as today.

R8. (Stage 2, D2073.) **`(..)` brings sub-namespaces.** `import N (..)`
also binds, at the Wildcard level, the next component of every namespace
under `N` that is not a declaration of `N` (for `Aoc.Year2024.Day13`:
`Spec`, `Proofs`, `Tests`). A type of `N` already works as a qualifier and
is unaffected. A sub-namespace and a declaration of `N` with the same name
are `E-NAMESPACE-CLASH` already (multi-file.md:370-372). Two `(..)`
bringing `Spec` are `E-AMBIGUOUS` at use. The existing note ("import it by
name, e.g. `import Aoc.Year2024.Day13 (Spec)`", scope.rs:1440-1456) already
fits. The pre-pass makes an edge to `N.S` **only when `S.x` is used**,
exactly as a written qualified name does today (project.rs:342-355), so
`(..)` creates no false cycle (the `wildcard-only-edge` and
`no-false-cycle` examples keep passing). The file's own namespace is not
brought (a proofs file's `(..)` of the day doesn't bind `Proofs` to
itself).

### 6.3 Printing: goals and messages

- **Goals and terms:** no change. `short_name` tries `fewestTokens`, then
  `Spec.fewestTokens`, and the second now resolves in a file that imported
  `Spec`. SW-918's property (what is printed resolves in the file, to the
  same declaration) holds by construction, because `names` *is*
  resolution. Test: a goal in a file with `import Shop (Spec)` prints
  `Shop.total prices = Spec.total prices`, or `total prices = Spec.total
  prices` if `Shop (total)` is imported (snapshot).
- **Messages:** `written` (scope.rs:1384) is replaced by the printer's
  suffix search, so `E-AMBIGUOUS` says "write `Spec.total` or `total`…"
  when those resolve. This is one routine for goals and messages.

### 6.4 Error messages

- `E-UNKNOWN-NAME` for `S.x`, where `S` is the last component of a project
  namespace `P.S`, gets a note like the library's (scope.rs:1497-1520):
  "`Spec` is the namespace `Aoc.Year2024.Day13.Spec`: add `import
  Aoc.Year2024.Day13 (Spec)`, or write `Aoc.Year2024.Day13.Spec.fewestTokens`".
  If several namespaces end in `S`, the note lists up to three, those that
  share the most leading components with the file's own namespace first.
- `import M as A` stays `E-PARSE`, but with a note: "there is no `as`;
  to write `Spec.x`, import the namespace by its last name: `import
  Aoc.Year2024.Day13 (Spec)`". If `A` isn't `M`'s last component, the
  note adds "a namespace is always written by its own name". The same note
  goes on `import M (x as y)`.
- `E-IMPORT-CLASH` (R3) names what `S.` means now.

### 6.5 LSP

- Hover on a namespace item: "namespace `Aoc.Year2024.Day13.Spec`" and its
  files. `note_import` records namespace items as well as declarations.
- Go to definition on the item: the namespace's first file, in path order.
  On `Spec.fewestTokens`: the declaration, as for any qualified name
  (unchanged).
- Completion and rename: there are none for names today (§3.8), so nothing
  changes. If rename is added later, it renames declarations; a qualifier
  is the namespace's own name, so it changes only if the namespace is
  renamed.

### 6.6 `fmt`

No change (no new tokens). The golden tests gain one import with a
namespace item, to pin that.

### 6.7 Hashes

An item only decides which key a written name resolves to, and the keys
are the same. So no definition or data hash may change. Tests:
1. `crates/cli/tests/caching.rs`: one project written twice, once with
   `Shop.Spec.total` and once with `import Shop (Spec)` and `Spec.total`.
   Every declaration's hash must be equal, and the second check must reuse
   the first's test results.
2. Rewrite day 13's four lines to `Spec.fewestTokens` and compare
   `HASH_DUMP` for aoc before and after (docs/testing.md "Hash dumps").
   The two files must be identical.
3. The `hashes` snapshot area must show no change.

### 6.8 How agents benefit

- What they try first (`Spec.fewestTokens`) works after one import line,
  and the error tells them that line.
- Correctness theorems can say which side is the spec: `program =
  Spec.f`. The proving guide can recommend it.
- One spelling per namespace across the repository, so `grep -rn
  'Spec\.fewestTokens'` finds every use, and a goal printed in one file
  reads the same in another.
- A documented rule becomes true, and an order-dependent result goes away.

## 7. Plan

**Stage 1 (b′), about a day for Sonnet; the elaborator's name resolution
needs judgement.**
- scope.rs: namespace items at the Import level (R1-R3, R5); fold in
  `library_namespace`; `written` via the suffix search (§6.3); notes
  (§6.4).
- project.rs: item edges (R4); `PrePass::short` counts namespace items.
- parser.rs: the `as` note (§6.4).
- nav.rs: namespace items in the index (§6.5).
- Docs: syntax.md:275, projects.md (imports), proving-guide.md (write
  `Spec.x` in correctness statements).
- aoc: day 13's four lines become `Spec.fewestTokens`.
- Tests:
  - `examples/projects/accept/import-namespace-item`: `Shop`, `Shop.Spec`,
    `Shop.Proofs` (which sorts before `Spec`, for R4), with `Spec.total` in
    a theorem and a test.
  - `examples/goals/…`: a goal printing `Spec.total`.
  - reject: `import-namespace-item-clash` (own declaration `Spec`; own
    sub-namespace; a root project namespace; a default name),
    `import-namespace-item-unknown`, `import-as` (the note),
    `namespace-item-alone` (`Spec` without `.x`).
  - `E-UNKNOWN-NAME` note snapshots.
  - hashes (§6.7).
  - `std-qualified-eq.sw` and the other `Std` item examples are unchanged.
- Tiers: lane `elab`, `projects`, `hashes`; merge tier.

**Stage 2 (b″), if D2073 is yes.** Half a day. `add_wildcard` binds
sub-namespaces (R8). The pre-pass edge is made on use. projects.md:179 is
reversed. Tests: accept `wildcard-sub-namespace`; reject
`wildcard-sub-namespace-ambiguous` (two days' `Spec`); `no-false-cycle`
and `wildcard-only-edge` must still pass.

**Not planned:** `as` (a), per-name renaming (c). Revisit (D2074) if a lane
records a file that needs two namespaces with the same last name, or a
clash that a rename of its own declarations can't avoid.

## 8. Risks

- **R2 moves `Std` items up.** A file that today has an own namespace
  `Eq` (from `def Eq.foo` in its own namespace) and also `import Std (Eq)`
  silently gets its own `Eq.` today. Under R3 the import is refused. That
  only turns a silent hiding into an error. The accepted examples and the
  aoc and rogue projects will show any real case.
- **Stage 2 adds implicit names.** A sub-namespace named like a default
  name (a hypothetical `Aoc.Year2024.Day13.List`) would hide `List.` at the
  Wildcard level, as a type of that name brought by `(..)` does today
  (projects.md:196-199). There are no such namespaces in the repository.
- **Not (a) may be wrong** if agents keep writing `as`. The `as` note
  turns that into one round trip. If the count of these grows in the notes,
  D2074 can be revisited. Adding `as` later only turns an error into a
  program.

## 9. Decisions for Matt

**D2072. Make a namespace an import item for project namespaces too:
`import Aoc.Year2024.Day13 (Spec)`, then `Spec.fewestTokens`, as it works
for `Std` today, with no new syntax. [rec: yes]**
Assumptions, in full:
1. Agents and people want to write a namespace's own last name
   (`Spec.x`), not a name of their choosing. The evidence is the lane's
   `as Spec` and the orchestrator's `Spec.fewestTokens`, both with the
   namespace's own name.
2. Fixing the documented rule (syntax.md:275) and the order-dependent
   import (§3.4) is wanted anyway, whatever else is decided.
3. Refusing an item whose name already means something as a qualifier in
   the file (R3) is better than letting one silently hide the other.

**D2073. Let `import N (..)` also bring `N`'s sub-namespaces as
qualifiers (stage 2), reversing projects.md:179. [rec: yes]**
Assumptions, in full:
1. Proof and test files usually import their day with `(..)` (115 of the
   138 files that import a spec), so this makes `Spec.x` work with no
   import line, as the orchestrator expected it to.
2. These names sit at the Wildcard level, below the file's own names and
   its named imports. Two of them clash only where used. So the new names
   can't change the meaning of a name the file already uses, except a
   default-name qualifier, of which there are none (§8).
3. The pre-pass makes an edge only when such a qualifier is used, so no
   false cycle appears.
4. Agda does this (stated); Rust globs very probably do (inferred).

**D2074. Don't add `import M as A` or `import M (x as y)` now; `as` gets
an `E-PARSE` note pointing at the item form. [rec: yes, defer]**
Assumptions, in full:
1. The evidence for a name other than the namespace's own last name is
   none: four lines, all one day, none a real clash (§2.1).
2. One spelling per namespace across files is worth more to agents
   (`grep`, printed goals that read the same everywhere) than a free
   choice.
3. Adding `as` later is a pure extension (an error becomes a program), so
   deferring loses nothing.
4. Lean 4, the closest language in purpose, has no module alias and does
   without.

## 10. Sources

**Code and docs read (this repository, 30 October 2026):**
crates/syntax/src/{ast.rs, parser.rs, lexer.rs}; crates/elab/src/{scope.rs,
project.rs, nav.rs, goals.rs}; crates/core/src/pretty.rs;
crates/cli/src/lsp.rs; crates/fmt/src/layout.rs; docs/syntax.md:257-277;
docs/projects.md:160-200; docs/proposals/multi-file.md §4.2, 4.5, 4.6;
docs/proposals/namespaces.md §0-1; docs/testing.md; aoc/NOTES-2024.md (by
search); games/rogue/NOTES.md, PROOFS.md (by search);
docs/research/agentic-proving.md §5.

**Probes (run 30 October with main's release binary, all reverted):** the
day 13 rewrites (§2.1); `import Aoc.Year2024.Day13 (Spec)` (§3.4); a
scratch project `Shop` for every output in the review brief.

**Other languages: 11 pages read in part, through a summarising fetch with
quoted passages; 0 read in full; 0 web searches.**
- [H] Haskell 2010 Report, ch. 5 "Modules", §5.3-5.5:
  https://www.haskell.org/onlinereport/haskell2010/haskellch5.html
- [R] The Rust Reference, "Use declarations":
  https://doc.rust-lang.org/reference/items/use-declarations.html
- [L1] Lean 4 reference, "Namespaces and Sections" (§6.1-6.2; the first
  100,000 of 105,245 characters):
  https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/
- [L2] Lean 4 reference, "Identifiers":
  https://lean-lang.org/doc/reference/latest/Terms/Identifiers/
- [S1] Scala 3 reference, "Imports":
  https://docs.scala-lang.org/scala3/reference/changed-features/imports.html
- [S2] Scala 3 reference, "Importing Givens":
  https://docs.scala-lang.org/scala3/reference/contextual/given-imports.html
- [O1] OCaml manual 5.3, "Type-level module aliases":
  https://ocaml.org/manual/5.3/modulealias.html
- [O2] OCaml manual 5.3, "Module expressions" (§11.2, open and include):
  https://ocaml.org/manual/5.3/modules.html
- [P] Python Language Reference, §7.11 "The import statement":
  https://docs.python.org/3/reference/simple_stmts.html
- [A] Agda documentation, "Module System":
  https://agda.readthedocs.io/en/latest/language/module-system.html
- [I] Idris 2 tutorial, "Modules and Namespaces":
  https://idris2.readthedocs.io/en/latest/tutorial/modules.html

**Not read, so supporting nothing here:** GHC's user guide (e.g.
`ImportQualifiedPost`); the Rust Reference's name-resolution chapter (glob
ambiguity); the end of Lean's resolution rules for `open A` followed by
`B.x`; OCaml's shadowing rules for `open!`; Scala 3's ambiguity rules.
