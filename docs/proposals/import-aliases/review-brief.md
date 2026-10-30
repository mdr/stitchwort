# Reviewer brief: import aliases for Stitchwort

**For:** an expert in programming-language design (module systems, proof
assistants), outside the project, with no access to its repository.
Everything you need is on this page.
**What we ask:** your view on the design in §4, and answers to the
questions in [§6](#6-questions-for-the-reviewer). Anything else you notice
is welcome.
**Status:** design note draft 1 (30 October 2026). Nothing is built. Every
Stitchwort example below was run with the current compiler, and its real
output is shown.

## 1. Stitchwort in brief

**What it is.** Stitchwort is a dependently typed functional programming
language written in Rust. Programs and proofs are the same kind of thing:
a theorem is a definition whose type is a proposition, and its proof is a
term. An elaborator turns source into a core calculus, and a small kernel
re-checks everything the elaborator produces. It is used to write programs
and prove things about them: solutions to Advent of Code (AoC) puzzles,
each with correctness theorems against a specification written in the
puzzle's own words, and a roguelike game.

**Who uses it.** AI agents first. Most code and proofs are written by
coding agents working in parallel "lanes". They drive the command-line
tool (`stitchwort check`, `stitchwort test`), read its error messages and
the goals it prints, and keep notes of what got in their way. So a design
is judged by what an agent would try first, whether the error message
teaches the fix, and whether the code it writes reads the same in every
file. People use it too, through an editor's language server.

**Enough syntax to read the examples.**

- `def f (x: T): R := body` is a function. `theorem t: P := proof` is a
  theorem. `rfl` proves an equation that holds by computation. `?` is a
  hole, and checking reports its goal.
- `match xs with | Nil => … | Cons x rest => …` is pattern matching.
- `(sum price => sum + price)` is a lambda. `xs.foldLeft 0 f` is a *dot
  call*: the type of `xs` (`List`) decides that it means
  `List.foldLeft xs 0 f`.
- `test "name" := boolean` is a unit test.

### 1.1 Namespaces and imports today

- Every declaration has a **full name** (its *key*): `Std.List.length` for
  the standard library, `Shop.Spec.total` for a project's.
- **A project** is a folder of `.sw` files. Each file starts with
  `namespace Name`, and files with the same namespace form one module.
  Namespaces nest **by name only**: `Shop` and `Shop.Spec` are two
  namespaces, and inside `Shop`, writing `Spec.total` does not reach
  `Shop.Spec.total`. This was a deliberate decision.
- **A full name always works**, with no import: `Shop.Spec.total`.
- **`import N (a, b)`** makes `a` and `b` usable by their short names in
  this file. **`import N (..)`** brings every name declared directly in `N`,
  at a lower priority. There is no `import N` without a list, and imports
  are never passed on to files that import this one.
- **A type owns a namespace** (its constructors, and functions declared
  `def Machine.cost`). Importing the type `Machine` lets you write
  `Machine.cost`.
- **A short name** means, at the first level that has it: a local variable;
  this namespace's own declaration; a name imported by name; a name from a
  `(..)`; the prelude. Two different things at one level are an error
  (`E-AMBIGUOUS`) only where the name is used.
- **A qualified name `A.b.c`**: `A` is looked up as a short name (a type or
  ability), then as a namespace of the file's own, then as a root project
  namespace, then as a library namespace that this file imports by name.
- **The library is special in one way that matters here:** an import item
  may be a namespace that declares no name of its own. `import Std (Eq)`
  lets the file write `Eq.sym`, and that is the only way to reach `Eq.sym`
  short of `Std.Eq.sym`.
- **Names are kept out of hashes.** A definition's hash leaves out its own
  name. A data type's hash includes its full name. Results are cached by
  hash, so a change of spelling must never change a hash.
- **Goals and messages print names the file can resolve.** A recent change
  makes the printer try a declaration's full name's trailing parts,
  shortest first (`total`, `Spec.total`, `Shop.Spec.total`), and print the
  first one that means that declaration in this file. So whatever is
  printed can be pasted back.

### 1.2 A small project, run

Three namespaces: the program, its spec, and the proofs.

```
-- src/Shop/Shop.sw
namespace Shop
import Std (List)

-- The program: the total price of a basket, in cents.
def total (prices: List Nat): Nat := prices.foldLeft 0 (sum price => sum + price)
```

```
-- src/Shop/Spec/Spec.sw
namespace Shop.Spec
import Std (List)

-- The specification: the same total, written the obvious way.
def total (prices: List Nat): Nat :=
  match prices with
    | Nil => 0
    | Cons price rest => price + total rest
```

```
-- src/Shop/Proofs/Proofs.sw
namespace Shop.Proofs
import Shop (total)
import Std (List)

theorem emptyAgrees: total [] = Shop.Spec.total [] := rfl
```

```
$ stitchwort check
checked 3 namespaces of probe
```

Importing both `total`s is accepted, and fails where the name is used:

```
import Shop (total)
import Shop.Spec (total)
…
theorem emptyAgrees: total [] = total [] := rfl
```

```
[E-AMBIGUOUS] Error: `total` could mean `Shop.Spec.total` or `Shop.total`
   ╭─[ probe/src/Shop/Proofs/Proofs.sw:6:22 ]
 6 │ theorem emptyAgrees: total [] = total [] := rfl
   │                      ──┬──
   │                        ╰──── write `Shop.Spec.total` or `Shop.total` in full
```

The same through two `(..)` imports gives the same error, with a note:
"both come in through `(..)` imports; to choose one, import it by name,
e.g. `import Shop.Spec (total)`".

A goal prints the full name, because nothing shorter resolves:

```
theorem twoAgree (prices: List Nat): total prices = Shop.Spec.total prices := ?
```

```
[GOAL] Goal: in `twoAgree`
 5 │ theorem twoAgree (prices: List Nat): total prices = Shop.Spec.total prices := ?
   │                                                                               ╰── prices: List Nat
   │                                                                                   ⊢ total prices = Shop.Spec.total prices
```

The middle way, `Spec.total`, doesn't exist:

```
theorem emptyAgrees: total [] = Spec.total [] := rfl
```

```
[E-UNKNOWN-NAME] Error: unknown name `Spec.total`
 5 │ theorem emptyAgrees: total [] = Spec.total [] := rfl
   │                                 ─────┬────
   │                                      ╰────── not in scope
```

Nor does an alias:

```
import Shop.Spec as Spec
```

```
[E-PARSE] Error: expected `(` and the names to import, but found `as`
```

For the library, the namespace-item form works, and its error teaches it:

```
import Std (List)
theorem flip (a: Nat) (b: Nat) (h: a = b): b = a := Eq.sym h
```

```
[E-UNKNOWN-NAME] Error: unknown name `Eq.sym`
   │ Note: `Eq` is `Std.Eq`; add `import Std (Eq)`, or write `Std.Eq.sym`
```

With `import Std (Eq, List)`, it checks.

**The same form for a project namespace is accepted but does nothing**, or
is refused, depending on the order the namespaces happen to be checked in:

```
import Shop (total, Spec)      -- Shop.Spec not yet checked
[E-IMPORT-UNKNOWN] Error: `Shop` has no `Spec`

import Shop (Spec, total)      -- plus `import Shop.Spec (..)`, so Shop.Spec is checked first
import Shop.Spec (..)
theorem emptyAgrees: Shop.total [] = Spec.total [] := rfl
[E-UNKNOWN-NAME] Error: unknown name `Spec.total`
```

The language's own reference says this form works for "any
sub-namespace". The cause: the dependency pass orders namespaces by
imports' paths, not by items that are namespaces, and name lookup only
looks for an imported namespace under the library.

## 2. The problem, with evidence

The request (from the project's maintainer, after an agent's note) was:
add `import M as A`.

- **Full names written today.** Across the AoC solutions (135
  namespaces), the roguelike (29 files), the standard library and the
  examples, real code writes a project's full name on **4 lines**. All are
  `Aoc.Year2024.Day13.Spec.fewestTokens`, in day 13's proofs and tests. The
  other 14 full names are in examples that test the full-name rules.
- **None of the four was needed.** The program has a *method*
  `Machine.fewestTokens`, and the spec a plain function `fewestTokens`.
  They don't clash. Importing `fewestTokens` by name and writing it short
  checks, and all 25 of day 13's tests pass (tried, then reverted). The
  agent believed they clashed, tried `import … as Spec`, got `E-PARSE`, and
  wrote the full name.
- **Real clashes in the agents' notes:** one. A constructor `Carries` in
  the program and a relation `Carries` in the spec gave `E-AMBIGUOUS`, and
  the agent renamed the constructor. Other name troubles in the notes are
  of other kinds: a lambda parameter shadowing a name brought by `(..)`,
  and two constructors with one name in one file.
- **How clashes are avoided:** 138 proof and test files import a day's
  spec, 115 of them with `(..)`, next to `(..)` of the program. The spec
  and program use different names (`part1`, `solvePart1`). Only 1 of 33
  days declares the same short name in both.

**Our reading:** the evidence for renaming to a name of one's choice is
weak. The evidence that agents expect to write `Spec.x` is better: the
agent's alias was `as Spec`, and the maintainer's first try was
`Spec.fewestTokens`. In a correctness theorem, `program = Spec.f` also
documents which side is the spec.

## 3. What other languages do

Read from the primary documentation (11 pages, each through a summarising
reader with quoted passages; details in the design note's sources).

| Language | Rename a module | A sub-module by its last name | Glob brings sub-modules | Rename one name | Clash |
|---|---|---|---|---|---|
| Haskell 2010 | `import qualified M as N`; several modules may share an `as` name if every use is unambiguous | no | n/a | no | error only if mentioned |
| Rust | `use a::b as c` | `use path::m;` then `m::f` | "all importable entities" (modules are items, so yes, inferred) | `use m::f as g` | named items shadow globs |
| Lean 4 | none found | inside `namespace A`, `B.x` is tried as `A.B.x`; `open A.B` | `open A` then `B.x`: not settled by what we read | `open X renaming a → b` | overloaded: elaborate all, keep the one that works |
| Scala 3 | `import java as j` | import a package or object | `*` skips givens | `import A.{min as minimum}`, hide with `as _` | (not read) |
| OCaml | `module M = A.B` (an alias at the type level) | via alias or `open` | `open`, `include` | no | (not read) |
| Python | `import a.b.c as d` | `from a.b import c` | `from m import *` (`__all__`) | `from a import b as c` | last binding wins |
| Agda | `import M as M'` | after `open A`, "qname can itself be a qualified name": `B.x` | yes | `open A renaming (x to y)` | error if an ambiguous name is used |
| Idris 2 | `import Data.List as L` | not settled by what we read | n/a | no | by qualification or by type |

## 4. The design

**(b′) Namespace items for project namespaces too. No new syntax.**

```
namespace Shop.Proofs
import Shop (total)
import Shop (Spec)          -- new for project namespaces; works today for Std

theorem emptyAgrees: total [] = Spec.total [] := rfl
```

- **R1.** `import P (S)`, where `P.S` is a namespace and not a declaration,
  binds `S` in this file as a qualifier for `P.S`. It applies to the file
  only and is not passed on.
- **R2.** It sits with the names imported by name, so one mechanism serves
  the library and projects.
- **R3. Clashes are refused at the import** (`E-IMPORT-CLASH`) when `S.`
  already means something there: the file's module declares `S`; its own
  namespace has `S` under it; `S` is a root project namespace; or `S` is a
  prelude name. Names brought by `(..)` are lower and lose silently, as
  named imports beat `(..)` today. Two imported things called `S` are
  `E-AMBIGUOUS` where used.
- **R4.** An item that is a project namespace adds a dependency edge, so
  the result never depends on the order of checking.
- **R5.** `Spec.Carries` works in patterns and expressions. `Spec` alone is
  an error that says it's a namespace.
- **R6.** Dot calls are untouched: they use the value's type, not a
  written qualifier.
- **Printing.** Goals need no change. The printer already tries
  `Spec.total` and checks that it resolves, so what it prints can always be
  pasted back. Messages switch to the same routine (today `E-AMBIGUOUS`
  only offers the short or the full name).
- **Errors that teach.** `E-UNKNOWN-NAME` for `Spec.total` gets a note
  like the library's: "`Spec` is the namespace `Shop.Spec`: add `import
  Shop (Spec)`, or write `Shop.Spec.total`". `import M as A` stays a parse
  error, with a note pointing at the item form.
- **Hashes.** Only resolution changes, and keys don't, so no hash can
  change. Tested by checking one project written both ways (equal hashes,
  cached test results reused) and by a whole-project hash dump before and
  after rewriting day 13's four lines.
- **Editor.** Hovering an item shows the namespace. Go to definition goes
  to its first file. There is no rename or name completion today.

**Stage 2 (b″), proposed:** `import N (..)` also binds `N`'s immediate
sub-namespaces (not the file's own) as qualifiers, at the `(..)` level. A
day's proof file already has `import Aoc.Year2024.Day13 (..)`, so
`Spec.fewestTokens` would work with no new line. A dependency edge is made
only when such a qualifier is used. This reverses a documented rule ("it
doesn't bring namespaces under it").

**Not proposed now:** `import M as A` and `import M (x as y)`. The
arguments:
- There is no evidence for a name other than the namespace's own.
- One spelling per namespace keeps code greppable, and goals read the same
  in every file.
- Renaming would need the printer to learn aliases, or it would print full
  names next to code written with aliases.
- Adding it later only turns an error into a program.

## 5. What we are fairly sure of, and what we are not

- **Sure:** the four full names were unnecessary. The namespace-item form
  is documented and broken for projects. The printer handles (b′) without
  change. Nothing touches hashes.
- **Less sure:** that agents won't keep reaching for `as`. The note on the
  parse error is meant to make that a one-step fix. Also, whether moving
  library items' priority up (R2) breaks a corner case: one such case is
  known, and it becomes an error instead of a silent hiding.
- **Not settled by our reading:** whether Lean 4 resolves `B.x` after
  `open A`, and whether Rust's glob imports bring modules (we infer yes).

## 6. Questions for the reviewer

1. Is (b′), the namespace's own last name with no renaming, enough for a
   language whose main users are AI agents? Or is `as` worth having anyway
   because it is what agents try first?
2. R3 refuses an imported namespace whose name already means something as
   a qualifier, instead of letting one hide the other. Is that the right
   default, given that short names *do* hide by level?
3. Stage 2 makes `(..)` bring sub-namespaces. Agda does this. Is the extra
   implicitness a problem in practice, for example with names like `Proofs`
   or `Tests` arriving in every file?
4. Two namespaces with the same last name (`Day12.Spec` and `Day13.Spec`)
   can't both be used short in one file. Is that a real limitation in
   your experience, or rare enough to leave to full names?
5. If `as` is added later, should the printer prefer the alias, which
   means a goal reads differently in each file, or the namespace's own
   name, which means the printed text may not resolve in that file?
6. Is there a module-system design we should have read that handles
   "spec vs program" pairs better, for instance Lean's `export` or Agda's
   `open … public`?

## Glossary

- **Agent / lane:** an AI coding agent working on one task in its own copy
  of the repository.
- **AoC:** Advent of Code; each day's solution has a program, a spec in the
  puzzle's words, proofs that the program meets the spec, and tests.
- **Key:** a declaration's full name, which is what resolution finds.
- **Qualifier:** the first component of a dotted name (`Spec` in
  `Spec.total`).
- **Level:** the priority at which a short name is found (module, import,
  `(..)`, prelude).
- **`(..)` / wildcard:** `import N (..)`, every name declared directly in
  `N`.
- **Prelude:** the library names every file sees without an import
  (`Nat`, `List`, `Option`, …).
- **Dot call:** `x.f`, resolved through the type of `x`.
- **Extension:** a function another namespace adds to a type (`def
  Grid.probe` declared outside `Grid`'s namespace).
- **Goal:** what is left to prove at a hole `?`, printed with its
  hypotheses.
- **Dependency pre-pass:** the step that orders namespaces before checking
  them, from imports and written qualified names.
- **`E-…` / `W-…`:** stable error and warning codes.
