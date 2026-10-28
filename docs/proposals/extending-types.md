# Adding functions to another namespace's type

**Status:** design note, 28 October 2026. Open question: may a file other
than the one declaring a type add functions to that type's namespace? Option
(c) chosen and implemented. Code references checked at `9f9220ce`.

**The short answer.** Allow it from any project namespace, but make the added
function **belong to the namespace that wrote it**: `grid.probe` finds it only
in that namespace's own files and in files that import that namespace. The
type's own namespace, other days and `Std` never see it. A clash with the
type's own function is an error where the extension is declared; two
extensions of the same name visible in one file are an error where they're
used. Adding a file can then only change an existing `x.f` if it is in your
namespace or in one you import with `(..)`, and the second case is always an
error, never a silent switch (§6).

## 1. The problem in one example

AoC 2025 day 4 keeps its program in `Aoc.Year2025.Day04` and the puzzle as
stated in `Aoc.Year2025.Day04.Spec` (`aoc/src/Aoc/Year2025/Day04/Spec/Spec.sw`),
so that `run` doesn't check the spec and proofs. The spec's helpers are about
the day's `Grid`:

```
namespace Aoc.Year2025.Day04.Spec
import Aoc.Year2025.Day04 (..)

def cellsOf (grid: Grid): Cells := …
def neighbours (grid: Grid) (cells: Cells) (r: Nat) (c: Nat): Nat := …
def accessible (grid: Grid) (cells: Cells) (r: Nat) (c: Nat): Bool := …
```

The house rule is that functions about a type live in its namespace and are
used with dot syntax (`grid.cellsOf`). Here that's refused. Scratch project
(`P` declares `Grid`, `P.Spec` imports it):

```
namespace P.Spec
import P (Grid)

def Grid.probe (grid: Grid): Nat := grid.width + 1
```

```
$ stitchwort check
[E-FOREIGN-NAMESPACE] Error: `Grid` belongs to namespace P, and P.Spec can't add to it
 4 │ def Grid.probe (grid: Grid): Nat := grid.width + 1
   │     ─────┬────
   │          ╰────── `Grid` here means `P.Grid`
   │ Note: name it in P.Spec without the `Grid.` prefix, e.g. `probe`
```

Other cases of the same shape: 2025 day 1's `mirror (dial: Dial n)` in
`Day01/Proofs/Part2.sw`; 2024 day 9's `idAndLength (file: File)` and
`blocksOfFile (file: File)` in `Day09/Proofs/Part2.sw`; and the five cases
listed in [multi-file.md §4.7](multi-file.md#47-adding-to-another-namespace-d8-deferred)
(2025 day 2's `Range.invalid`, the roguelike's `Area.fits` in its tests and
`level.goalReachable` in its proofs, plus two on `Std` types).

## 2. Why namespaces are closed today

Two decisions, neither of which ruled the idea out:

- **Std (namespaces.md, answer to Q4, 16 October 2026):** "A user's file
  adding functions to library namespaces … **deferred**. For now a user file
  can't add to `Std`'s namespaces (an error saying so)." The note's own
  reason for keeping it closed until then
  ([§8](namespaces.md#8-extending-it-later-without-breaking-anything)):
  "Since user files can't add to library namespaces (§4.3), a library
  addition can't collide with a user's `List.sum` either. If extension is
  allowed later (Q4), that collision becomes possible, as in Lean." The
  reviewer question R9 named the multi-file risk: "two files can both add
  `List.sum`, which is a conflict only if both are loaded."
- **Other project namespaces (multi-file.md D8):** "**Deferred**: needs its
  own design. Until then `E-FOREIGN-NAMESPACE`; `Std` stays closed." Its
  reason (§4.7): "Refusing now keeps every answer open: all of them only turn
  errors into programs." It listed what the design must answer: "where the
  added name lives …; whether it can be imported elsewhere; how it interacts
  with namespaces.md §4.8's alias rules for dot notation; and, with
  interfaces, whether an instance for another namespace's type is the same
  question." And it noted: "letting `P.Tests` and `P.Proofs` add to `P`'s
  types would cover every case met in tests and proofs."

A property today's rule gives for free (multi-file.md §4.8): `T`'s namespace
"is complete once `T`'s namespace is checked, so the answer can't depend on
which other namespaces exist." Every option below has to say what replaces
it.

## 3. How `x.f` is found today

1. `x`'s type gives a head, `Grid` (`dot.rs`, `find_in_view`). Nicknames are
   tried before they are unfolded (`Price` then `Nat`).
2. The head's **key** is built, `Aoc.Year2025.Day04.Grid`, and `.f` appended.
3. That string is looked up in **one table of every declaration loaded so
   far**: `cx.e.scope.get(&key)` (`dot.rs:503-506`), where `Scope.entries` is
   "Every declaration, by key" (`scope.rs:113`). No import is consulted. The
   prelude comment says so: "Dot notation needs no import (D261)"
   (`scope.rs:45`).
4. In a project, namespaces are checked one at a time in canonical order
   (each after what it uses, ties by name; `project.rs`, `canonical_order`),
   all into that same table. Which namespaces are loaded depends on the
   command: `check` loads all, `test Aoc.Year2025.Day05` loads Day05 and what
   it uses. The closure of what a namespace uses is passed in, but only
   `auto` filters by it (`auto.rs:583`); plain lookups don't.
5. A namespace "uses" another only through an `import` or a qualified name
   (`project.rs`, `namespace_edges`). A dot call adds no edge, which is fine
   today because `T.f` is always in `T`'s namespace, already loaded wherever
   a `T` exists.

Confirmed in the scratch project: namespace `Q` with no imports at all
checks `def useSize (grid: P.Grid): Nat := grid.size`.

So today, "visible" for dot notation means "loaded". That is harmless only
because the only files that can write `Grid.f` are `Grid`'s own namespace.

**Two things that already exist:**

- **Joining the namespace.** File names and folders mean nothing
  ([projects.md](../projects.md)), so a file in `Day04/Spec/` that starts
  `namespace Aoc.Year2025.Day04` adds to `Grid` freely. Checked: a file
  `src/P/Spec/Extra.sw` with `namespace P` and `def Grid.probe` makes
  `grid.probe` work in `Q`; if `P.sw` also defines `Grid.probe`, it's
  `E-DUPLICATE`. That puts the helper in the program's namespace, which is
  what the Spec split avoids (`run` would check it).
- **A local nickname.** `def SpecGrid: Type := Grid` and
  `def SpecGrid.probe (grid: SpecGrid)` work for values typed `SpecGrid`, but
  a `grid: Grid` still says "`P.Grid` has no field or function `probe`".

## 4. The options

Two separate questions hide in "open the namespace":

- **Who may extend:** nobody, the type's sub-namespaces, or any project
  namespace.
- **Who sees the extension:** files that import the extender, or everything
  that happens to be loaded.

The second decides how far an extension spreads. In the tables, Spec
declares `Grid.probe` for Day04's `Grid`; Proofs and Tests files say
`import Aoc.Year2025.Day04.Spec (..)` (all of AoC's do).

### (a) Closed (today)

Helpers stay plain functions: `cellsOf grid`, `grid |> cellsOf`. Nothing
spreads; nothing can clash.

### (b) Sub-namespaces may extend the parent's types

`Aoc.Year2025.Day04.Spec` (and `.Proofs`, `.Tests`) may write `def Grid.probe`
for `Aoc.Year2025.Day04.Grid`; `Aoc.Year2025.Day05` may not. This limits who
writes extensions, not who sees them, so it needs one of the visibility rules
below. With (c)'s rule it is (c) restricted; with (d)'s it has (d)'s
problems. It covers every AoC case and the roguelike's, but not 2025 day 2's
`Range.invalid` on the shared `Aoc.Range`.

### (c) Any project namespace may extend; seen only where imported

The extension is a declaration **of the extending namespace**: its full name
is `Aoc.Year2025.Day04.Spec.Grid.probe`. `x.f` looks in `T`'s own namespace
first, then in the extensions of `T` that this file can see: its own
namespace's, and those of namespaces it imports with `(..)`. Imports aren't
passed on (multi-file.md D6), so seeing one needs a direct import.

| Where `grid.probe` is written | Sees Spec's `Grid.probe`? |
|---|---|
| Spec's own files | yes |
| Proofs, Tests (import Spec `(..)`) | yes |
| A Tests file that imports only Proofs | no |
| Day04 itself | no (it can't import Spec: that's a cycle) |
| Day05, or another project, importing Day04 but not Spec | no |
| `Std` | no |

### (d) Any file may extend; seen everywhere once loaded

The extension goes into `Grid`'s namespace in the shared table (key
`Aoc.Year2025.Day04.Grid.probe`), as Lean and Swift (before 6.1) do it.

| Where `grid.probe` is written | Sees it? |
|---|---|
| Spec, Proofs, Tests | yes |
| Day04 itself | no: checked before Spec, so not loaded yet |
| Day05 (doesn't use Spec) | **depends on the command**: with `check`, yes if Spec comes before Day05 in canonical order (it usually does: `…Day04.Spec` sorts before `…Day05`); with `test Aoc.Year2025.Day05`, no, since Spec isn't loaded |
| `Std` | no |

The Day05 row is the infection Matt asked about, and it is worse than a
leak: the same file checks or fails depending on what else was asked for.
Fixing that means either loading every extending namespace before any
namespace that might use it (impossible for the type's own namespace, which
comes first), or making visibility follow the dependency graph, which is (c)
with transitive imports. The check cache would also be wrong: a namespace's
cache key covers what it depends on, and Spec isn't among Day05's
dependencies.

## 5. Name clashes, option by option

| Situation | (a) | (c), recommended rules | (d) |
|---|---|---|---|
| Spec and Proofs each define `Grid.probe` | can't happen | two different functions (`…Spec.Grid.probe`, `…Proofs.Grid.probe`). In Proofs, its own wins over the imported one, as a namespace's own `probe` beats an imported `probe` today (`scope.rs`, levels). | `E-DUPLICATE` if both are loaded, which depends on the command |
| Proofs imports two namespaces that both add `Grid.probe` | — | error where `grid.probe` is used, suggesting the full names (D2: ambiguity is an error only where used) | as above |
| Day04 later adds its own `Grid.probe` | — | error **at Spec's declaration**: Day04 is always checked before Spec, so this is always caught there, never at a use | `E-DUPLICATE` |
| Day05 adds `Grid.probe` too | refused | fine; nobody sees both unless they import both, then it's an error at the use | `E-DUPLICATE`, only when both are loaded |

**Can adding a file change what an existing `x.f` means?**

- (a): no.
- (c): only (1) a file of **your own namespace** adding an extension, which
  shadows an imported one, exactly like adding a short name today; or (2) a
  file of a namespace you import `(..)` from, which can only turn a working
  call into an ambiguity error. A new function in the type's own namespace
  makes the extension fail where it's declared. Unrelated files: no effect.
- (d): yes, from anywhere, and whether it does depends on which namespaces
  the command loaded.

## 6. Recommendation: (c)

- **Any project namespace** may extend a **project** type. The sub-namespace
  restriction of (b) adds a rule without making anything safer, since
  containment comes from the visibility rule, and it would leave 2025 day 2's
  `Range.invalid` refused. `Std` stays closed (`E-STD-NAMESPACE`); with (c)'s
  rules, opening it later would be safe in the same way, and that stays a
  separate open question.
- **Seen by:** the extending namespace's own files, and files that import it
  with `(..)`. Direct imports only, as Kotlin, C# and Swift 6.1 do and
  Stitchwort's imports already work.
- **The type's own function always wins, and a clash is an error where the
  extension is declared.** Kotlin, C# and Swift silently prefer the member;
  here the check is free and earlier, because the owner is always checked
  first.
- **Own namespace's extension beats an imported one; two imported ones are
  ambiguous at the use**, the same levels short names use.
- **Qualified names agree with dot notation:** in Proofs, `Grid.probe grid`
  means what `grid.probe` means; the full name `Aoc.Year2025.Day04.Spec.Grid.probe`
  works anywhere, like any qualified name.
- **Nicknames:** at each head the type-head view tries (namespaces.md §4.8),
  look at the type's own namespace, then visible extensions of that head,
  before unfolding.

## 7. Costs

- **Lookup.** Dot lookup, method sections and qualified `T.f` grow one step:
  after `T`'s own namespace, the visible extensions of `T`. These need an
  index from (type, name) to the namespaces that extend it; the per-file
  `(..)` imports are already tracked (`Scope.wildcards`).
- **`E-FOREIGN-NAMESPACE`** becomes an extension for project types. Its
  qualified-name branch ("`P` is a namespace of the project") stays. Its note
  today says "write `Grid.probe`" for `def P.Grid.probe` in `P.Spec`, which
  is refused too; under (c) that advice becomes correct.
- **Error messages.** `E-UNKNOWN-FIELD` in a file that doesn't import the
  extender should name it: "`Aoc.Year2025.Day04.Spec` adds `Grid.probe`;
  import it with `import Aoc.Year2025.Day04.Spec (..)`". The message already
  lists functions elsewhere that take the type (`dot.rs`, `elsewhere_taking`).
  New errors: the owner clash at the declaration, and the use-site ambiguity.
- **Proofs.** An extension is an ordinary definition with its own full name,
  so `unfold`, equation lemmas and `rfl` work unchanged. A checked term
  refers to the definition itself, not to the name, so nothing already
  checked can change meaning. A theorem in Proofs about `grid.cellsOf` reads
  like one about the program's own functions.
- **Hashes:** the extension's full name is the extender's, so moving a helper
  from a plain function to an extension changes names and hashes. Not a
  concern now.
- **Check cache and `auto`:** unaffected under (c), because what a file can
  see is decided by its own namespace and its imports, both already part of
  the dependency closure. Under (d) the cache would be unsound (§4).
- **Editor:** completion after `grid.` should list visible extensions;
  go-to-definition already works by definition.
- **Orphan instances** (an interface implemented for another namespace's
  type) are the same question for `auto` and are not decided here.

## 8. How other languages do it

- **Lean 4.** Any file can `def String.add`, and `"hello".add "world"` then
  finds it [L1]. "Source files may add names to any namespace" [L2], and
  "Importing is transitive" [L3], so an extension reaches everything that
  imports its file, directly or not. `protected` keeps a name out of `open`
  [L4]; `private` keeps it inside its module [L2]. *Leak:* transitive to
  every downstream importer.
- **Scala 3.** An extension method applies when it is "visible under a simple
  name, by being defined or inherited or imported", or is "defined in the
  implicit scope of the type of `r`" (its companion object), and only when
  "`m` is not a member of `e`" [S1]. *Leak:* none beyond imports, except
  the type's own companion, which plays the role of `T`'s own namespace here.
- **Kotlin.** "Extensions don't modify the classes or interfaces they
  extend"; "To use an extension outside its declaring package, import it at
  the call site"; "the member function takes precedence" [K1]. *Leak:* the
  declaring package, plus importers.
- **C#.** "Extension methods are only in scope when you explicitly import the
  namespace … with a `using` directive"; an extension "with the same name and
  signature as an interface or class members are never called" [C1].
  *Leak:* the declaring namespace, plus `using` sites; a later member
  silently takes over.
- **Swift.** Extensions add to a type "for which you don't have access to the
  original source code", and the functionality "will be available on all
  existing instances of that type"; they "can't override existing
  functionality" [W1]. Until 6.1, an extension in a module imported only
  indirectly was still found; SE-0444's example has "The call to `parse()` is
  now ambiguous" after a dependency was added to *another* file. The fix,
  implemented in Swift 6.1, accepts a member only if its module is "directly
  imported" [W2]. *Leak:* was module-wide and transitive, now direct imports.
- **Rust.** Inherent methods: "An implementing type must be defined within
  the same crate as the original type definition" [R1] (closed, like (a)
  across crates). Trait methods: "the user must bring the trait into scope"
  [R2], and the orphan rule allows an impl only if "either the trait or at
  least one of the types … is defined in the current crate", which "ensures
  that other people's code can't break your code and vice versa" [R1, R2].
  *Leak:* only where the trait is imported.
- **Haskell.** Instances can't be named in import lists: "All instances in
  scope within a module are always exported and any import brings all
  instances in from the imported module" [H1]. An orphan is an instance in a
  module that declares neither the class nor the type; GHC warns because it
  "must pro-actively read the interface files for all orphan modules" [H2].
  *Leak:* global and transitive, the (d) end of the scale.

The trend: the languages that started global (Swift, Haskell's instances)
added rules or warnings to contain it; the ones designed later (Kotlin, C#,
Scala 3) scope extensions by import from the start. Lean is the closest
language to Stitchwort and is transitive.

## Sources

Fetched 28 October 2026.

- [L1] Theorem Proving in Lean 4, "Interacting with Lean" (`def String.add`
  example, §More on Namespaces):
  https://lean-lang.org/theorem_proving_in_lean4/Interacting-with-Lean/
- [L2] Lean Language Reference, "Source Files and Modules":
  https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/
- [L3] As [L1]: "Importing is transitive. … if you import Foo and Foo imports
  Bar, then you also have access to the contents of Bar".
- [L4] Lean Language Reference, "Namespaces and Sections":
  https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/ ;
  generalized field notation: https://lean-lang.org/doc/reference/latest/Terms/Function-Application/
- [S1] Scala 3 reference, "Extension Methods":
  https://docs.scala-lang.org/scala3/reference/contextual/extension-methods.html
- [K1] Kotlin docs, "Extensions": https://kotlinlang.org/docs/extensions.html
- [C1] Microsoft Learn, "Extension members":
  https://learn.microsoft.com/en-us/dotnet/csharp/programming-guide/classes-and-structs/extension-methods
- [W1] The Swift Programming Language, "Extensions":
  https://docs.swift.org/swift-book/documentation/the-swift-programming-language/extensions/
- [W2] SE-0444, "Member import visibility":
  https://github.com/swiftlang/swift-evolution/blob/main/proposals/0444-member-import-visibility.md
- [R1] The Rust Reference, "Implementations":
  https://doc.rust-lang.org/reference/items/implementations.html
- [R2] The Rust Programming Language, ch. 10.2 "Traits":
  https://doc.rust-lang.org/book/ch10-02-traits.html
- [H1] Haskell 2010 Report, §5.4:
  https://www.haskell.org/onlinereport/haskell2010/haskellch5.html
- [H2] GHC User's Guide, `-Worphans`:
  https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html

**Not verified:** what Lean reports when two imported files declare the same
full name (no official page found); whether the SE-0444 amendment (May 2026)
was accepted.
