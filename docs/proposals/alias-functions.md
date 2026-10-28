# Should a type alias have its own functions?

**Status:** design note, 28 October 2026. Recommendation ([§8](#8-recommendation)) items 1–3
implemented: fixes 1 and 2, with fix 2 evaluating a definition's type again only when it names
a definition (no measurable cost on the bench), the `E-UNKNOWN-FIELD` note, and the rule in
[namespaces.md](namespaces.md) §4.8 and the guide. Place 3 and the same-name warning are open.
The experiment in [§3](#3-the-experiment) is commit `5be9ec86` on its own branch, marked
experimental. Related: [namespaces.md](namespaces.md) §4.8 (the dot rule),
[dot-receiver.md](dot-receiver.md), [folded-calls.md](folded-calls.md) (glued calls),
[microtypes.md](microtypes.md) (one-field records as distinct types),
[opaque-definitions.md](opaque-definitions.md).

Labels: **[run]** a program I ran (release CLI, `main` at `9f9220ce` or the experiment);
**[checked]** read in the Stitchwort source; **[cited]** quoted from the page linked in
[Sources](#sources); **[inferred]** my reasoning from those.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [What the dot rule promises today](#2-what-the-dot-rule-promises-today)
3. [The experiment](#3-the-experiment)
4. [Is it predictable?](#4-is-it-predictable)
5. [Proofs: aliases versus wrapper types](#5-proofs-aliases-versus-wrapper-types)
6. [Other languages](#6-other-languages)
7. [Options](#7-options)
8. [Recommendation](#8-recommendation)
- [Sources](#sources)

## 0. Summary

- An alias (`type Code = List NumericKey`, `def Bank: Type := List Battery`) is a second name
  for a type. Functions in its namespace (`Code.numericPart`) are found by dot notation only
  while the checker still has the name `Code` in hand. Today it often doesn't: a lambda
  parameter whose type came from `List Code` is seen as `List NumericKey`, so
  `code.numericPart` fails.
- **Why the name is lost** ([§3](#3-the-experiment), **[run]**): three places, not one.
  1. Dot notation forces an inferred type before looking at it (the hypothesis; true, but on
     its own it fixes only one case).
  2. A definition's own parameter types are evaluated once, with aliases unfolded, so
     `codes: List Code` is `List (List NumericKey)` inside the body; anything inferred from
     `codes` never sees `Code`.
  3. Checking an argument against an expected type unfolds the expected type first, so an
     unknown type is filled in with the unfolded form.
- **The experiment** fixes 1 and 2 with 16 changed lines: the day 21 lambda, the 2025 day 3
  section, the plain `List.scanLeft` case and an annotated lambda all work. Place 3 is left: a
  simple patch to it broke the standard library, and the day 9 proofs that go through
  `List.mapZipWithScanLeft` still fail. Cost: the bench baseline test fails (`check-list-rfl`
  +11% steps; most checks +0 to 7%); aoc `check` and `test` times are unchanged within noise.
- **Even fixed, it can't be fully predictable.** Whether `x.f` finds `Code.f` depends on
  whether `x`'s type passed through something that names `Code`. `[1, 2].numericPart` never
  will (Lean is the same). A value built by a generic function finds it or not depending on
  argument order.
- **Wrapper types** (a one-field record, unboxed at run time) give a namespace that always
  works, but every lemma about the underlying type then needs unwrapping, and pattern matches
  change. For the proof-heavy AoC code that's the larger cost.
- **Other languages split three ways** ([§6](#6-other-languages), **[cited]**): Lean keeps
  alias namespaces and unfolds to the underlying one; Kotlin and Swift make a function on an
  alias a function on the underlying type, visible everywhere; F# forbids extensions on an
  abbreviation, and Haskell forbids instances on a synonym. Scala 3 and Kotlin point to
  opaque types and inline classes for a type with its own operations.
- **Recommendation** ([§8](#8-recommendation)): keep functions on aliases with Lean's rule,
  which is already the spec, land fixes 1 and 2 after making 2 cheaper, make the error say
  why `Code` wasn't seen, and say plainly in the docs that alias functions are found by dot
  only where the type mentions the alias. Use a wrapper type when the point is a *different*
  type, not a namespace.

## 1. The problem

Day 21 of 2024 has door codes:

```
type Code = List NumericKey

def Code.numericPart (code: Code): Nat := code.foldLeft 0 (…)

def complexities (robots: Nat) (codes: List Code): Nat :=
  …
  codes.sumBy (code => costs.shortestLength code * Code.numericPart code)
```

The natural spelling is `code.numericPart`. It fails **[run]**:

```
[E-UNKNOWN-FIELD] Error: `List` has no field or function `numericPart`
  looked in `List`
  Note: `Code.numericPart` takes a `List` first: write `Code.numericPart code …`
```

`codes` is declared `List Code`, so each `code` "is" a `Code`, yet the checker looked in
`List`. The same happens in 2025 day 3 (`banks |> .sumBy (.maxJoltage 2)` with
`banks: List Bank`, which is why `maxJoltage` was left outside `Bank`'s namespace) and in the
2024 day 9 proofs, where a `FreeSpace` that goes through `List.scanLeft` is seen as a `Map`.

The question is whether aliases should keep their own functions (and the checker be fixed to
find them more often), or whether a type that wants its own functions should be a new type.

## 2. What the dot rule promises today

[namespaces.md](namespaces.md) §4.8 says the namespace comes from the receiver's type *as
elaborated*, "with solved metavariables substituted", and that for an alias the view tries
the alias's namespace, then unfolds one step and tries again: `p: Price` tries `Price.show`,
then `Nat.show` **[checked]**. A "metavariable" is the checker's placeholder for a type it
hasn't worked out yet, such as the type of the lambda parameter `code` above.

So the written rule already says `code` should find `Code.numericPart`: the placeholder for
`code`'s type is solved by `List Code`'s element type, which is `Code`. The implementation
falls short of that because, as §3 shows, the placeholder is solved with `List NumericKey`
instead. Two cases the rule deliberately leaves out: `xs: List NumericKey` written by hand,
and a list literal `[…]`, have no `Code` anywhere in their types, so they look only in `List`.

## 3. The experiment

### 3.1 The scratch examples

`experiments/alias-functions/` (in the experimental commit) has four files:

- `Code.sw`: the day 21 shape, with an un-annotated lambda (`total`) and an annotated one
  (`(code: Code) => code.numericPart`, `totalAnnotated`).
- `Bank.sw`: the 2025 day 3 shape, `banks |> .sumBy (.maxJoltage 2)` with
  `Bank.maxJoltage (bank: Bank) (count: Nat)`.
- `FreeSpace.sw`: the day 9 shape: `List.scanLeft files (FreeSpace.of [1]) (free file =>
  free.move file)` (`steps`), the same through an un-annotated `let` (`viaLet`), and a
  function whose *first* argument is a lambda that fixes the state type before the initial
  state is seen (`stateFixedFirst`, the shape of `List.mapZipWithScanLeft`).
- `Predictability.sw`: a hand-written `List Nat` (`handWritten`), a literal (`literal`), a
  literal annotated as `Code` (`checkedLiteral`), a `let` from a function returning `Code`
  (`viaLet`), `codes.map (code => code.numericPart)` (`viaMap`), and a value passed through a
  generic identity function (`viaSame`).

### 3.2 Where the name is lost

Traced with temporary prints (not committed) on the receiver's type, on every placeholder
solution, and on every expected-versus-found comparison **[run]**:

1. **Dot notation forces the inferred type.** `step_value` in `crates/elab/src/dot.rs` calls
   `force` on a type that came from inference. While checking, a constant such as `FreeSpace`
   is kept as a *glued call*, a value that remembers "this is `FreeSpace`" and computes its
   unfolding only when asked (`crates/core/src/value.rs`, `eval_step` on `Term::Def`)
   **[checked]**. `force` asks, so the name is gone before the namespace is chosen. This was
   the hypothesis, and it's right, but it matters only when the glued call reached the
   placeholder in the first place.
2. **A definition's parameters arrive already unfolded.** For `total (codes: List Code)`, the
   trace shows the receiver `codes` with written type `List Code` but type value
   `Data(List, [Data(List, [Nat])])`, that is `List (List Nat)`. `body_term`
   (`crates/elab/src/lib.rs`) binds the parameters from `kernel::def_type`, the type value the
   kernel stored when the definition was declared, and declaration runs with gluing off
   (`kernel.rs`, `unglued`) **[checked]**. So when `codes.sumBy` matches `List ?a` against
   `codes`'s type, `?a := List Nat` (trace: `solve ?1 := … List Nat`). The written-type path
   in `dot.rs` rescues `codes.f` itself, but not anything inferred *from* `codes`.
3. **Checking against an expected type unfolds it.** In `stateFixedFirst`, the lambda
   `(file free => List.length (FreeSpace.move free file))` comes first; `free`'s type is a
   placeholder, settled when `free` is checked as `FreeSpace.move`'s first argument. The trace
   shows that comparison as `found ?1`, `expected Data(List, [Nat])`: `check_inner`
   (`crates/elab/src/check.rs`) starts with `let expected = force(g, expected)`, so the
   expected type has lost its name before the comparison solves the placeholder
   **[checked]**. Everything later inherits `List Nat`.

The kernel's own inference in `rewrite` (gluing off) was a suspect for the day 9 proofs; making
it glue changed nothing, so it isn't the cause there **[run]**.

### 3.3 The change

Fixes for places 1 and 2, 16 lines in two files:

- `dot.rs`: before forcing, `force_solved` (which replaces solved placeholders but stops at a
  glued call), and if the result is a glued call, try its namespace first; unfolding it is a
  `force`.
- `lib.rs`, `body_term`: while gluing, evaluate the definition's type again instead of using
  the stored value, so `codes: List Code` is `List Code` (with `Code` glued) in the body.

A third change, evaluating every *referenced* definition's type again while gluing
(`kernel::def_ty`), fixed no further example, and made `check-nested-apps` 35% more steps, so
it was dropped. A patch to place 3 (compare a local variable with the unforced expected type)
broke the standard library (`std/List/Toolkit.sw` and many `rfl` proofs in
`std/List/Lemmas.sw` stopped checking), so it was dropped too; place 3 needs a real design,
not a one-line change **[run]**.

### 3.4 Results

`main` is `9f9220ce`; "fix 1" is the `dot.rs` change alone; "fixes 1+2" is the commit
**[run]**.

| Example | `main` | fix 1 | fixes 1+2 |
|---|---|---|---|
| `Code.total`: lambda over `List Code` (day 21) | fails | fails | **works** |
| `Code.totalAnnotated`: `(code: Code) => code.numericPart` | fails | fails | **works** |
| `Bank.solve`: `.sumBy (.maxJoltage 2)` (2025 day 3) | fails | fails | **works** |
| `FreeSpace.steps`: through `List.scanLeft` | fails | **works** | **works** |
| `FreeSpace.viaLet` | fails | **works** | **works** |
| `FreeSpace.stateFixedFirst` (day 9 proofs' shape) | fails | fails | fails |
| `viaMap`: `codes.map (code => code.numericPart)` | fails | fails | **works** |
| `viaSame`: `(same code).numericPart` | fails | fails | **works** |
| `checkedLiteral`: `([1, 2]: Code).numericPart` | works | works | works |
| `viaLet` from a function returning `Code` | works | works | works |
| `handWritten`: `digits: List Nat` | fails | fails | fails (intended) |
| `literal`: `[1, 2].numericPart` | fails | fails | fails (intended) |

Note that on `main` even the *annotated* lambda parameter fails: an annotation on a lambda
checked against a known function type doesn't reach dot notation.

On the real programs, with fixes 1+2 **[run]**: day 21 with `code.numericPart` checks. In the
day 9 proofs, the `List.scanLeft` line (`Part2.sw:65`) checks with `free.moveFile file`, but
the two `List.mapZipWithScanLeft` lines (`:56`, `:79`) still fail with "`Map` has no field or
function `moveFile`": that's place 3. (Rewritten the same way, the lambdas at `:55`, `:64`,
`:78` fail for a different reason, `E-CANNOT-INFER`: their parameter's type isn't known at all
when the lambda is checked. Tried with the fix only.) 2025 day 3 wasn't rewritten, since `maxJoltage` takes
the count first; `Bank.sw` covers it.

### 3.5 Cost

`cargo nextest run --release -p stitchwort-driver --test std_library -p stitchwort-bench
--test baseline` **[run]**:

- `main`: 34 run, 34 passed.
- Fixes 1+2: 33 passed; `counts_have_not_regressed` fails on three rows over the 10%
  threshold: `check-list-rfl` steps +11.1% (720,069 → 800,080), `check-text-literal` 19 → 22
  steps, `check-nested-parens` 8 → 11 steps. The `check-closed-*` rows (which check a small
  file with the library) are +6.6% steps and +7% allocations; run-time rows are unchanged.

The extra steps are most likely fix 2 evaluating each definition's type a second time
**[inferred]**; fix 1 alone wasn't benchmarked. Storing a glued type value next to the
unglued one at declaration would avoid evaluating it per body.

aoc, cold cache (`.stitchwort` deleted), one run each **[run]**:

| | `main` | fixes 1+2 |
|---|---|---|
| `stitchwort check` (135 namespaces) | 39.3 s | 37.5 s |
| `stitchwort test` (910 tests, all pass) | 61.7 s | 60.6 s |

Within run-to-run noise: no measurable cost on real programs.

## 4. Is it predictable?

What a user would rely on is "a value I *got* as a `Code` has `Code`'s functions". With fixes
1 and 2 that holds for declared parameters, annotations, `let`s, function results, and values
that flow through `map`, `sumBy`, `scanLeft` and the like. It does not hold for:

- **Values that never were a `Code`.** `[1, 2]` and `digits: List NumericKey` look only in
  `List`. This matches Lean (§6) and is easy to state: the alias is in the type or it isn't.
- **Values whose type was settled from the unfolded side** (place 3). In `stateFixedFirst`,
  swapping the arguments of the user's own function changes whether `free.move` works. A user
  can't be expected to predict that; it's the case that makes the feature feel random.

Fixing place 3 would remove the second kind, leaving a rule that depends only on the types as
written. Until then, the error message is where predictability is won or lost. Today it says
"`List` has no field or function `numericPart`", plus a note naming `Code.numericPart`. It
could say why:

```
`code` has type `List NumericKey` here, which doesn't mention `Code`, so `.numericPart` was
looked up in `List`. `Code.numericPart` takes a `Code`: write `Code.numericPart code`, or
annotate the value as `Code` where it's made.
```

There is no worse failure than this message: since an alias and its underlying type are the
same type, a wrongly chosen namespace can only mean "not found", never a different function
called silently, unless both `Code.f` and `List.f` exist. In that case `code.f` calls
`Code.f` when `Code` is seen and `List.f` otherwise, and both type-check **[inferred]**. That
is the one silent surprise, and it's an argument for a warning when an alias declares a
function whose name its underlying type's namespace already has.

## 5. Proofs: aliases versus wrapper types

An alias is the same type, so every lemma about the underlying type applies unchanged:

- 2025 day 3's `Bank.best` matches on `Cons first rest` directly, and its proofs use
  `List.length`, `List.map`, `List.subsequenceCons` and the like on `Bank` values with no
  conversion **[checked]** (`Year2025/Day03/Proofs/Best.sw`).
- Day 9's `FreeSpace` functions are written with `Map`'s `alter`, `adjust` and `toList`, and
  the proofs `rewrite` with `List.mapAccumLeftList` at type `FreeSpace` **[checked]**.

With a wrapper type, `type Bank = { batteries: List Battery }` (a one-field record, which
Stitchwort already represents as the bare field at run time, [microtypes.md](microtypes.md)),
`bank.best` always finds `Bank.best`, but:

- every `List` operation and lemma is reached through `.batteries`, and the pattern
  `Cons first rest` becomes `{ batteries = Cons first rest }`;
- a lemma stated for `List Battery` has to be restated for `Bank` or applied to
  `bank.batteries`, and goals mention the projection, so `rewrite` must find `List.length
  bank.batteries` rather than `bank.length`;
- functions that build a `Bank` wrap the result.

For a microtype such as `UserId`, that friction is the point: it stops a `UserId` being passed
as an `OrderId`. For `Bank`, `Code` and `FreeSpace`, nobody wants to stop that; the name is
there for reading and for a namespace. Moving them to wrappers trades a dot-notation gap for
work in every proof that touches them **[inferred]**.

## 6. Other languages

- **Lean 4.** Field notation looks in "the namespace of the term's type, which is the
  constant's name", and "if the field is not found, but the constant can be unfolded to yield
  a further type which is a constant or application of a constant, then the process is
  repeated with the new constant". Its example, `def Username := String`: a `Username` value
  can use `String` functions "because `Username.any` is not defined and `Username` unfolds to
  `String`", but "`Username.validate` can't be called on `"admin"` using field notation,
  because `String` does not unfold to `Username`" **[cited]**. This is Stitchwort's written
  rule. Whether Lean's inference keeps `Code` through `List.map` is not stated there; I
  believe it does, since Lean's unifier doesn't unfold a constant to solve a placeholder, but
  I haven't checked **[unverified]**.
- **Kotlin.** "A type alias doesn't create a new type. It introduces an alternative name for
  an existing type. The alias and its underlying type are interchangeable." **[cited]** An
  extension function declared on an alias is an extension of the underlying type: a forum
  user found `fun Bar.bar()` (with `typealias Bar = Long`) callable on another alias of
  `Long`, and the reply was "A type alias does not create a new type, it just assigns an
  alternative name to an existing type" **[cited]**. For a type with its own identity, the
  docs contrast inline classes: "type aliases are assignment-compatible with their underlying
  type …, while inline classes are not … inline classes introduce a truly new type"
  **[cited]**.
- **Swift.** "Type aliases don't create new types; they simply allow a name to refer to an
  existing type." **[cited]** An `extension` on an alias extends the underlying type: a
  Swift Evolution pitch, "Limit typealias extensions to the typealias", complains that an
  extension of `HeaderKey` (an alias of `String`) "is also applied to normal strings"
  **[cited]**. The pitch's outcome isn't in what I read.
- **Scala 3.** Opaque type aliases "provide type abstraction without any overhead"; outside
  their scope "`Logarithm` is seen as an abstract type that has nothing to do with `Double`",
  and "Extension methods define opaque types' public APIs" **[cited]**. So the type with its
  own functions is the opaque one, not the plain alias.
- **Haskell.** A synonym and its definition "are completely interchangeable, except in the
  instance type of an instance declaration"; instances "can be defined for a type defined by
  newtype but may not be defined for a type synonym", and a `newtype` "creates a distinct type
  that must be explicitly coerced to or from the original type" **[cited]**.
- **F#.** "Type extensions cannot be defined on type abbreviations", and "Type abbreviations
  are not preserved in common intermediate language (CIL) code" **[cited]**.
- **TypeScript.** "aliases are *only* aliases - you cannot use type aliases to create
  different/distinct 'versions' of the same type. When you use the alias, it's exactly as if
  you had written the aliased type." **[cited]** Methods belong to classes and interfaces,
  so there is nothing to attach to an alias.

So: **Lean** (alias namespace, found when the name is in the type), **Kotlin and Swift**
(functions on an alias are functions on the underlying type, everywhere, a known complaint),
**F# and Haskell** (not allowed; use a real type), with **Scala 3** and Kotlin's inline
classes as the "own type, own functions, no run-time cost" answer.

## 7. Options

### (a) Keep alias functions, fix the lookup

Lean's rule, already the spec. Land fixes 1 and 2 (with 2 made cheaper), design a fix for
place 3, improve the error (§4). Users write `code.numericPart` on anything that was a `Code`.

- For: no change to programs or proofs; aliases keep every lemma; matches Lean, the closest
  language in spirit.
- Against: until place 3 is fixed, some cases depend on argument order. Values that never
  mention the alias (literals, hand-written types) never find it, which must be learnt.
  Checker cost, a few percent of steps, as measured.

### (b) Forbid functions in an alias's namespace; use wrapper types

`def Code.numericPart` is an error when `Code` is an alias ("`Code` is another name for
`List NumericKey`; give it its own functions by making it a record, `type Code = { keys:
List NumericKey }`, or put the function in a module namespace").

- For: dot notation is fully predictable; same as F# and Haskell.
- Against: §5's proof cost for every alias that has functions today (in aoc, games, examples
  and std, eight aliases have namespaced functions, by a rough grep: `Bank`, `Code`,
  `FreeSpace`, `Grid`, `Links`, `Meters`, `Price`, `Thunk`). It pushes people towards
  un-namespaced helpers, as 2025 day 3 already did.

### (c) In between

- **(c1) Functions on an alias extend the underlying type** (Kotlin, Swift): `[1,
  2].numericPart` works; `x.numericPart` works on every `List NumericKey`. Predictable, but
  the alias's functions spill onto every list of keys, two aliases of one type can't both have
  an `f`, and both languages have users asking for the opposite.
- **(c2) Keep (a)'s rule but don't chase place 3**: land fixes 1 and 2 and the better error,
  document "found where the type mentions the alias", and leave the argument-order cases
  with the prefix call. The cheapest, and fixes all three reported cases except the two
  `mapZipWithScanLeft` lines.
- **(c3) A `newtype`-like declaration as sugar for a one-field record** (microtypes.md option
  b1): doesn't answer this question; it makes (b)'s wrappers shorter to write.

## 8. Recommendation

Option **(a)**, reached through **(c2)** first:

1. Land fixes 1 and 2 as a real change, with fix 2 reworked to store a glued type value at
   declaration rather than evaluate per body, and re-measure against the bench baseline.
2. Change `E-UNKNOWN-FIELD`'s note to say the value's type as the checker knows it and that it
   doesn't mention the alias (§4).
3. Document the rule in the language guide: an alias's functions are found by dot when the
   value's type mentions the alias; `[…]` and hand-written underlying types don't.
4. Treat place 3 (checking against an unfolded expected type) as a separate design question,
   since it touches how every argument is checked, not dot notation.
5. Consider a warning when an alias's namespace and its underlying type's both define the
   same name (§4).

Use wrapper types for what they're for: a type that must not be mixed up with its underlying
one (`UserId`). Don't use them to get a namespace; in proofs that's paid for at every lemma.

## Sources

- Lean 4 reference, Function application, generalized field notation:
  <https://lean-lang.org/doc/reference/latest/Terms/Function-Application/>
- Kotlin, Type aliases: <https://kotlinlang.org/docs/type-aliases.html>
- Kotlin, Inline value classes ("Inline classes vs type aliases"):
  <https://kotlinlang.org/docs/inline-classes.html>
- Kotlin Discussions, "Extension functions on type aliases should only be accessable from
  similar types":
  <https://discuss.kotlinlang.org/t/extension-functions-on-type-aliases-should-only-be-accessable-from-similar-types/3722>
- Kotlin KEEP, type aliases ("Type aliases do not introduce new types"):
  <https://github.com/Kotlin/KEEP/blob/master/proposals/type-aliases.md>
- Swift, The Swift Programming Language, Declarations (Type Alias Declaration):
  <https://docs.swift.org/swift-book/documentation/the-swift-programming-language/declarations/>
  (read from its source,
  <https://github.com/swiftlang/swift-book/blob/main/TSPL.docc/ReferenceManual/Declarations.md>)
- Swift Forums, "Pitch: Limit typealias extensions to the typealias":
  <https://forums.swift.org/t/pitch-limit-typealias-extensions-to-the-typealias/6083>
- Scala 3 reference, Opaque type aliases:
  <https://docs.scala-lang.org/scala3/reference/other-new-features/opaques.html>
- Haskell 2010 report, §4.2.2 and §4.2.3:
  <https://www.haskell.org/onlinereport/haskell2010/haskellch4.html>
- F#, Type abbreviations:
  <https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/type-abbreviations>;
  Type extensions:
  <https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/type-extensions>
- TypeScript handbook, Everyday types (Type aliases):
  <https://www.typescriptlang.org/docs/handbook/2/everyday-types.html>
