# Proposal: namespaces, imports and dot notation

**Status:** draft 2, 16 October 2026. The user has answered §11 (see the
end of the decisions section), and an external reviewer has answered §12;
draft 2 adopts the review ([Changes since draft
1.1](#changes-since-draft-11)). Stages 0 and 1 ([§9](#9-staging)) are
built; stage 2 (dot notation) is design only.
It records decisions the user has already made, proposes the rest, and
keeps the questions that were put to the user
([§11](#11-questions-for-the-user)) and to the external reviewer ([§12](#12-open-questions-for-the-reviewer)).

This note is written to be read without knowing the codebase. §1 describes
the parts of Stitchwort it touches, checked against the source at commit
`787fa54` (and, for records, the records lane's work in progress at
`0d05f53`). Claims about other languages cite their sources
([Sources](#sources)). Anything not checked against a source is marked
**unverified**, and [What I couldn't verify](#what-i-couldnt-verify) lists
the gaps.

## Contents

- [The user's decisions (16 October 2026)](#the-users-decisions-16-october-2026)
- [Changes since draft 1.1](#changes-since-draft-11)
0. [Summary](#0-summary)
1. [Background: names in Stitchwort today](#1-background-names-in-stitchwort-today)
2. [Goals and non-goals](#2-goals-and-non-goals)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design)
5. [Whole-module scope and the dependency pre-pass](#5-whole-module-scope-and-the-dependency-pre-pass)
6. [Moving the prelude into namespaces](#6-moving-the-prelude-into-namespaces)
7. [Effects on the rest of the system](#7-effects-on-the-rest-of-the-system)
8. [Extending it later without breaking anything](#8-extending-it-later-without-breaking-anything)
9. [Staging](#9-staging)
10. [Recommendation](#10-recommendation)
11. [Questions for the user](#11-questions-for-the-user)
12. [Open questions for the reviewer](#12-open-questions-for-the-reviewer)
- [What I couldn't verify](#what-i-couldnt-verify)
- [Sources](#sources)

## The user's decisions (16 October 2026)

These are settled. The rest of the note designs around them.

- **D1. Scope.** Names are grouped into namespaces and can be written in
  full (`List.sort`, `Text.length`). **Dot notation by type**: `xs.sort`
  means `List.sort xs` because `xs` is a list, as with Lean 4's
  "generalized field notation". It should fit records' `p.name`
  ([records.md](records.md), stage 1 being built now). Splitting a program
  over several files comes later.
- **D2. Import syntax.** `import List (map, filter)` makes those names usable
  without `List.`. Nothing else for now: no "import everything", no hiding,
  no renaming, no import inside an expression. The design must leave room
  for all of those without breaking any program. Without an import, write
  `List.map` or use dot notation. Importing a name that doesn't exist is an
  error. If two imports bring in the same name, that's an error **only
  where the name is used**, and the message suggests the full form.
- **D3. One concept.** `import` will mean the same thing for namespaces now
  and for other files later, as in Python and Scala. There is no separate
  `open`.
- **D4. Small default.** The standard library is organised into namespaces.
  Only a small set of names is visible without an import: the core types and
  their constructors (`Nat`, `Bool`, `List`, `Maybe`, `Text`, `Char`,
  `Pair`, …, `Cons`, `Just`, …) and the operators. Everything else is
  reached by dot notation, by its full name, or by `import`. Possibly a
  file could also ask for no default names at all.
- **D5. No backwards compatibility.** Prefixed names (`textLength`,
  `textSplit`, …) are removed and replaced by namespaced ones.

**Answers to §11 (16 October 2026):**

1. `not` is visible everywhere, the one function in the default set: yes.
2. `IO` (and so `print`, `readLine`) is visible everywhere: yes. **Changed on
   19 October 2026 (D29):** `IO` stays a default name, but its operations
   don't: they are written `IO.print`, `IO.readLine`, `IO.readAll`, or
   imported (`import IO (print)`).
3. Other `List` names visible without the prefix inside `List.sum`'s body:
   **deferred (someday/maybe)**. Not in this proposal.
4. A user's file adding functions to library namespaces (`List.sum` defined
   in user code, then `xs.sum`): **deferred**. For now a user file can't
   add to `Std`'s namespaces (an error saying so); its own namespaces work
   as proposed. Reviewer question R9 becomes moot for now.
5. `Std` as the root that always means the standard library: yes.

**After the review (16 October 2026):**

6. **Constructors follow whichever type binding is visible.** A file that
   declares its own `Maybe` hides the default `Maybe`, and with it the
   default `Just` and `Nothing`: they're reached as `Std.Maybe.Just` and
   `Std.Maybe.Nothing` (or the file's own constructors of those names
   take their place). The constructors are visible *because* their type
   is, not because the type was once introduced (§4.4).

## Changes since draft 1.1

Draft 2 adopts the external review (§12) and brings the body into line with
the user's answers. In order of the note:

- **The body follows the decisions.** User files can't add to `Std`'s
  namespaces (Q4, §4.3). The check is made on the **resolved owner** of the
  namespace, so `List.sum` is refused exactly like `Std.List.sum` when `List`
  means the library's (new error `E-STD-NAMESPACE`, §4.12). `not` is in the
  default set through an **alias binding** to `Std.Bool.not`, not a wrapper
  definition (§4.6). `IO` is default. Constructors follow the visible type
  binding (decision 6, §4.4). Stage 1's tests no longer assume extension;
  they test its refusal instead (§9).
- **The built-in registry has explicit invariants** (§4.7): each entry is a
  finalised declaration of the current kernel environment; user name
  resolution can't change it; a missing entry never falls back to a search
  of user scope; entries are bound as declarations finish loading;
  completeness is checked before any user code; raw ids are never carried
  between environments.
- **Binding syntax and replacing a definition with a native are separate**
  (§4.7, §7.3). The first is an elaboration choice. The second also needs
  the natives' existing validation (exact type shape, and the content hash
  for compact text and the JS text natives), which stays as it is.
- **The stage-0 audit includes the effect machinery** (`Comp`, `Done`,
  `Call`, `bind`, `Sig`, `sigOp`, `sigRes`, `SigMap`, the translations and the
  operations' metadata) and the `Partial` lane's primitives, in both
  directions: code that *builds* a reference to a built-in, and code that
  *recognises* a term or value as one (§9, stage 0).
- **A stage-0 test alters the user-facing name environment** and checks that
  syntax, natives, codecs, printing and the runner still pick the original
  declarations. Writing `add` and writing `+` may mean different things once
  names can be redefined; that's intended (§4.7).
- **Dot notation has a deterministic type-head view** (§4.8): alias
  namespaces are found by rule, not by whether the evaluator happened to
  unfold the alias; lookup stops and reports when unfolding is blocked, and
  within the normal budget; a found `T.f` with no eligible receiver stops
  lookup rather than falling back.
- **Receiver-first checking is specified for complete calls** (§4.8.2), with
  a dependent test (`Sized.read`: `s.read 3` checks, `s.read 4` fails).
  Missing-argument abstractions that would capture a receiver whose type
  depends on a missing argument are refused with a clear error.
- **Evaluation order is spelled out** (§4.8.2): the receiver once, then the
  written arguments left to right, then arranged in parameter order.
- **Dependency edges are certain or speculative** (§5). Speculative
  dot-notation edges are narrowed wherever a reliable syntactic type head
  exists. The review's false mixed-kind cycle (a record type and a function)
  becomes a test, with a diagnostic that explains the artificial dependency
  and suggests the qualified form. `E-MUTUAL-SIGNATURE` never authorises a
  signature to mention a pending sibling.
- **Collecting declarations and registering full names are separate passes**
  (§5), so no declaration's full name is needed before the imports that
  determine it are resolved.
- **Type hashes include the full logical nominal path** (`Main.Geometry.Shape`,
  never a file-system path), and the summary's cache promise is qualified:
  definitions' own hashes leave names out, but many hashes change once
  through the data types they mention (§0, §7.4).
- **The elaboration cache must rerun lookups** to revalidate, including the
  absence of a nearer candidate; recording the chosen target isn't enough
  (§7.5, still deferred).
- **JS** (§7.3): the new name encoding, with tests that the whole
  generator's namespaces are disjoint (definitions, runtime helpers,
  generated locals, constructor helpers) and that every source character the
  lexer accepts gives a valid JS identifier. Short export names with
  collision errors, tested on the same type reached twice (not a collision)
  and two types with one short name (a collision). Hidden constructors such
  as a record's `mk` move to a name source can't spell (`Person.%mk`), since
  the grammar will accept lowercase qualified names.

## 0. Summary

**In plain words.**

- Every library function gets a home: `Text.length`, `List.length`,
  `Nat.toText`. You can write the full name anywhere, with no setup.
- **Dot notation** saves typing. `t.length` means `Text.length t` when `t` is
  a `Text`, and `xs.length` means `List.length xs` when `xs` is a list. The
  compiler picks the namespace from the type of the thing before the dot.
  It's the same mechanism as a record's `p.name`: a record's fields simply
  live in the record type's namespace.
- **`import Text (split, join)`** lets you write `split` and `join` on their
  own in that file.
- **Without any import**, a file sees only the core types, their
  constructors and the operators (`+`, `==`, `++`, …). Everything you define
  yourself is visible in your own file and **hides** a default name with the
  same spelling. So you can at last define your own `length` or `Maybe`
  (today that's an error).
- **You put a definition in a namespace by naming it that way:**
  `Shape.area : Shape -> Nat` at the top level, next to your own `type Shape`.
  After that, `s.area` works too. The library's namespaces are closed to
  user files for now: `List.sum` in your file is an error.
- **Names stay out of a definition's own hash.** Moving `textLength` to
  `Text.length` doesn't by itself change its hash. But a data type's hash
  gains its full name (`Std.Text`), so the move changes every hash that
  mentions a library type once, and cached test results are recomputed once.

**For the reviewer.**

- **A single global tree of full names**, like Lean or Scala packages. The
  library lives under a reserved root `Std`, and the user's file has its own
  root. Namespaces are just name prefixes; they carry no semantics.
- **A type `T` owns the namespace `T`.** That namespace holds `T`'s
  constructors, its record projections and its ability operations, plus
  anything declared as `T.x`.
- **Unqualified names resolve in a fixed order of levels.** In order:
  locals, then the file's own declarations, then explicit imports, then the
  default set. A higher level hides lower ones without comment. Two
  candidates on the same level are an error only when the name is used
  (`E-AMBIGUOUS`).
- **Dot notation follows Lean** ([L4], [L5]):
  - The elaborator infers the receiver's type and reduces it to a head
    constant `T` through a deterministic **type-head view**: the folded head
    first, then one explicit unfolding step at a time, stopping when
    unfolding is blocked.
  - It then resolves `T.f` and passes the receiver as the first explicit
    parameter whose declared type is headed by `T`.
  - If the head is an unsolved metavariable, that's `E-CANNOT-INFER`. There
    is no postponement (Lean postpones, see [§3](#3-how-other-languages-do-it)).
  - Unlike a plain application, **the receiver is elaborated first** and its
    type is unified with its parameter before the other arguments are
    checked. So `xs.map (\x -> x.length)` infers where
    `List.map (\x -> x.length) xs` can't.
- **Built-in syntax binds to fixed identities, not to names.** A registry
  of finalised declarations, bound as the library loads and checked complete
  before user code, serves operators, literals, `if`, `()`, the effect
  machinery, natives, JS codecs and text natives, the printer and the
  runner. Today these are looked up by name in the user's scope, which is
  only safe because prelude names can't be redefined (§1.3). This is a
  prerequisite (stage 0), and it also fixes a latent problem: the JS
  boundary picks codecs by type *name*.
- **The whole-module dependency pre-pass** ([mutual-recursion.md
  §10.2](mutual-recursion.md#102-as-built-milestone-2-function-groups-and-forward-references))
  can't know where `x.f` points before types are known. It over-approximates
  with **speculative** edges to every module declaration named `….f`,
  narrowed where a syntactic type head is reliable. This can merge
  components that don't really depend on each other, and the diagnostics say
  so (§5).
- **No new kernel rules.** A definition's own hash still leaves out its
  name. A data type's hash gains its full logical name, which changes every
  hash that mentions a data type, once.

## 1. Background: names in Stitchwort today

### 1.1 One flat table, prelude first

The elaborator keeps every global name in one flat map from a string to what
it names (`names: HashMap<String, (Global, Span)>`,
`crates/elab/src/lib.rs:67`). That covers definitions, data types,
constructors, abilities and operations. The prelude
(`crates/elab/src/prelude.sw`, 770 lines; now `std/core.sw`) is loaded first, as a module of
its own (`crates/driver/src/driver.rs:56-60`), and the user's file is
elaborated against the same table. (Since docs/proposals/std-library.md stage
1, `std/core.sw` (formerly `prelude.sw`) is the always-loaded *core*, and the library files under
`crates/elab/src/std/` are checked when a program uses them; their names are
in the same table from the start, as pending entries.)

A new top-level name that's already in the table is refused
(`new_module_name`, `crates/elab/src/module.rs:338`). The message reads
"`` `x` is already defined ``". Two names, `rfl` and `J`, are reserved
outright (`lib.rs:38`). That is the **known issue** in `TODO.md`: user code
can't define `length`, `append`, `not`, `fst`, … The test
`examples/reject/duplicate-definition.sw` checks exactly this:

```
-- expect-error: E-DUPLICATE
-- `length` is already defined by the prelude.
def length : Nat := 0
```

To leave room for user names, the text operations got prefixes
(`textLength`, `textSplit`, `textJoin`, …).

### 1.2 Whole-module scope

Inside a file, declarations can come in any order. `elaborate_module`
(`module.rs`, header comment) does three things:

1. It enters every name the file declares as `Global::Unchecked`, reporting
   duplicates.
2. It computes each declaration's dependencies from its **free names, by
   syntax alone**, before anything is type-checked.
3. It checks strongly connected components in dependency order.

Definitions in one component are checked together and face extra rules:
`E-MUTUAL-SIGNATURE`, full application inside the cycle, and no use by
`auto`. A lowercase name in a type position is an automatically bound type
variable unless it names something. If it names a declaration of the module,
there's a warning, `W-MODULE-NAME` (`crates/elab/src/autobind.rs:80-81`).

### 1.3 Built-in syntax finds prelude definitions by name

Several pieces of syntax turn into calls of prelude definitions. They find
them by looking the name up in the same flat table that user code uses
(`def_named` and `ctor_named`, `crates/elab/src/check.rs:1195-1215`):

| Syntax | Looks up | Where |
|---|---|---|
| `+ - * / %`, `< <=` | `add`, `sub`, `mul`, `div`, `mod`, `LessThan`, `LessEq` | `check.rs:350-365` |
| `a ++ b` | `textAppend` if `a`'s type is `Text`, `append` if it's a `List`, else an error | `check.rs:824-851` |
| `a == b`, `a != b` | `toBool` with a decision found by `auto`, `Not` | `check.rs:328-348` |
| `if`, `if h :` | `ifThenElse`, `elimDec` | `check.rs:891-922` |
| literals, `()` | `MkChar`, `MkText`, `Nil`, `Cons`, `UnitType` | `check.rs:217-260` |
| `auto` | `fromYes`, `Trivial`, `Yes` | `auto.rs:89-90,164` |

Other components identify prelude things by name too:

- **The kernel's natives** are attached to prelude definitions by name while
  the prelude loads: `add`, `eqNat`, `decEqNat`, … (`lib.rs:1048`), along
  with `Nat` and `Bool` (`lib.rs:868-869`). The kernel's `native.rs` finds
  `Void` by name (`find_data("Void")`, lines 194 and 329).
- **The JS generator** picks boundary codecs by the type's *name*
  (`crates/js/src/lib.rs:188-197`, with the comment "Prelude names can't be
  redefined, so these are the prelude's"). It binds its 14 text natives by
  name and then hash (`lib.rs:1761-1765`, same comment), and finds
  `ifThenElse` by name (`lib.rs:983`).
- **The pretty printer** prints `List`, `Nat`, `Char`, `Text`, `UnitType`
  and others specially by name (`crates/core/src/pretty.rs:275-277`).
- **The effect machinery** (added in draft 2, from the review) builds and
  recognises `Comp`, `Done`, `Call`, `Plus`, `NoOp`, `Sig`, `sigOp`, `sigRes`,
  `bind`, `foldComp`, `translate`, the `sig…` combinators, `runPure`,
  `handlePlus` and `UnitType` by name (`data(cx, "Comp")`,
  `call(cx, "bind", …)` in `crates/elab/src/effects.rs`). The `Partial`
  lane's kernel primitives and step function (`crates/core/src/partial.rs`,
  `step.rs`) and its translation (`crates/elab/src/partial.rs`) find `Comp`,
  `Plus`, `SigMap`, `Rec`, `PlusRes` and `RecRes` by name too.
- **Records** generate a decision procedure as *source syntax* that names
  `Yes`, `No`, `cong` and `Decidable` (`crates/elab/src/records.rs`), so it
  is elaborated against whatever those names mean in scope.
- **Number patterns** are compiled to `Zero` and `Succ` patterns found by
  name (`crates/elab/src/lib.rs`, `ctor_named`).

So **every one of these depends on prelude names being unredefinable**.
Letting user code reuse names means binding them some other way first
([§4.7](#47-operators-and-other-built-in-syntax)).

### 1.4 Names that already have dots

An `ability State` generates names with dots: a data type `State` whose
constructors are `State.get` and `State.put` (one per operation), plus
`State.res` and `State.elim` (`declared_names`, `module.rs:963-981`;
`lib.rs:382`). The records lane generates `Person.mk` for a record's
constructor and `Person.name`, `Person.age` for its projections, and says
these "can't be written in source" ([records.md
§6.2](records.md#62-what-the-kernel-sees)). The JS generator writes a dot in
a definition's name as `$$` and a prime as `$` (`def_name`,
`crates/js/src/lib.rs:1924-1928`).

### 1.5 `auto` finds procedures by type

`auto` looks for a decision procedure by scanning **every** checked
definition whose result type is `Decidable …`, most recent first
(`decision_procedures`, `crates/elab/src/auto.rs:166-187`). Names play no
part, so this is unaffected by where a procedure lives.

### 1.6 Hashes and names

A definition's hash leaves out its own name (`crates/core/src/hash.rs:29-32`:
"Left out, so they don't affect identity: the definition's own name, binder
names, local variable names … Data types are nominal, so their names *are*
included, along with their constructors' names", and `hash.rs:124-132`).
The test cache is keyed by the test's hash (`crates/driver/src/driver.rs:127`).
DESIGN §11 says a nominal type's hash should include its **logical module
name** as well as its own name. As built, only the type's own name is
hashed.

### 1.7 Records' field access

The records lane (stage 1, in progress) adds `.` to the lexer, valid only
with no spaces around it (`p.name`, `(f x).name`, `p.address.city`). It
binds tighter than application, and the AST node is `Expr::Field(e, name)`.
It resolves `p.name` by inferring `p`'s type. If that type is a declared
record with a field `name`, the access is a call of the generated projection
`Person.name`. Otherwise the error is `E-UNKNOWN-FIELD`, `E-NOT-A-RECORD`,
or `E-CANNOT-INFER` when the type isn't known yet ([records.md
§6.1](records.md#61-surface)). Dot notation by type generalises exactly
this.

## 2. Goals and non-goals

**Goals**

1. Library names don't collide with user names. The prelude can grow (the
   standard library is next in `TODO.md`) without taking names away from
   programs.
2. Short, readable code without clutter: `t.length`, `xs.sort`,
   `line.split ','`.
3. One rule for records' `p.name` and for `xs.sort`.
4. Errors that say what to write instead.
5. Room to add multi-file programs, "import everything", hiding, renaming
   and local imports **later, without changing the meaning of any program
   that already works**.
6. Nothing in the trusted kernel changes, and nothing about identity:
   names stay out of definitions' hashes.

**Non-goals (for now)**

- Several files, packages, visibility modifiers (`private`) and
  re-exporting.
- Overloading: one short name meaning several things, resolved by type.
  Ambiguity is an error (D2). §8 shows how it could be added later
  compatibly.
- `namespace … end` blocks (§4.3 explains why, and §8 how to add them).
- Type classes. Operators stay as they are (§4.7); §8 sketches a namespace
  route for `Int`.

## 3. How other languages do it

**Lean 4** is the closest model, and D1 names it.

- *Namespaces come from declarations.* A declaration's dotted name puts it
  in that namespace, and creates the namespace if needed: "If the declared
  name has more than one component, then its namespace is nested within the
  current namespace" [L1].
- *Constructors live in their type's namespace* (`HotDrink.tea`), and so do
  structure projections. `open X`, `open X (a b)`, `open X hiding a`,
  `open X renaming a → b` and `open X in e` cover the import forms D2
  defers. Names listed in `open X (a)` "must exist in exactly one of the
  considered namespaces", so a missing name is an error at the `open`
  [L1].
- *`protected`* keeps a name out of `open`; *`private`* keeps it inside its
  file [L2].
- *Resolution:* "Names in the current namespace take precedence over names
  in the root namespace" [L1]. A dotted identifier `x.y.z` is resolved by
  its longest prefix that names something: "The suffix that was not included
  in the resolution process is then treated as field projections or field
  notation". For each prefix, local variables come first, then global names
  [L3]. An identifier that resolves to several names is elaborated with each
  candidate, and "It is an error if more than one succeed or if all fail"
  [L3].
- *Generalized field notation:* `e.f` is "roughly short for `T.f e` where
  `T` is the type of `e`". `e` is passed as the "first explicit parameter of
  type `T ...`", which needn't be the first argument. Functions use the
  `Function` namespace. If `T.f` isn't found and `T` can be unfolded, "the
  process is repeated with the new constant". If the type "is not an
  application of a constant (e.g. a metavariable or a universe) then it
  doesn't have a namespace" [L4].
- *In Lean's source* (`resolveLValLoop`, `Elab/App.lean`), the type is first
  reduced without unfolding definitions (`whnfCore`). If it is a
  metavariable, elaboration is **postponed** (`tryPostponeIfMVar`), and if
  it stays unknown the error is "Type of … is not known; cannot resolve
  field". Structure fields are tried first, then `T.f`, then the type is
  unfolded and the loop repeats [L5].
- *Leading dot:* `.some x` looks the name up in the namespace of the
  *expected* type [L3].

**Agda.** Modules are opened with `open M using (a; b)`, `hiding`,
`renaming (a to b)`, and re-exported with `open M public`. `import M` only
loads; names need `open` to be used unqualified [A1].

- "When you define a datatype it also defines a module so constructors can
  now be referred to qualified by their data type", and records do the same
  [A1].
- Its ambiguity policy is the one D2 chose: "allow the introduction of
  ambiguous names, but give an error if an ambiguous name is used" [A1].
- Postfix projection is `r .field` [A2].

**Haskell 2010.** `import M (a, b)`, `import qualified M as N`, and
`hiding` [H1 §5.3].

- Clashes are reported only on use: "It is not an error for there to exist
  names that cannot be so resolved, provided that the program does not
  mention those names" [H1 §5.5.2].
- Unlike the other languages here, **a module's own top-level name does not
  hide an imported one**. In the report's `sin` example, the local `sin` is
  legal, but references "must both be qualified" [H1 §5.5.2]. This is the
  well-known reason for `import Prelude hiding (…)`.
- The Prelude is imported implicitly "if and only if it is not imported with
  an explicit import declaration", so `import Prelude ()` turns it off
  [H1 §5.6.1].
- GHC's `OverloadedRecordDot` requires no space: `r.x` selects a field and
  `f . g` composes [G1].

**Elm.** Every file implicitly starts with a fixed list of imports, among
them `import List exposing (List, (::))`, `import Maybe exposing (Maybe(..))`
and `import String exposing (String)`. In other words: types and their
constructors exposed, functions qualified (`List.map`, `String.length`).
The stated reason: such names are "very unlikely to overlap with anything
that anyone will ever write in a library … easier to use whatever version
of `map` suits your fancy" [E1].

- In the compiler, top-level definitions override imports ("Use union to
  overwrite foreign stuff"), and clashes between imports are reported only
  on lookup [E2].
- Exposing a name that doesn't exist is an error
  (`ImportExposedValueNotFound`) [E2].
- D4 is essentially Elm's default.

**Python.** `from m import a, b` raises `ImportError` if `a` isn't found
[P1].

**Scala 3.** `import p.{a, b}`, `import p.*`, renaming `a as b`, hiding
`a as _`. "`import` statements can be anywhere" [S1].

- Binding precedence, from highest: definitions in the same compilation
  unit, then explicit imports, then wildcard imports, then everything
  supplied by the compiler (`scala.*`, `Predef`) [S2].
- A reference is an error if no binding shadows the others [S2].
- This is very close to the order proposed in §4.4.

**Rust.** Explicit items and imports may shadow glob imports, and "The
errors occur at time of use, not time of import" [R1, R2]. The prelude's
names "are not part of the module itself: they are implicitly queried
during name resolution" [R3]. `#![no_implicit_prelude]` turns it off [R3].

**OCaml.** `Stdlib` "is automatically 'opened' when a compilation starts"
[O1]. Local opens are written `M.(e)` and `let open M in e` [O2]. An `open`
silently shadows earlier names; warnings 44 and 45 report it on request, and
`open!` marks it as intended [O3].

**Unison.** "names are just separately stored metadata that don't affect the
function's hash" [U1], which is Stitchwort's position too.

- A name resolves if it "is a suffix of exactly one fully qualified name in
  the environment" [U2].
- *Type-directed name resolution:* if a name is ambiguous or unknown, Unison
  picks the one candidate whose type fits, and otherwise reports an error
  [U3].

**Idris 2.** Names in different `namespace`s "can be disambiguated by their
types" [I1]. Record projection `.field` "is a postfix projection operator
that binds tighter than function application" [I2].

- `foo.bar` (lowercase first) is a projection, while `Foo.bar` is one
  namespaced identifier [I2]. Stitchwort's convention in §4.13 is the same.
- Ambiguous names are elaborated as alternatives and **retried later** when
  more is known [I3].

**Koka.** `s.encode(3)` "is simply syntactic sugar for the function call
`encode(s,3)`", where `encode` is then resolved by overloading on type. So
`map` over a list and over a string are both just `map`, and an ambiguous
use needs an annotation [K1]. This is the alternative to Lean's design:
dot notation picks a *visible* function by type, rather than looking in the
type's namespace.

**What this suggests.**

| Question | Answer by most systems | This proposal |
|---|---|---|
| Does a type get a namespace automatically, with its constructors in it? | Yes (Lean, Agda, Idris for records) | Yes |
| Do a module's own names hide imported/default ones? | Yes (Elm, Scala, Rust); Haskell is the exception | Yes |
| Is ambiguity reported at import or at use? | At use (Haskell, Agda, Rust, Elm, Scala) | At use (D2) |
| Importing a name that doesn't exist? | Error (Python, Elm, Lean `open X (a)`) | Error (D2) |
| `x.f` when `x`'s type isn't known yet? | Lean and Idris postpone, then error; Koka and Unison error | Error with a suggestion (no postponement yet) |

## 4. The design

### 4.1 Words used here

- **Full name.** A name with every namespace written out, such as
  `Std.List.length` or `Geometry.Shape.area`.
- **Short name.** The last component: `length`.
- **Namespace.** A prefix of full names. It exists as soon as anything is
  declared in it. It is not a value and carries no meaning beyond names.
- **Qualified name.** What a program writes with dots, such as `List.length`.
  Its first component is resolved like any name, and the rest is looked up
  inside it.
- **Visible.** A short name is visible in a file if it can be written there
  without a qualifier.

### 4.2 Where names live

- **The library's root is `Std`.** Every library name has a full name under
  it: `Std.List`, `Std.List.length`, `Std.Text.split`. Programs almost never
  write `Std.`: it's the escape hatch for when a file hides a library name
  (§4.4). `Std` is reserved, like `rfl` and `J`.
- **The user's file has its own root.** Its top-level declarations are
  `area`, `Shape` and so on, and a declaration written `Geometry.area` is in
  the file's namespace `Geometry`. (Later, when there are several files,
  each file's root is its module path; see §8.)
- **A type owns the namespace of the same name.** Declaring
  `type Shape = | Square (side : Nat) | Rect …` creates:
  - the type `Shape`;
  - the namespace `Shape`, holding the constructors `Shape.Square` and
    `Shape.Rect`;
  - for a record, its field projections (`Person.name`);
  - for an ability, its operations (`State.get`, `State.put`).
  Anything declared as `Shape.x` joins the same namespace, as in Lean and
  Agda.
- **Record fields and namespace functions share one space.** A user
  definition `Person.name` next to a field `name` is `E-DUPLICATE`, so
  "field or function?" never needs an answer (§4.8).
- **Generated names move out of the way.** An ability's generated
  constructors, `res` and `elim` (§1.4) must not take `State.get` or
  `State.elim` from the user. They get names source can't spell, for example
  `State.%get`, `State.%res` and `State.%elim` (the elaborator already uses
  `%` for generated binders such as `%o`). `State.get` then means the
  *operation*, which is what a reader expects. The same applies to records'
  constructor `Person.mk`: draft 1.1 said it was unwritable because it's
  lowercase, but the grammar of §4.13 accepts `Person.mk`, so it becomes
  `Person.%mk`.

### 4.3 Declaring into a namespace

**Proposed: the declaration's own name says where it goes.**

```
type Geometry.Shape =
  | Square (side : Nat)
  | Rect (width : Nat) (height : Nat)

def Geometry.Shape.area : Geometry.Shape -> Nat
  | Square s => s * s
  | Rect w h => w * h

theorem Geometry.Shape.areaSquare (s : Nat) : Geometry.Shape.area (Square s) = s * s := …
```

**The qualifier is resolved the way it is in an expression** (§4.4).

- A qualifier that resolves to the file's own type or namespace
  (`Geometry.Shape` above, once declared) adds to it, and `sh.area` then
  works everywhere in the file.
- A qualifier that doesn't resolve to anything (`Geometry`) creates a new
  namespace in the file.
- **A qualifier that resolves into `Std` is refused** (the user's answer to
  Q4): `E-STD-NAMESPACE`, "the standard library's namespaces can't be
  extended". The check is on the **resolved owner**, not on the spelling, so
  in a file without its own `List`, both `List.sum` and `Std.List.sum` are
  refused. In a file that declares its own `type List`, `List.sum` resolves
  to *that* `List` and is fine.
- Adding a name the file's namespace already has is `E-DUPLICATE`.

Allowing extension later (Q4, deferred) turns `E-STD-NAMESPACE` errors into
programs, so it's compatible (§8).

**Why this form, and not a `namespace List … end` block?**

- *Layout.* A declaration starts at column 0 and continues on indented lines
  ([syntax.md](../syntax.md#layout)). An indented block would break that
  rule. A Lean-style unindented `namespace X … end X` keeps it, but then the
  meaning of a declaration depends on a line far above it.
- *Each declaration says where it lives.* That makes searching easy and needs
  no state while parsing.
- *Lean has both forms* [L1], so adding blocks later is a known path. A block
  would only be a shorthand for writing the prefix (§8).

**The cost:** each equation line repeats the full name
(`Geometry.Shape.area (Square s) = …`).
A namespace block would remove that; §8 keeps the option open.

**Inside `Shape.area`'s equations, other `Shape` names still need `Shape.`**
(or dot notation). Lean opens the declaration's namespace in its body [L1];
this proposal doesn't (Q3, deferred). Opening it with *highest* priority, as
Lean does, would let `perimeter` silently mean `Shape.perimeter` inside
`Shape.area` even though the file defines its own `perimeter`, and that's
surprising. Opening it later at *lowest* priority is a compatible addition
(§8).

### 4.4 What a short name means

A short name `x` is resolved by going down these levels and stopping at the
first level where `x` is found:

| Level | Source of the name | Example |
|---|---|---|
| 1 | Local binders: function parameters, `let`, pattern variables, named implicit parameters, handler variables | `\xs -> …` |
| 2 | **The file's own top-level declarations**, plus the constructors of the file's top-level types and the operations of its top-level abilities | `area`, `Shape`, `Square` |
| 3 | **Names brought in by `import`** | `import List (map)` |
| 4 | **The default set** (§4.6) | `Nat`, `Cons`, `Just` |

- **A higher level hides lower ones without a warning.** That's the Elm,
  Scala and Rust behaviour [E2, S2, R1]. It fixes the known issue: a file
  can define `length`, `Maybe` or `Yes`, and inside that file the name means
  the file's own.
- **Two different things at the same level** are `E-AMBIGUOUS`, reported
  where the name is used and never where it's introduced (D2).
  - Two imports of `length`, from `List` and `Text`, are fine until
    `length` is written.
  - Two types in one file that both have a constructor `Square` are fine
    until `Square` is written on its own; `Shape.Square` and `Tile.Square`
    always work.
  - The same thing reached twice (say, imported twice) isn't ambiguous.
- **An import that clashes with a declaration of the same file is an
  error at the import** (`E-IMPORT-CLASH`). The file's declaration would hide
  the import completely, so the import can only be a mistake. Rust refuses
  the same thing (E0255; **unverified** against the Reference text).
- **A qualified name `A.b.c`** resolves its first component `A` by the same
  levels, and then looks inside it. If a local variable is called `A`, it's
  dot notation instead (§4.8).
- **`Std.…` always means the library**, whatever the file declares. The
  user's own `type List` hides the library's in that file, and `Std.List.map`
  still reaches the library's function.
- **Constructors and operations follow their type's visible binding**
  (decision 6). Whenever a type or ability is visible by its short name, so
  are its constructors or operations, at the same level, whether through
  level 2, an import, or the default set. So `import Effect (Comp)` brings
  in `Done` and `Call` too, the way Elm's `Maybe(..)` does. It's one rule
  instead of two kinds of import item.
  - The rule is about the binding that **survives**, not the one that was
    introduced. A file declaring its own `type Maybe` hides the default
    `Maybe`, and so hides the default `Just` and `Nothing` with it, even if
    the file's `Maybe` has differently named constructors. They're still
    reachable as `Std.Maybe.Just`.
  - Implementation: the default set and each import contribute a
    constructor's short name only if their type's short name, looked up
    through all four levels, resolves to that same type.
- **Not visible by short name:**
  - names in the file's own namespaces (`Geometry.area` is written so, or
    used by dot notation);
  - record fields (`p.name` or `Person.name`);
  - anything in the library outside the default set.

### 4.5 `import`

```
import List (map, filter)
import Text (split, join)
import Effect (Comp)
```

- **Placement.** Imports go at the top of the file, before any other
  declaration, each starting at column 0. Since names are file-wide anyway,
  where an import appears couldn't change its meaning. Requiring the top
  keeps files easy to read, and allowing imports elsewhere later breaks
  nothing.
- **The path.** It names a namespace and is resolved like a qualifier
  (§4.4). So `import List (…)` means the library's `List` unless the file
  declares its own `List`. `import Std.List (…)` always means the library's.
- **Each item** is a short name declared directly in that namespace:
  lowercase or uppercase, a function, theorem, type, constructor or
  ability.
  - Importing a type also imports its constructors (§4.4).
  - An item may be any sub-namespace (D50, stage 2 of the library). If it
    is a type, `import Std.Effect (Comp)` makes `Comp` usable as a type and
    as a qualifier, `Comp.Done`. If it declares no name of its own,
    `import Std (Eq)` makes `Eq` usable as a qualifier (`Eq.sym`).
  - The path is read without the file's imports, so a library namespace
    that isn't a default name is written in full in a path:
    `import Std.Effect (Comp)`, not `import Effect (Comp)`.
- **Errors** (§4.12):
  - An unknown namespace is `E-IMPORT-UNKNOWN`. So is an unknown item: "`List`
    has no `sortt`", with near-miss suggestions.
  - A clash with the file's own declaration is `E-IMPORT-CLASH`.
  - Importing the same item twice is a warning, not an error.
  - Listing nothing (`import List ()`) is a syntax error. That deliberately
    keeps the form free for later (§8).
- **What an import doesn't do.** It doesn't load anything, change what `auto`
  finds, or affect what a program means beyond which short names may be
  written.

### 4.6 The default set

**Proposed: the default set is exactly what `Std` declares at its root.** In
the library source that's a visible, checkable rule: anything not in a
namespace is default. Constructors follow their type (§4.4), and so do the
operations of a user's own abilities. The library's abilities are the
exception: since 19 October 2026 (D29, ticket SW-134) `IO`'s operations are
not default. A program writes `IO.print "hi"`, or `import IO (print)` for
the short name. The qualifier needs no import, because `IO` is default.
The operations are still visible unqualified inside the library itself.

| Default | With |
|---|---|
| `Nat` | `Zero`, `Succ` |
| `Bool` | `False`, `True` |
| `List` | `Nil`, `Cons` |
| `Maybe` | `Nothing`, `Just` |
| `Pair` | `MkPair` |
| `Char` | `MkChar` |
| `Text` | `MkText` |
| `Ordering` | `Less`, `Equal`, `Greater` |
| `Decidable` | `Yes`, `No` |
| `And` | `Both` |
| `Or` | `Inl`, `Inr` |
| `Int` | `OfNat`, `NegSucc` |
| `Void` | (no constructors) |
| `Unit` | `Trivial` |
| `Not` | (a definition: `Not p = p -> Void`, used in many types) |
| `IO` (ability) | (nothing: its operations are written `IO.print`, `IO.readLine`, `IO.readAll`, or imported; changed 19 Oct 2026, D29) |
| `Partial` (ability, from the `Partial` lane) | (its operations, if any) |
| `not` | an **alias** of `Std.Bool.not` (Q1: yes) |

The table has 16 type and ability names, plus `Not`, `not`, and 22
constructors.

**`not` is an alias, not a definition at the root.** `not` lives in `Bool`
like every other `Bool` function, and the library's root declares
`alias not = Bool.not` (spelling for implementation): a second *name* for
the same declaration, not a wrapper definition. So `not`, `Bool.not` and
`b.not` are one declaration with one hash, errors print it as the file
would write it, and a user's own `not` hides the alias like any default
name. Aliases are internal to the library for now; user-written aliases are
a compatible later addition (§8).

**Qualifiers follow the default set** (D50, 20 October 2026; this replaces
"Qualifiers are always available"). A namespace is usable as a qualifier
without an import only if its name is a default name or the file's own. So
`List.map` and `Int.abs` work everywhere, but `Eq` (for `=`, §4.8),
`Effect` (the machinery behind abilities) and `Builtin` (what syntax uses,
such as the type of `()`) are written `Std.Eq.sym`, or imported with
`import Std (Eq)`. A bare `Eq.sym` is `E-UNKNOWN-NAME` with the note "`Eq`
is `Std.Eq`; add `import Std (Eq)`, or write `Std.Eq.sym`". Dot notation
(`p.sym`) finds the namespace from the type and needs no import (§4.8). No
namespace joins the default set for this (D55).

**The operators aren't names** and need no visibility (§4.7).

**Leaving out the default set** (D4's "possibly") isn't proposed for the
first stage; §8 shows a compatible form.

**A tension to keep watching** (Matt, 19 Oct 2026). Every name in the default
set is one a program gets without asking for it, which is convenient but
implicit, and crowds out a file that wants a different set of basics. The
set stays small for now: types, their constructors and operations, and
`not`. Nothing joins it without a reason as strong as these have, and an
opt-out like Haskell's `NoImplicitPrelude` isn't planned. Built-in syntax
(operators, literals, `if`) is the deeper version of the same tension: it
always means `Std`'s declarations (§4.7), whatever a file imports.

### 4.7 Operators and other built-in syntax

**Each piece of built-in syntax is bound to one fixed library declaration,
by identity, when `Std` is loaded.** It's never looked up by name in the
user's scope.

- `a + b` always means `Std.Nat.add a b`, even in a file that defines its
  own `add` or `Nat`.
- The same goes for every row of the table in §1.3:
  - `-` `*` `/` `%`;
  - `<` and `<=` (`Std.Nat.LessThan`, `Std.Nat.LessEq`);
  - `!=` (`Std.Not`) and `==` (`Std.Decidable.toBool`, with the decision
    found by `auto` exactly as now);
  - `if` (`Std.Bool.ifThenElse`) and `if h :` (`Std.Decidable.elim`);
  - literals (`Std.Char.MkChar`, `Std.Text.MkText`, `Std.List.Nil` and
    `Std.List.Cons`);
  - `()` (`Std.Builtin.UnitType`).
- `++` keeps its two cases: `Std.Text.append` for texts, `Std.List.append`
  for lists.

**The implementation: a built-in registry.** A table of built-ins (data,
constructor and definition ids) replaces `def_named`, `ctor_named` and
`data_named` for these uses, and the name-based lookups in the kernel
natives, the effect machinery, the `Partial` primitives, the JS generator
(boundary codecs, text natives, `ifThenElse`), the pretty printer and the
driver's runner (§1.3, §7.3). This is the prerequisite step of §9: without
it, a user's own `List` with different constructors would be **encoded as a
JS array** at the boundary (`crates/js/src/lib.rs:193`), which is wrong.

**The registry's invariants:**

1. **Each entry is a finalised declaration of the current kernel
   environment** (`State::Final`). The registry lives inside that
   environment (`Globals`), so raw ids are never carried from one
   independently loaded environment to another.
2. **User name resolution can't change it.** Nothing a user file declares,
   imports or hides writes to it. It's written only while the library
   loads.
3. **A missing entry never falls back to user scope.** If `+` is used where
   `Std.Nat.add` isn't bound (only possible while the library itself
   loads), it's an error naming the built-in, not a search for `add`.
4. **Entries are bound as their declarations finish loading** (when the
   kernel makes them final), so library code later in load order can use
   the syntax.
5. **Completeness is checked before any user code.** After the library
   loads, every entry must be bound; otherwise loading fails with the list
   of missing entries.

**Binding syntax and replacing a definition are separate operations.**
Compiling `+` to the checked `Std.Nat.add` is an ordinary elaboration
choice, and needs only invariant 1. *Replacing* a definition with a native
implementation also assumes that the implementation computes what the
definition does. A same-typed `Std.Nat.add` could compute something else, so
"the registry's entry, with the expected type" isn't the whole condition for
a native. The existing validation stays as it is: each native's exact type
shape (`register_native`), and the content hash of the declarations that
compact text and the JS text natives were written for (§7.3). The registry
says *which* declaration is meant; the hash check says whether the native
may stand for it.

**Ordinary names stay shadowable.** Once a file can define its own `add`,
writing `add` means the file's and writing `+` means `Std.Nat.add`. That's
intended: syntax isn't a name.

**When `Int` arrives** (next in `TODO.md`), `+` will need to work on two
types. One route that fits namespaces: `a + b` means `T.add a b`, where `T`
is the head of `a`'s type, exactly as dot notation finds `T` (§4.8). That's
how `++` already behaves for two types. It's a later decision (§8, R6), not
part of this proposal.

### 4.8 Dot notation

**The rule.** For `e.f`, where `e.f` isn't a qualified name (§4.4: `e`'s
first component isn't a namespace that contains `f`):

1. **Infer `e`'s type `A`.**
2. **Find `A`'s namespace**, through the **type-head view** below. Each
   step gives a head; the first head whose namespace has an `f` is used:
   - **`D args`**, a data type (a record, ability or ordinary type):
     namespace `D`. If `D` is a record with a field `f`, the field
     projection is `D.f` (records stage 1). Otherwise look for a
     declaration `D.f`.
   - **A folded definition `d args`**, such as a nickname
     `Price = Nat`, or `Not p`: try namespace `d` first. If `d.f` doesn't
     exist, unfold `d` one step and go back to 2. This is Lean's loop [L5].
   - **`x = y`**, the built-in equality: namespace `Eq`. So `p.sym` and
     `p.trans q` work, as `Eq.symm` does in Lean.
   - **An unsolved metavariable**: `E-CANNOT-INFER`. Nothing is guessed
     (§4.8.2).
   - **Anything else**: a function type, a universe, or a type variable
     `a`. That's `E-NO-NAMESPACE`: "`f` is a function, which has no
     namespace". Lean uses a `Function` namespace for functions [L4]; that
     could be added later.
3. **Find the receiver's place.** In `T.f`'s signature, it's the **first
   explicit parameter whose declared type has head `T`**, read through the
   same view, starting from the signature as written. If there's no such
   parameter, the error is `E-DOT-NO-RECEIVER`, and **lookup stops**: it
   doesn't go on to unfold `T` and try another namespace. Finding `T.f` is
   the decision; a wrong `T.f` is an error to fix, not a reason to look
   elsewhere. (Lean also unfolds parameter types when finding the receiver
   [L5]; this rule reads them through the view instead, which is the same
   thing for parameters written with the type's own name and a
   simplification otherwise.)

**The type-head view** is a deterministic function of the receiver's
*elaborated type term*, not of whatever `Value` evaluation happened to
produce. The draft-1.1 question of whether inferred types are still folded
is settled by rule, so that an alias's namespace is found reliably, and so
that no cache or evaluator optimisation that unfolds a definition earlier
can change which namespace is used:

- It starts from the type as elaborated (the term the receiver was checked
  or inferred at), with solved metavariables substituted. Annotations,
  locations and β-redexes are removed; definitions are **not** unfolded.
  For a variable, that's its binder's type as written; for an application
  `f a`, it's `f`'s result type as written, instantiated.
- Each further step unfolds the **outermost** definition head once, by
  its equations (or case tree), and removes β-redexes again.
- **It stops and reports when unfolding is blocked.** `Family n` with
  `Family : Nat -> Type` defined by matching, and `n` unknown, can't unfold:
  after trying `Family.f`, the result is `E-NO-NAMESPACE` ("`x : Family n`
  has no `f`; `Family n` can't be unfolded further while `n` is unknown").
  The view never retries the same head, and every step is charged to the
  ordinary resource budget, so a deep tower of aliases ends in the usual
  resource error rather than hanging.
- A stuck application `d args` counts as having `d`'s namespace (R2).

Two definitionally equal types may offer different lookups: with
`Price = Nat`, `p : Price` tries `Price.show` and then `Nat.show`, while
`n : Nat` tries only `Nat.show`. That's intended, and it depends only on
the types as written.
4. **Build the call.** `e.f a₁ … aₙ` is `T.f` with `e` in the receiver's
   place and `a₁ … aₙ` filling the other explicit parameters in order.
   Implicit and `auto` arguments are inserted as usual.
   - With fewer arguments, the result is a function of the missing ones:
     `t.split` is `\s -> Text.split s t`, with `t` evaluated once. This is
     allowed only when no missing parameter is one the receiver's parameter
     type depends on (§4.8.2).

This keeps the library's natural argument orders. `Text.split : Char -> Text
-> List Text` stays as it is (so `map (Text.split ',') lines` works), and
`line.split ','` works too, because the receiver is found by type, not by
position.

```
-- with t : Text, xs : List Nat, p : Person, n : Nat
t.length              -- Text.length t
xs.length             -- List.length xs
line.split ','        -- Text.split ',' line
xs.map (\x => x * 2)  -- List.map (\x -> x * 2) xs
n.toText              -- Nat.toText n
p.name                -- the field (Person.name p)
p.name.length         -- Text.length (Person.name p)
(appendLength xs ys).sym   -- Eq.sym (appendLength xs ys)
```

#### 4.8.1 Records

Field access is the special case where `D.f` is a generated projection. One
lookup does both:

- `p.name` finds `Person.name` whether it's a field or a function the user
  added to `Person`.
- The two can't both exist (`E-DUPLICATE`).
- The records lane's `E-UNKNOWN-FIELD` becomes "`Person` has no field or
  function `nmae`". It lists the fields and suggests near misses among the
  namespace's functions.
- `E-NOT-A-RECORD` becomes `E-NO-NAMESPACE`, or `E-UNKNOWN-FIELD` for a
  data type that has a namespace but no `f`.

With namespaces, records' projections become **writable**: `Person.name` is
an ordinary function (`map Person.name people`). That's a change from
records.md §6.2, which says they "can't be written in source", and the two
lanes need to agree on it. Record *update* (`{ p | age = … }`) and record
patterns still refer only to fields.

#### 4.8.2 Inference: the caveat

**Dot notation needs the receiver's type before it can do anything.**

- `\p -> p.name` with nothing saying what `p` is gives `E-CANNOT-INFER`,
  suggesting `\(p : Person) -> p.name`. That's the records lane's behaviour,
  and Lean's when postponing doesn't help [L5].
- Lean and Idris *postpone* such an expression and retry once more is known
  [L5, I3]. Stitchwort's elaborator has no postponement except for `auto`
  obligations at the end of a declaration, so this proposal doesn't add
  one (R3).

**The receiver is elaborated first, out of the written order of `T.f`'s
parameters.** It has to be, since its type picks `T`. For a **complete
call** (every explicit parameter supplied):

1. Make a scoped placeholder (metavariable) for each parameter before the
   receiver's, in order, each in the context of the ones before it.
2. Unify the receiver's type with the receiver parameter's type, with the
   placeholders substituted.
3. Check each written argument against its parameter type, in parameter
   order, which solves or confirms the placeholders.

This is compatible with dependent parameter types. The test that shows it
uses a receiver whose type depends on an *earlier explicit* argument:

```
type Sized (n : Nat) = { value : Nat }

Sized.read : (n : Nat) -> Sized n -> Nat
Sized.read n s = s.value

-- with s : Sized 3
s.read 3   -- checks: the placeholder for n is 3 from s's type, and 3 agrees
s.read 4   -- E-MISMATCH: 4 isn't 3
```

**Missing arguments that the receiver depends on are refused.** `s.read`
alone can't become `\n -> Sized.read n s`: the captured `s` has type
`Sized 3`, not `Sized n` for every `n`. Rather than silently taking `n = 3`
(and pretending the argument was given) or making a lambda that ignores its
argument, that's an error:

```
error[E-DOT-PARTIAL]: `s.read` leaves out `n`, which the type of `s` depends on
   = note: give it, `s.read 3`, or write the call, `Sized.read 3 s`
```

A missing argument that the receiver's type doesn't mention (`t.split`) is
fine. Its type is then also allowed to depend on the receiver.

This makes dot notation infer *better* than the plain call:

```
def names := List.map (\p => p.name) people   -- E-CANNOT-INFER: the lambda is checked first,
                                         -- when `p`'s type is still unknown
def names := people.map (\p => p.name)        -- fine: `people : List Person` is elaborated
                                         -- first, so `p : Person` is known
```

**Evaluation order is not elaboration order.** In effectful code:

1. the receiver runs, **once**;
2. then the written arguments run, left to right as written;
3. then their values are arranged in `T.f`'s parameter order for the call.

So `line.split sep`, with both effectful, runs `line` and then `sep`, even
though the call is `Text.split sep line`. A plain rewrite to
`Text.split sep line` would run them in the opposite order, so the
elaborator binds each effectful argument to a fresh variable first, as the
records lane does for fields, which run in source order ([records.md
§6.1](records.md#61-surface)).

#### 4.8.3 Chains and qualified names

`a.b.c` is parsed as `(a.b).c`. It's resolved like Lean's dotted
identifiers [L3]:

- **If `a` is a local variable**, everything after it is dot notation.
- **Otherwise**, take the **longest** prefix `a.b…` that names a
  declaration, with `a` resolved by §4.4. That prefix is the head, and the
  rest is dot notation on it.
  - `List.map` is a qualified name.
  - `xs.map` is dot notation (since `xs` is a local).
  - `Origin.x`, with `Origin : Point` defined and no `Origin.x` declared,
    is dot notation on the definition `Origin`.
  - `List.length.foo` is dot notation on the function `List.length`, which
    is `E-NO-NAMESPACE`.

### 4.9 Constructors and patterns

- **In patterns**, a constructor may be written by its short name if visible
  (`Cons x xs`) or qualified (`List.Cons x xs`, `Shape.Square s`). A pattern
  is still a constructor if its *last* component starts with an uppercase
  letter, so `List.Cons` is a constructor pattern and `x` is a variable.
- **Short names follow §4.4.** The file's own `type Answer = | Yes | No`
  makes `Yes` mean `Answer.Yes` in that file, hiding `Decidable`'s `Yes`.
  Patterns on a `Decidable` then need `Decidable.Yes h`.
- **Not proposed: choosing a constructor by the type being matched**, as
  Agda does for overloaded constructors (secondary sources only, see
  [What I couldn't verify](#what-i-couldnt-verify)). Nor a leading dot,
  `.Yes h`, which Lean resolves against the expected type [L3]. Both turn
  some of today's errors into working programs, so either can be added later
  (§8).
- **A constructor's place in the tree** is its type's namespace:
  `Std.List.Cons`, `Std.Effect.Comp.Done`. The **kernel** sees only data
  and constructor ids, as now.

### 4.10 Abilities and handlers

```
ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()
```

- **Names.** `State.get` and `State.put` are the operations, and in the
  defining file, `get` and `put` are visible as short names (level 2,
  "operations follow their ability"). Two abilities in one file that both
  have `get` are no longer `E-DUPLICATE`: plain `get` is `E-AMBIGUOUS` at
  each use, and `State.get ()` always works.
- **Rows** (`{State Nat, IO}`) name abilities like any other name, so a
  qualified `{Console.IO}` would work too.
- **Handler clauses** (`| get u => k -> …`) resolve the operation's name the
  same way, and may be qualified (`| State.get u => k -> …`). Today the
  elaborator works out which ability a handler handles from the clause names
  (`crates/elab/src/effects.rs:1300`), and that still works once each name
  is resolved. Resolving clause names against the handled computation's row,
  as records resolve field patterns by type, would be a later convenience.
- **Library abilities.** `IO` and `Partial`
  are in the default set (§4.6, Q2), but `IO`'s operations are not (D29,
  19 October 2026): `IO.print`, `IO.readLine`, `IO.readAll`. `simulate` becomes `IO.simulate`.

### 4.11 Type variables

The rule "a name in the module takes priority over a type variable", with
`W-MODULE-NAME` ([syntax.md](../syntax.md#declaration-order)), extends to
every level of §4.4:

- A lowercase name in a type position is bound automatically as a type
  variable only if it resolves to nothing.
- If it resolves to a name from levels 2–4, it means that name.
- `W-MODULE-NAME` warns when the name came from the file (as now) **or from
  an import**.

The default set is almost all uppercase, so in practice this frees more
lowercase names for type variables than today, when `length`, `not`, `add`
and the rest of the prelude are all visible.

### 4.12 Errors

The codes are new except `E-DUPLICATE`, `E-UNKNOWN-NAME`, `E-CANNOT-INFER`
and `E-UNKNOWN-FIELD` (records lane). Each example shows the shape of the
message; the exact wording is for implementation.

**An ambiguous name, reported where it's used:**

```
import List (length)
import Text (length)

def count (xs : List Nat) : Nat := length xs
```
```
error[E-AMBIGUOUS]: `length` could mean `List.length` or `Text.length`
  --> main.sw:5:12
   |
 1 | import List (length)
   |              ------ `List.length` imported here
 2 | import Text (length)
   |              ------ `Text.length` imported here
 5 | count xs = length xs
   |            ^^^^^^ write `List.length` or `Text.length`, or use dot notation: `xs.length`
```

**A name that isn't visible, though the library has it:**

```
error[E-UNKNOWN-NAME]: there's no `split` here
   |
 4 | parts = split ',' line
   |         ^^^^^ `Text.split` exists: write `Text.split`, `line.split ','`, or `import Text (split)`
```

**Importing something that isn't there:**

```
error[E-IMPORT-UNKNOWN]: `List` has no `sortt`
   |
 1 | import List (sortt)
   |              ^^^^^ did you mean `sort`?
```

**An import clashing with the file's own declaration:**

```
error[E-IMPORT-CLASH]: `map` is imported, but this file also defines `map`
   |
 1 | import List (map)
   |              ^^^ imported here
 9 | map : (Nat -> Nat) -> Tree -> Tree
   | --- defined here, which would hide the import
   = note: remove the import, and write `List.map` or `xs.map` where you mean the list one
```

**Dot notation on an unknown type:**

```
error[E-CANNOT-INFER]: can't tell what `p` is, so can't look up `.name`
   |
 3 | def names := List.map (\p => p.name) people
   |                              ^^^^^^ `p`'s type isn't known yet here
   = note: annotate it, `\(p : Person) -> p.name`, or write `people.map (\p -> p.name)`
```

**No such field or function:**

```
error[E-UNKNOWN-FIELD]: `Text` has no field or function `size`
   |
 6 | n = t.size
   |      ^^^^^ did you mean `length`?
```

**A function with no parameter for the receiver:**

```
error[E-DOT-NO-RECEIVER]: `Nat.fromDigits` has no parameter of type `Nat` to put `n` in
   |
 7 | m = n.fromDigits
   |     ^^^^^^^^^^^^ `Nat.fromDigits : List Char -> Maybe Nat`
   = note: call it directly, `Nat.fromDigits cs`
```

**Adding to a library namespace** (refused on the resolved owner, so the
same for `Std.List.sum`):

```
error[E-STD-NAMESPACE]: `List` is the standard library's, which a program can't add to
   |
 3 | List.sum : List Nat -> Nat
   | ^^^^^^^^ `List` here means `Std.List`
   = note: define it in your own namespace, for example `sum` or `Lists.sum`
```

**A receiver whose type depends on a missing argument:**

```
error[E-DOT-PARTIAL]: `s.read` leaves out `n`, which the type of `s` depends on
   |
 9 | f = s.read
   |     ^^^^^^ `Sized.read : (n : Nat) -> Sized n -> Nat`
   = note: give it, `s.read 3`, or write the call, `Sized.read 3 s`
```

Messages print names **as the file would write them**: the shortest form
that means the same thing there. That's `List Nat` and not
`Std.List Nat`, unless the file has its own `List`.

### 4.13 Grammar sketch

```
module      ::= import* decl*
import      ::= "import" nspath "(" item ("," item)* ")"     -- column 0, before any decl
nspath      ::= Upper ("." Upper)*
item        ::= lower | Upper

declname    ::= (Upper ".")* (lower | Upper)        -- signatures, equations, `type`, `ability`
                                                    -- (namespace components are uppercase)
atom        ::= … | name ("." (lower | Upper))*     -- no space on either side of "."
pattern     ::= … | (Upper ".")* Upper pattern*     -- a constructor, possibly qualified
```

**New keyword:** `import`. **Reserved name:** `Std`.

**Namespace components start with an uppercase letter.** This is a
convention made into a rule, so that `p.name` (lowercase first: a value) and
`List.length` (uppercase first: probably a namespace) read differently, as
in Idris [I2]. It isn't load-bearing for resolution, which still uses §4.8.3,
because uppercase definitions exist (`Not`, `IsZero`).

**Lexing.** The records lane's `.` token already requires no spaces around
it. The parser must also accept an uppercase name after it (`List.Cons`,
`Std.List`), and dotted names at the start of a declaration and of an
equation.

## 5. Whole-module scope and the dependency pre-pass

Today the pre-pass finds each declaration's dependencies from its free names
before anything is type-checked (§1.2). Each new construct is handled
differently:

**Collection and registration are separate passes.** A declaration's full
name can depend on the imports (`Shape.area` means `Geometry.Shape.area`
only if `Shape` resolves there), and imports are resolved against the
file's declarations. So step 1 of §1.2 splits in three:

1. **Raw collection.** Every declaration is entered under its name *as
   written* (`Shape.area`), and every type's and ability's constructors and
   operations under the type's written name. Nothing is resolved yet. The
   only names whose meaning is fixed here are top-level single-component
   names, which need no resolution.
2. **Imports** are resolved, against the library and the raw top-level
   names.
3. **Full-name registration.** Each written qualifier is resolved by §4.4
   (which now has all four levels), giving the declaration's full name.
   Duplicates, `E-STD-NAMESPACE` and `E-IMPORT-CLASH` are reported here.

A qualifier can refer to a namespace another declaration creates
(`Geometry.Shape.area` before `type Geometry.Shape`), so registration
resolves qualifiers against the namespaces collected in pass 1, never
against the results of pass 3 itself.

**Qualified names are exact.** After registration, `Geometry.area` and
`Shape.area` resolve syntactically: the qualifier is resolved by §4.4 and
the rest is looked up. So the pre-pass adds a **certain** edge to exactly
that declaration.

**Dot notation can't be exact.** In `s.label`, the target is `T.label`,
where `T` is `s`'s type. That isn't known until elaboration, which is after
the components have been fixed. The proposal is to **over-approximate**:

- `e.f` adds a **speculative** edge to **every declaration of this file
  whose full name ends in `.f`**, and to every record of this file with a
  field `f`.
- Library declarations are already checked, so they need no edges.
- **Every edge records why it exists**: *certain* (a name or qualified name
  that resolves to that declaration) or *speculative* (a dot-notation
  candidate, with the `e.f` that caused it). Diagnostics about components
  use the reasons (below).

**What over-approximation costs.** It can merge declarations that don't
really depend on each other into one component:

```
type Shape = { name : Text }
type Tile  = { shape : Shape }

def Shape.label (s : Shape) : Text := s.name

def Tile.label (t : Tile) : Text := t.shape.describe

def Shape.describe (s : Shape) : Text := s.label         -- means Shape.label, but `.label` also
                                   -- adds an edge to Tile.label
```

Here `Tile.label` → `Shape.describe` is a real dependency, while
`Shape.describe` → `Tile.label` is spurious. Together they form a cycle, so
the two are checked as one group. The termination check is unaffected,
since it looks at the elaborated bodies, which contain only real calls.
What the user can notice:

- **Full application.** Inside the group, each member must be given all its
  arguments wherever it's used.
- **`auto`.** It can't use the group's members.
- **`E-MUTUAL-SIGNATURE`.** It's reported from the pre-pass's edges, so a
  signature that uses dot notation could be refused because of an edge that
  isn't real.

**The cost is larger than that example suggests:** a speculative edge can
create a false **mixed-kind** cycle, a data type and a function checked as
one group, which the user would read as an attempted
induction-recursion. The reviewer's example:

```
type A = { value : Nat }

def make (n : Nat) : A := { value = n }

def measure (n : Nat) : Nat := (make n).value

type B = { value : Nat, ok : measure 0 = 0 }
```

Really, `measure` can be checked before `B`. But `(make n).value` draws a
speculative edge `measure → B` (since `B` has a field `value`), and `B`'s
proof field draws a certain edge `B → measure`. That's a cycle of a type and
a function. Narrowing by a parameter's type (mitigation 2) doesn't cover
`(make n).value`, since the receiver isn't a parameter.

**Mitigations, simplest first:**

1. **Explain it.** When a component exists only because of speculative
   edges, the "checked together because …" note says so, and names the
   edge: "`(make n).value` might mean `B.value`, so `measure` and `B` are
   checked together; write `A.value (make n)` to say which." For a
   mixed-kind component the error says the dependency is artificial and
   that the program isn't defining a type and a function together.
   **This example is a stage-2 test**, asserting the diagnostic.
2. **Narrow it wherever a reliable syntactic type head exists.** When the
   receiver is a parameter or `let` whose declared type has a known head
   (`s : Shape`), or an application of a known function whose declared
   result type has a known head (`make n`, with `make : Nat -> A`), resolve
   `e.f` exactly in the pre-pass and make the edge certain. This stays
   syntactic: no unification, no unfolding, no implicit arguments. Anything
   more is left speculative rather than growing a second type checker inside
   the pre-pass.
3. **Report `E-MUTUAL-SIGNATURE` only for references the elaborated
   signature really contains.** This is a better error message, never a
   permission: a signature still may not mention a pending sibling, because
   the kernel's admission rule is unchanged (it refuses a group that refers
   to an unfinished declaration outside it, R1), and so is the
   elaborator's rule against a signature using a member of its own group. When the
   approximation has grouped declarations that really need checking one
   after another, the choices are to narrow the edge (2) or to reject with
   the qualified-form hint (1). The approximation can't make the kernel
   admit anything it wouldn't otherwise.

The qualified form is always exact, so a user who hits this has a one-line
way out. Forming components lazily (R1) isn't needed for the first
implementation; the approximation is a documented initial limitation.

## 6. Moving the prelude into namespaces

Every current prelude name, and where it goes. Names marked **default** are
at `Std`'s root (§4.6). Everything else is reached by dot notation, its
qualified name, or `import`.

**The guiding rules:**

- A function goes into the namespace of the type it's mainly *about*: its
  receiver, so dot notation reads naturally.
- Prefixes that only existed to avoid clashes are dropped.
- The new names are suggestions, and can be edited freely before
  implementation.
- Keywords can't be namespace members, so `maybeThen` becomes `andThen`
  (Elm's name for it) rather than `then`.

**Logic**

| Today | New full name | Notes |
|---|---|---|
| `Void` | `Void` | **default** |
| `Unit`, `Trivial` | `Unit`, `Unit.Trivial` | **default** (both) |
| `Not` | `Not` | **default** |
| `absurd` | `Void.absurd` | `v.absurd` |
| `exfalso` | `Void.exfalso` | |
| `cong`, `sym`, `trans` | `Eq.cong`, `Eq.sym`, `Eq.trans` | `p.sym`, `p.trans q`, `p.cong f` (receiver found by type, §4.8) |

**Numbers**

| Today | New full name | Notes |
|---|---|---|
| `Nat`, `Zero`, `Succ` | `Nat`, `Nat.Zero`, `Nat.Succ` | **default** |
| `add`, `sub`, `mul` | `Nat.add`, `Nat.sub`, `Nat.mul` | behind `+ - *`; natives (§7.3) |
| `pred` | `Nat.pred` | |
| `leq` | `Nat.leq` | native |
| `LessEq`, `LessThan` | `Nat.LessEq`, `Nat.LessThan` | behind `<=`, `<` |
| `eqNat` | `Nat.equal` | native |
| `eqNatRefl`, `eqNatSound` | `Nat.equalRefl`, `Nat.equalSound` | natives |
| `natNeq` | `Nat.equalFalse` | registered specially (`lib.rs:1050`) |
| `IsZero`, `zeroNotSucc`, `succNotZero`, `succInjective` | `Nat.IsZero`, `Nat.zeroNotSucc`, `Nat.succNotZero`, `Nat.succInjective` | |
| `divFuel`, `div`, `mod` | `Nat.divFuel`, `Nat.div`, `Nat.mod` | behind `/`, `%`; `divFuel` native |
| `compareNat` | `Nat.compare` | `m.compare n` |
| `decEqNat`, `decEqNatFrom`, `decSucc` | `Nat.decEq`, `Nat.decEqFrom`, `Nat.decSucc` | `decEq` native; found by `auto` by type (§7.1) |
| `decLessEq`, `decLessThan` | `Nat.decLessEq`, `Nat.decLessThan` | |
| `natToText`, `natDigits`, `digitChar` | `Nat.toText`, `Nat.digits`, `Nat.digitChar` | `n.toText` |

**Booleans and decisions**

| Today | New full name | Notes |
|---|---|---|
| `Bool`, `False`, `True` | `Bool`, `Bool.False`, `Bool.True` | **default** |
| `not` | `Bool.not` | `b.not`; **default** through the alias `not` (Q1, §4.6) |
| `ifThenElse` | `Bool.ifThenElse` | behind `if` |
| `IsFalse`, `falseNotTrue`, `trueNotFalse` | `Bool.IsFalse`, `Bool.falseNotTrue`, `Bool.trueNotFalse` | |
| `decTrue`, `decEqBool` | `Bool.decTrue`, `Bool.decEq` | |
| `canon`, `canonConst`, `symThenSelf`, `fromCanon`, `uniqueBoolEq` | `Bool.canon`, `Bool.canonConst`, `Bool.symThenSelf`, `Bool.fromCanon`, `Bool.uniqueEq` | Hedberg's argument |
| `Decidable`, `Yes`, `No` | `Decidable`, `Decidable.Yes`, `Decidable.No` | **default** |
| `IsYes`, `fromYes` | `Decidable.IsYes`, `Decidable.fromYes` | `fromYes` used by `auto` |
| `toBool` | `Decidable.toBool` | behind `==` |
| `elimDec` | `Decidable.elim` | behind `if h :` |
| `decNot` | `Decidable.not` | `d.not` |

**Lists, `Maybe`, `Pair`, `Ordering`**

| Today | New full name | Notes |
|---|---|---|
| `List`, `Nil`, `Cons` | `List`, `List.Nil`, `List.Cons` | **default** |
| `length`, `append`, `reverseOnto` | `List.length`, `List.append`, `List.reverseOnto` | `append` behind `++` |
| `lengthAppend` | `List.lengthAppend` | |
| `IsNil`, `nilNotCons`, `consNotNil` | `List.IsNil`, `List.nilNotCons`, `List.consNotNil` | |
| `headOr`, `tailOf` | `List.headOr`, `List.tailOf` | `Cons`'s fields are called `head` and `tail`, but they aren't projections (only records have those), so the names don't collide; still, avoid them for clarity |
| `decCons`, `decEqList` | `List.decCons`, `List.decEq` | |
| `Maybe`, `Nothing`, `Just` | `Maybe`, `Maybe.Nothing`, `Maybe.Just` | **default** |
| `maybeThen` | `Maybe.andThen` | `then` is a keyword |
| `Pair`, `MkPair` | `Pair`, `Pair.MkPair` | **default** |
| `fst`, `snd` | `Pair.fst`, `Pair.snd` | `p.fst` reads like a record field |
| `Ordering`, `Less`, `Equal`, `Greater` | `Ordering`, `Ordering.Less`, … | **default** |
| `thenCompare`, `isLess` | `Ordering.andThen`, `Ordering.isLess` | |

**Characters and text**

| Today | New full name | Notes |
|---|---|---|
| `Char`, `MkChar` | `Char`, `Char.MkChar` | **default** |
| `isScalar` | `Char.isScalar` | |
| `charToNat`, `charFromNat` | `Char.toNat`, `Char.fromNat` | `c.toNat`; `Char.fromNat n` (receiver is a `Nat`, so not `n.…`) |
| `mkCharExt`, `charExt`, `decCharFrom`, `decEqChar` | `Char.mkExt`, `Char.ext`, `Char.decEqFrom`, `Char.decEq` | |
| `isSpaceCode`, `isSpace`, `digitValue` | `Char.isSpaceCode`, `Char.isSpace`, `Char.digitValue` | |
| `Text`, `MkText` | `Text`, `Text.MkText` | **default** |
| `textToList`, `textFromList`, `textToFromList`, `textFromToList` | `Text.toList`, `Text.fromList`, `Text.toFromList`, `Text.fromToList` | JS natives (§7.3) |
| `textAppend`, `textLength`, `textLengthAppend`, `textIsEmpty` | `Text.append`, `Text.length`, `Text.lengthAppend`, `Text.isEmpty` | `append` behind `++` |
| `decTextFrom`, `decEqText` | `Text.decEqFrom`, `Text.decEq` | |
| `textUncons`, `textFold`, `foldChars` | `Text.uncons`, `Text.fold`, `Text.foldChars` | |
| `compareChars`, `textCompare`, `textLess` | `Text.compareChars`, `Text.compare`, `Text.less` | |
| `dropSpaces`, `textTrim` | `Text.dropSpaces`, `Text.trim` | |
| `readDigits`, `textToNat` | `Text.readDigits`, `Text.toNat` | `s.toNat` |
| `splitCons`, `splitChars`, `joinChars`, `joinPair`, `joinCons`, `joinSplitCons`, `joinSplitChars`, `textsOf`, `charListsOf`, `charListsOfTexts`, `splitTexts`, `joinSplitTexts` | `Text.` + the same name | helpers and lemmas |
| `textSplit`, `textJoin`, `textJoinSplit` | `Text.split`, `Text.join`, `Text.joinSplit` | `line.split ','`; `Text.join ',' parts` |

**Abilities and their machinery**

| Today | New full name | Notes |
|---|---|---|
| `IO`, `print`, `readLine` | `IO`, `IO.print`, `IO.readLine` | `IO` **default** (Q2); the operations are not (D29) |
| `nextLine`, `simulate` | `IO.nextLine`, `IO.simulate` | |
| `Comp`, `Done`, `Call`, `foldComp`, `bind` | `Effect.Comp`, `Effect.Comp.Done`, `Effect.Comp.Call`, `Effect.foldComp`, `Effect.bind` | frees `Done`, `Call` for users |
| `Plus`, `L`, `R`, `PlusRes` | `Effect.Plus`, `Effect.Plus.L`, `Effect.Plus.R`, `Effect.PlusRes` | frees `L`, `R` |
| `SigMap`, `MkSigMap`, `sigInject`, `sigReply`, `translate`, `sigId`, `sigCompose`, `sigLeft`, `sigRight`, `swapOp`, `swapReply`, `sigSwap` | `Effect.` + the same name | |
| `NoOp`, `NoRes`, `Sig`, `MkSig`, `sigOp`, `sigRes` | `Effect.` + the same name | the printer matches `sigOp` by name (`pretty.rs:90`) |
| `caseInject`, `caseReply`, `sigCase`, `noInject`, `noReply`, `sigFromNo`, `handlePlus`, `runPure` | `Effect.` + the same name | |
| `UnitType`, `UnitValue` | `Builtin.UnitType`, `Builtin.UnitValue` | written `()` in source |

**Names added by lanes in flight** follow the same rules:

- The `Partial` lane's `Delay`, `now`, `lift`, `bindD`, `mapSig`, `pfix`,
  `Rec` and `RecRes` go into `Effect` (or a `Partial` namespace if `Partial`
  is an ability with one). They're kernel primitives, admitted with exact
  type checks, so they're registry entries like the natives.
- The records lane's projections are already `Person.name`; its constructor
  becomes `Person.%mk` (§4.2).

**What else changes with it.**

- **Examples and tests.** Every example, test and snapshot that uses a
  prelude function is rewritten. That's mechanical, and dot notation keeps
  it short. In `examples/` alone: `length` about 95 times, `not` 51,
  `simulate` 42, `append` 41, `natToText` 28, `textToNat` 20, the other
  `text…` names about 60 in total.
- **`examples/reject/duplicate-definition.sw`** stops being an error. It
  becomes an *accept* example: a file defining its own `length`.
- **The playground's examples** (`web/index.html`) and the JS snapshots are
  updated too.

## 7. Effects on the rest of the system

### 7.1 `auto`

**No change.** `auto` keeps searching every checked definition whose result
is `Decidable …` (§1.5), wherever it lives and whether or not it's imported.
That keeps one simple rule: **imports decide which names you can write;
they never change which proofs are found.** Lean's instances work the same
way unless declared `scoped` [L1]. A `scoped` variant could be added later
if a library ever needs one.

`E-AUTO-NONE` and the other messages print procedures by the names of
§4.12, such as `Nat.decEq`.

One thing to watch, though it's not caused by namespaces: the search is a
scan over all definitions per obligation (`auto.rs:170`). The next
milestone grows the library a lot, so the cost of `auto` will grow with it.
Not measured (**unverified**).

### 7.2 Abilities

See §4.10. The generated names move out of the user's namespace
(`State.%elim`). Ability order in rows is by (module, source position)
([mutual-recursion.md §10.2](mutual-recursion.md#102-as-built-milestone-2-function-groups-and-forward-references)),
which namespaces don't affect.

### 7.3 Built-ins, natives and the JS generator

**Natives.**

- The kernel's natives (`add`, `eqNat`, …) and `Nat`/`Bool` are registered
  by name while the prelude loads (`lib.rs:868-869`, `1048`). They go
  through the registry of §4.7: the registry says which declaration is
  meant, and the existing registration checks (each declaration's exact
  type shape, `register_native`; content hashes for compact text) still
  decide whether the native may replace it. Nothing about those checks is
  weakened.
- The kernel's `find_data("Void")` (`native.rs:194`, `329`) takes the
  `Void` id from the same registry.

**The JS generator.**

- **Boundary codecs** (`lib.rs:188-197`), **text natives** (`lib.rs:1761`)
  and **`ifThenElse`** (`lib.rs:983`) must use identities from the
  registry, not names. The comment "Prelude names can't be redefined" stops
  being true the day §4.4 lands. The text natives keep their content-hash
  check: the registry picks the declaration, and the hash says whether the
  JS implementation was written for it.
- **Export names.** An export's JS name is its **short** name: an export
  `Geometry.area` is imported in JS as `area`.
  - Two exports in one file with the same short name are `E-EXPORT`: "both
    would be exported as `area`".
  - The existing checks (a JS identifier, not reserved, not one of the
    module's own exports) apply to the short name.
  - Nested JS objects (`export const Geometry = { area }`) would also work,
    but they're harder to type in TypeScript and to tree-shake; not
    proposed.
- **`.d.ts` type names** are short too (`Shape`, not `Geometry$Shape`), with
  `E-EXPORT` if two **different** boundary types in one export set share a
  short name. The comparison is by identity: the same type reached twice
  (two exports both taking a `Shape`) is not a collision, and there's a
  test for each case. The library's types keep their current names
  (`Maybe`, `Pair`), so existing `.d.ts` output doesn't change.
- **Internal JS names must be injective.**
  - `def_name` writes a prime as `$` and a dot as `$$` (`lib.rs:1924-1928`).
  - Primes may appear *inside* names: the lexer accepts `'` after the first
    character (`crates/syntax/src/lexer.rs:122`).
  - So `a''b` and `a.b` both become `$a$$b`.
  - Today dots occur only in generated names, so a clash needs a user
    definition such as `State''elim` next to an ability `State`
    (`State.elim`). Whether that's reachable in generated JS is
    **untested**.
  - With namespaces, user-chosen dots make it easy to reach.
  - **Proposed fix:** escape each character with `$` followed by a code
    letter, for example `'` as `$p`, `.` as `$d` and `%` as `$g`. Source
    names never contain `$`, and every `$` is followed by exactly one code
    letter, so decoding is unique.
  - Only internal names change. Field keys and `.d.ts` names keep their
    current scheme, which has no dots.
  - The encoding is applied to **full logical names** (`Std.List.length`,
    not `length`), so two declarations with one short name stay apart.
- **Two further properties are tested, not just argued** (from the review):
  - **Disjointness across the whole generator.** An injective encoding of
    source names doesn't by itself keep them apart from the generator's
    *other* names: runtime helpers, generated locals, constructor helpers
    and codec names. A test generates code for definitions whose names
    collide with each of those schemes as closely as the source grammar
    allows, and checks that every top-level JS binding is distinct.
  - **Validity as a JS identifier.** Escaping `.`, `'` and `%` covers only
    part of it. Every character the lexer accepts in a name must be valid at
    its position in a JS identifier, or get an escape of its own. A test
    enumerates the lexer's accepted name characters and checks each encoded
    name against ECMAScript's identifier grammar.

**The pretty printer** prints literals and `()` by type name
(`pretty.rs:275`). It should use identities too, or a user's own `List`
type would print as a list literal. It also needs the short-name display
rule of §4.12.

**The driver's runner** looks up `UnitType` and `Maybe` by name
(`crates/driver/src/run.rs:278-279`). That moves to the table too.

### 7.4 Hashing

- **Definitions: no change.** Their names aren't hashed (§1.6). Moving
  `textLength` to `Text.length` changes no definition's hash, so no cached
  test or kernel result is invalidated by the renames themselves.
- **Data types: hash the full logical nominal path**, which brings the
  code in line with DESIGN §11 ("a nominal type's hash includes its logical
  module name and its own name"). That means `Std.List` for the library's
  `List`, and for the user's file, the file's root name followed by the
  type's **whole** namespace path, such as `Main.Shape` or
  `Main.Geometry.Shape`, where `Main` stands for "the program's file" until
  files have logical names (§8).
  - Every intermediate namespace is included (R5): hashing only the module
    and the last component would merge two same-shaped types
    `Main.Geometry.Shape` and `Main.UI.Shape`.
  - Physical paths, checkout directories and session-local ids never enter
    it. A file's logical name is what's hashed, not where it's stored.
  - **Why now:** once a file can hide a library type (§4.4), a user's own
    `type List (a : Type) = | Nil | Cons (head : a) (tail : List a)` would
    otherwise get the **same hash** as the library's. That breaks DESIGN's
    "nominal types differ", even though both are different kernel types.
  - **Cost:** every data type's hash changes once, and with it every hash
    that mentions one. Caches are invalidated once, and the 14 text-native
    hashes in `crates/js/src/lib.rs` are regenerated (they're checked by
    tests anyway).
  - Constructor and field names stay as they are, short names.
- **Kernel identity is unaffected.** The kernel compares data ids, not
  hashes.

### 7.5 Caching

- **Test results** stay keyed by test hash (`driver.rs:127`), which names
  don't enter. A file whose imports change but whose tests resolve to the
  same definitions keeps its cached results. That's correct: the
  definitions really are the same.
- **Generated JS** is keyed by definition hash, export names and options
  (DESIGN §11). Export names become short names (§7.3).
- **The planned elaboration cache** (DESIGN §11, "Later") keys a declaration
  by its source text and its dependencies' hashes. Two things complicate
  that key:
  - Which declarations a name refers to now depends on the file's imports
    and on everything visible.
  - Dot notation's targets depend on types.
  So the dependencies can't be read off the syntax before elaborating. The
  simple sound option is to record each **lookup query** made during
  elaboration (a short name at a position, `x.f` with its type-head view)
  and to validate the cached entry by **rerunning** those queries, as
  incremental compilers do (R7).
  - Recording only the *target* isn't enough. If `p.show` with
    `p : Price` fell back to `Nat.show` because there was no `Price.show`,
    adding `Price.show` later changes the right answer while `Nat.show` is
    unchanged. A query's validity includes the **absence** of every nearer
    candidate.
  - The same goes for a new import that makes a name ambiguous, and for a
    lowercase name in a type that was a type variable and now names
    something (§4.11).
  There is nothing to do now, since that cache doesn't exist yet.

### 7.6 The CLI

`stitchwort assumptions <name>` and similar commands take full or qualified
names (`Text.split`). `main` and tests are unaffected: `main` is a top-level
name of the file, and tests are labels.

## 8. Extending it later without breaking anything

"Doesn't break anything" means: **a program that's accepted today, with a
given meaning, is accepted later with the same meaning.** The test for each
extension is whether it only turns errors into programs, or only adds names
at a level that can't hide an existing resolution.

| Later feature | Possible syntax | Why it's compatible |
|---|---|---|
| **Other files** | `import Geometry (area)`, where `Geometry` is a file `Geometry.sw` | A file's root is a namespace (§4.2), so `import` works exactly as for a library namespace (D3). A path that resolves to nothing today is `E-IMPORT-UNKNOWN`; later it may also find a file, which only turns an error into a program. A file's types are hashed with its module path in place of `Main` (§7.4), which is DESIGN §11's "logical module name". |
| **Import everything** | `import List (..)` | `(..)` is a syntax error today. Its names would come in below explicit imports, as in Scala's wildcard level [S2] and Rust's globs [R1], so it never hides anything an explicit import or the file declares. |
| **Hiding** | `import List (..) hiding (map)` | Only makes sense with `(..)`. |
| **Renaming** | `import List (map as listMap)` | `as` inside an import list is a syntax error today. |
| **Imports inside a definition or expression** | `import List (map) in e`, or Lean's `open … in` [L1] | `import` in an expression is a syntax error today. Its names would sit between locals and the file's declarations, and only inside `e`. |
| **No default names** | `import Std ()`: Haskell's rule that an explicit import of the Prelude replaces the implicit one [H1 §5.6.1] | `import X ()` is a syntax error today (§4.5). Built-in syntax keeps working, since it's bound by identity (§4.7). |
| **Namespace blocks** | `namespace Geometry` … `end Geometry` | Pure shorthand: a declaration `area` inside is `Geometry.area`. |
| **Own namespace open in a body** | Lean's rule [L1], at lowest priority | Inside `List.sum`, other `List` names usable unqualified, only where they'd otherwise be unknown, so nothing that resolves today changes (Q3). |
| **Choosing among same-level names by type** | Agda, Idris, Unison style [I1, U3] | Turns some `E-AMBIGUOUS` errors into programs. |
| **Constructors by expected type** | `.Square s`, Lean's leading dot [L3] | A leading `.` is a syntax error today. |
| **Functions' namespace** | `f.comp g` via `Function`, Lean [L4] | `E-NO-NAMESPACE` today. |
| **Operators by namespace** | `a + b` as `T.add a b` for `a : T …` | `+` on a non-`Nat` is a type error today; it keeps meaning `Nat.add` on `Nat`. That needs care with literals: `0 + n`, with `n : Int`, must not commit to `Nat` from the literal first (R6). |
| **Adding to library namespaces** | `List.sum` in a user file (Q4) | `E-STD-NAMESPACE` today. |
| **User-written aliases** | `alias len = List.length` | `alias` is not a declaration form today (§4.6 uses it inside the library only). |
| **`private` and `protected`** | Lean's modifiers [L2] | New keywords, and they only remove names from views. Adding one to an *existing* declaration can break its users, but that's the author's choice, as anywhere. |
| **Postponing dot notation** | Lean and Idris [L5, I3] | Turns some `E-CANNOT-INFER` into programs. |

**What could break compatibility, and is avoided above:**

- Letting imports or the file's own names be *hidden* by something added
  later at a higher level.
- Changing what an unqualified name means when a library namespace gains a
  member. Since library functions aren't default-visible (D4), adding
  `List.sum` to the library can't change the meaning of a user's `sum`.
  Elm's argument [E1] applies here.
  - Since user files can't add to library namespaces (§4.3), a library
    addition can't collide with a user's `List.sum` either. If extension is
    allowed later (Q4), that collision becomes possible, as in Lean.
  - Dot notation through an alias is safe too: with `Price = Nat`, a
    library that later adds `Nat.show` changes what `p.show` means only if
    the file has no `Price.show`, in which case `p.show` was an error
    before. A *nearer* namespace gaining a member can change a resolution,
    but the nearer namespaces of a user's type are the user's own.

## 9. Staging

**Stage 0: built-ins by identity** (no visible change).

- The registry of §4.7, with its invariants, filled while the prelude loads
  and checked complete before user code.
- **The audit covers both directions**: code that *builds* a reference to a
  built-in (elaborating `+`, a literal, a handler's translation), and code
  that *recognises* a term or value as one (the printer's `()` and list
  literals, the JS codecs, the runner's `Done`/`Call`, the step function's
  `Comp`). Its consumers:
  - syntax: operators, `==`/`!=`, `++`, `if`/`if h :`, literals, `()`,
    number patterns' `Zero`/`Succ`, and records' generated decision
    procedures (`Yes`, `No`, `cong`, `Decidable`);
  - `auto`'s `fromYes`, `Trivial` and `Yes`, and the test runner's `Bool`;
  - the effect machinery: `Comp`, `Done`, `Call`, `bind`, `foldComp`,
    `Plus`, `NoOp`, `NoRes`, `PlusRes`, `Sig`, `sigOp`, `sigRes`, `SigMap`,
    `translate` and the `sig…` combinators, `handlePlus`, `runPure`, and
    the operations' metadata;
  - the `Partial` lane's primitives and their references to `Comp`,
    `Plus`, `SigMap`, `Rec`, `PlusRes`, `RecRes`, in the kernel, the step
    function and the elaborator;
  - kernel natives, `Nat`, `Bool`, `Decidable`, `Void`, `natNeq`, compact
    text's `List` and `Char`;
  - JS: codecs, text natives, `ifThenElse`, `Decidable`;
  - the printer and the runner (with `simulate`'s `IO`).
- The injective JS name encoding, with its two whole-generator tests
  (§7.3).
- Generated ability names move to `State.%elim`.
- **Tests:**
  - every existing test passes unchanged (snapshots of internal JS names
    are regenerated);
  - the registry is complete after the prelude loads, every entry is final,
    and a prelude missing an entry is refused before user code;
  - **the altered-name-environment test**: load the prelude, then rebind
    the user-facing names of built-ins (`add`, `Nil`, `List`, `Maybe`, …)
    to other declarations (through a test-only hook until stage 1 makes it
    expressible), and check that syntax, natives, codecs, printing and the
    runner still select the original declarations;
  - a user type named like a built-in, through the same hook, isn't given
    the built-in's codec or printing.

The JS encoding and the generated ability names are separable from the
registry, and may be done at the start of stage 1 instead, since they only
matter once users can write dotted names.

**As built** (stage 0): the registry is `crates/core/src/registry.rs`, kept
in `Globals`, with an entry per built-in (data types, constructors,
definitions) bound by `bind_data` and `bind_def` as the prelude's
declarations are admitted, and `check_complete` run by
`Elaborator::finish_prelude` and again before any user module. (Since
docs/proposals/std-library.md stage 1 it is `finish_core`, which checks only
the core built-ins; a library built-in is bound when its file loads.) Syntax the
compiler *generates* as source (records' `==`, the runner's call of `main`
and `simulate`) is elaborated with those names temporarily meaning the
registry's declarations (`with_builtin_names`). The tests are in
`crates/driver/tests/builtins.rs`. The JS name encoding, the generated
ability names, and `module.rs`'s syntactic `ends_in_decidable` (which reads
the *written* name `Decidable`) move to stage 1.

**Stage 1: namespaces, qualified names and `import`.**

- Dotted declaration names; type namespaces (constructors, record
  projections, ability operations).
- The levels of §4.4 with `E-AMBIGUOUS` at use.
- `Std` and the default set.
- `import` with its errors.
- Qualified names in expressions, types, rows, patterns and handler
  clauses; exact pre-pass edges for them.
- Full type names in hashes.
- The prelude moved (§6), and every example, test, snapshot and playground
  example rewritten.
- `W-MODULE-NAME` extended.
- `E-STD-NAMESPACE`, checked on the resolved owner; the `not` alias.
- Raw collection and full-name registration as separate passes (§5).
- **Tests:**
  - accept examples: a file defining its own `length`, `Maybe` and `Yes`;
    adding functions to the file's own types and namespaces; importing;
    `Std.` escapes; a file that declares its own `List` and then
    `List.sum`, which extends *its* `List`;
  - a file declaring its own `Maybe` doesn't see the default `Just` and
    `Nothing` (decision 6), while `Std.Maybe.Just` still works;
  - reject examples: one per new error code, each asserting its code,
    including `List.sum` and `Std.List.sum` both refused with
    `E-STD-NAMESPACE`;
  - a user `List` with other constructors at the JS boundary, refused or
    encoded by its own codec, never as an array;
  - the user type `List` identical to the library's gets a different hash,
    and so do `Main.Geometry.Shape` and `Main.UI.Shape`;
  - short export names: two different types with one short name are
    `E-EXPORT`; one type reached twice isn't.

**As built** (stage 1), with what differs from the plan above:

- **Names** are resolved in `crates/elab/src/scope.rs`. Every declaration has a
  *key*, its full name (`Std.List.length`, or `Geometry.area` for a program's
  own), and the kernel's `Data` and `Def` carry a `path` (`Std.List`,
  `Main.Geometry.Shape`): data types hash it, and JS names definitions and
  type descriptions by it. A declaration's own `name` is its key without
  `Std.`, which is how messages show it. Only `E-AMBIGUOUS` and the
  suggestions of `E-UNKNOWN-NAME` print names "as the file would write
  them" (`Std.Maybe.Just` when the file hides `Maybe`); other messages print
  the key without `Std.`.
- **Qualified names are one token**: the lexer joins `Upper.name…` with no
  spaces; after a lowercase component, `.` is field access as before. A
  binder, field or constructor being declared can't be qualified.
- **Library namespaces are closed on what the qualifier means.** A
  declaration's qualifier that names a library namespace is refused even
  when it isn't a type (`Text.size`, `Effect.size`), since §4.6 makes those
  namespaces available as qualifiers in every file.
- **Imports of a program's own namespaces** (`import Console.Log (log)`)
  are resolved after the qualified declarations are registered, so they
  can't affect how a qualifier resolves; imports of the library's are
  resolved before (§5).
- **Aliases** are a list in the elaborator (`ALIASES`: `not` for
  `Bool.not`), not syntax.
- **Code the compiler generates as source** (records' `==`, the runner's
  call of `main` and `IO.simulate`) names the library from `Std`, which no
  program can change; stage 0's temporary rebinding of names is gone.
- **Generated names** are unspellable: an ability's constructors
  (`State.%get`), `State.%res`, `State.%elim`, and a record's constructor
  (`Person.%mk`).
- **JS** (§7.3) is done here rather than in stage 0: the injective encoding,
  short export and type names with `E-EXPORT` on clashes (checked when a file
  loads), and the runtime's partial-computation token renamed to `delayed`
  so it can't meet a definition's name.
- Two constructors with one name in two types of a file were
  `E-DUPLICATE`; they're now `E-AMBIGUOUS` where the short name is used.
- The pre-pass's "returns `Decidable`" (for `auto`'s hints) now asks what the
  result's head means, not how it's spelt.

**Stage 2: dot notation by type** (needs records stage 1 merged, since it
shares `Expr::Field`).

- §4.8 in full: receiver-first elaboration for complete calls, the
  type-head view, `Eq`.
- Fields and functions in one lookup; projections writable.
- The pre-pass over-approximation with certain and speculative edges, and
  mitigations 1, 2 and 3 of §5.
- **Tests:**
  - receiver in a non-first position (`line.split ','`);
  - partial application (`t.split`), and `E-DOT-PARTIAL` for `s.read`;
  - the dependent receiver: `s.read 3` checks and `s.read 4` fails;
  - an alias's namespace (`p.show` with `p : Price` finds `Price.show`,
    and falls back to `Nat.show` without one), whatever the evaluator does;
  - a blocked unfolding (`x : Family n`) reports and stops;
  - a found `T.f` with no receiver parameter stops lookup;
  - inference through `people.map (\p -> p.name)`;
  - evaluation order: an effectful receiver and an effectful argument run
    receiver first, then the arguments as written;
  - the spurious-cycle example of §5 and its note, and the mixed-kind
    example with its diagnostic;
  - every error of §4.12.

**As built** (stage 2), with what differs from the plan above:

- **Where:** `crates/elab/src/dot.rs`. `e.f`, `e.f args` and leftover
  components of a qualified name (`P.x`, `Origin.x`) all go through
  `infer_dot`; the records lane's `infer_field` is gone, since a field is
  found as its projection `T.f`, already in the type's namespace.
- **Types as written.** Values unfold nicknames at once, so the elaborator's
  context now records each variable's type *as written* where it's known:
  a definition's parameters (from its signature term) and `let`s (the
  annotation, or the value's written type). An application's is its
  function's declared result type, instantiated; an annotation's is the
  annotation. Elsewhere (pattern variables from constructor fields, lambda
  parameters) the view starts from the type's value, so a nickname there is
  already unfolded.
- **The view's unfolding step:** a definition whose body isn't a case tree
  is unfolded by substituting its arguments into the body term (so a
  nickname of a nickname is seen step by step); one defined by matching is
  run, and if it's stuck that's the blocked case (`E-NO-NAMESPACE`). The
  view never retries a head it has seen, so it always stops. Receiver
  matching reads each parameter's type through the same view, and matches
  if any head on the way is `T`.
- **Errors:** a written argument that disagrees with what the receiver
  fixed (`s.read 4`) is `E-TYPE-MISMATCH` (there's no `E-MISMATCH`). Named
  implicit arguments (`e.f [x := …]`) aren't accepted through dot
  notation (`E-ARITY`, suggesting the full call). Finding a constructor or
  type rather than a function at `T.f` is `E-DOT-NO-RECEIVER`. The records
  lane's `E-NOT-A-RECORD` for `.field` is gone (`examples/reject/
  record-not-a-record.sw` became `dot-unknown-function.sw`, since `p.fst`
  on a `Pair` is now `Pair.fst p`); record patterns and updates keep it.
- **Partial application** (`t.split`) is `(\r -> \c -> Text.split c r) t`,
  annotated, so the receiver is evaluated once. Only parameters before the
  receiver can be missing; ones after it are ordinary currying.
- **Effects:** in a computation, `e.f a` runs `e`, then the arguments, then
  calls; a call is recognised as performing operations when its target can
  be found without elaborating the receiver (a variable, or a definition
  without implicit parameters). A dot call on any other receiver whose
  target performs operations isn't recognised as a computation (left
  over).
- **The pre-pass:** `e.f` (and a qualified name's leftover components)
  adds a speculative edge to every declaration of the module whose key ends
  in `.f`, carrying "`.f` might mean `X.f`". Records' fields aren't given
  edges: a record's projections only exist once the record is checked, and
  a receiver of a record type reaches the record through certain edges (its
  type is mentioned by whatever produced it), so the mixed-kind example of
  §5 is accepted rather than refused. Mitigation 1 is the note on
  `E-MUTUAL-KIND` (a component joined by a speculative edge); mitigation 3
  is that the pre-emptive `E-MUTUAL-SIGNATURE`/header checks skip
  speculative edges, leaving a real use to the elaborator, which reports it
  when it meets the unfinished sibling. **Mitigation 2 (narrowing edges by a
  syntactic type head) isn't built** (left over): the spurious-cycle example
  of §5 is accepted, checked as one group.
- **The library** has no `List.map`, so `xs.map` needs one; the tests use
  their own `Bag` type. Adding list functions to the prelude is left over.
- **Tests:** `examples/accept/dot-notation.sw` (non-first receiver, partial
  application, the dependent receiver, a nickname's namespace and its
  fallback, `let`s, `p.name.length`, `p.sym`, `Person.name` as a function,
  inference through `people.map`, forward references by dot, the
  spurious-cycle example, and evaluation order with effects); and
  `examples/reject/dot-*.sw`, one per error.

Stage 1 alone makes code wordier (`Text.length t`) until stage 2 lands. So
the two should be built back to back, in one lane, and merged separately.

## 10. Recommendation

1. Adopt **§4 as written**. A global tree of full names with the library
   under `Std`. Types own namespaces. Declarations are placed by their
   dotted name. Unqualified names resolve by the four levels of §4.4, where
   the file's own names hide defaults and ambiguity is reported at use.
   `import N (a, b)` sits at the top of the file. The default set is `Std`'s
   root, plus the `not` alias (§4.6). User files can't add to `Std`'s
   namespaces. Dot notation follows Lean's rule through a deterministic
   type-head view, with the receiver elaborated first for complete calls
   and no postponement.
2. Do **stage 0 first, as its own merge.** Binding built-ins by identity is
   needed whatever the namespace design, and it removes the reliance on
   "prelude names can't be redefined" that today sits in four crates (core,
   elab, js, driver). The reviewer agreed it can proceed independently.
3. Then **stages 1 and 2 back to back**, after records stage 1 merges.
4. Keep `auto` blind to imports (§7.1).
5. Defer everything in §8. Each is compatible as described.

## 11. Questions for the user

Answered on 16 October 2026; the answers are at the top of the note and
the body follows them. Kept for the record. Only real taste choices; my
recommendation was given with each.

- **Q1. `not` everywhere?** By D4, `not b` becomes `b.not` or `Bool.not b`.
  It's used about as often as an operator (51 times in the examples). Should
  `not` be in the default set, the one function there? *Recommendation:
  yes.*
- **Q2. `print` and `readLine` everywhere?** They're `IO`'s operations, and
  almost every program with `main` uses them. Should `IO` (and so `print`
  and `readLine`) be in the default set? *Recommendation: yes.*
- **Q3. Inside `List.sum`, other `List` names without `List.`?** Lean allows
  this. *Recommendation: not at first*, because it can make `length` mean
  something different inside `List.sum` than in the rest of the file. It
  can be added later safely, if done so that it only fills in names that
  would otherwise be unknown.
- **Q4. Adding your own functions to library namespaces?** For example,
  `List.sum` in your file, then `xs.sum`. *Recommendation: yes*, as in
  Lean. The catch is that if the library later adds a `List.sum`, your file
  gets an "already defined" error and you rename yours.
- **Q5. The library's escape-hatch name.** `Std.List.map` always means the
  library's, even if your file defines its own `List`. Is `Std` a good name?
  You'd rarely type it.

## 12. Open questions for the reviewer

**Answered by the external review (16 October 2026).** In brief, and adopted
in draft 2:

- **R1:** over-approximation is acceptable initially, with narrowing and
  honest diagnostics; it can also make false mixed-kind cycles (§5). Keep
  certain and speculative edges distinct. Reporting `E-MUTUAL-SIGNATURE`
  from elaborated references is sound only while it never authorises a
  pending sibling.
- **R2:** make the type-head view explicit and deterministic; stop when
  unfolding is blocked; a stuck application uses its definition's
  namespace; a found `T.f` without a receiver stops lookup (§4.8).
- **R3:** no postponement needed at first. Receiver-first works for complete
  calls; missing arguments the receiver depends on need a separate rule,
  which draft 2 makes an error (§4.8.2). Keep elaboration order and
  evaluation order apart.
- **R4:** no loss of soundness, but binding syntax and replacing a
  definition with a native are separate; keep the natives' existing
  validation; audit the effect machinery too, in both directions (§4.7, §9).
- **R5:** hash the full logical path including intermediate namespaces,
  never a physical path; qualify the cache promise (§7.4).
- **R6:** not reviewed in detail; stays a later decision.
- **R7:** revalidation must rerun lookups, including the absence of nearer
  candidates (§7.5).
- **R8:** approve the encoding and short export names, with whole-generator
  disjointness and identifier-validity tests, and identity-based collision
  checks (§7.3).
- **R9:** moot (Q4 deferred).

The original questions follow.

- **R1. Dependencies for dot notation.**
  - Is over-approximating the pre-pass (§5) acceptable, given that it can
    merge components and so impose the mutual-recursion restrictions
    spuriously?
  - Or should components be formed lazily? That would mean elaborating
    until a reference to an unchecked declaration is resolved, then
    checking that first, and treating cycles found this way as groups.
  - Is reporting `E-MUTUAL-SIGNATURE` only for references present in the
    elaborated signature sound with respect to the kernel's admission rules
    (the kernel refuses a group that refers to an unfinished declaration
    outside it, so a scheduling mistake can't split a cycle)?
- **R2. The head of the receiver's type.**
  - Is "folded head first, then unfold one step, repeat" (§4.8, Lean's
    loop) well-defined for Stitchwort's values? `Value::Neutral(Head::Def, …)`
    is "a folded definition". Does unfolding always terminate here (it does
    for total definitions)?
  - Should stuck applications (a definition stuck on a variable) count as
    having that definition's namespace?
- **R3. No postponement.** Is receiver-first elaboration (§4.8.2) enough in
  practice?
  - Or should applications elaborate lambda arguments last, a cheap form of
    postponement (GHC's Quick Look and Lean's postponement are the
    heavyweight versions)?
  - Does elaborating the receiver out of order interact badly with
    dependent parameter types? For example, a receiver whose parameter type
    mentions an *earlier* explicit parameter (`Vec.get : (i : Fin n) -> Vec
    a n -> a`, receiver second). Its type is unified with metavariables for
    `n` before `i` is checked. I believe that's fine, since the other
    arguments are checked against the instantiated types, but it should be
    checked.
- **R4. Built-ins by identity.** Is there any place where binding syntax to
  a fixed `Std` declaration, rather than whatever is in scope, is less sound
  or less expected than today? In particular, `==`'s decision is still found
  by `auto` by type, so a user's own decision procedure for their own type
  is still used.
- **R5. Hashing full type names.**
  - Is hashing `Std.List` and `Main.Shape` the right reading of DESIGN §11,
    with `Main` as a placeholder until files have logical names?
  - Should a type's hash include the full path of its namespace, so that
    moving a type between namespaces makes a new type? Or only its module
    and short name?
- **R6. Operators for `Int`.** Is "an operator means `T.op` for the head `T`
  of its left operand's type" (§8) a reasonable direction, given numeric
  literals that default to `Nat`? Or should `Int` get its own operators?
- **R7. The elaboration cache.** Is recording resolutions and re-validating
  them (§7.5) the right key design once name resolution depends on types?
- **R8. JS names.** Is the `$`-plus-code-letter encoding (§7.3) enough? Are
  short export names, with a collision error, preferable to qualified ones?
- **R9. Extending library namespaces** (§4.3, Q4). Lean allows it. Once
  there are several files, two files can both add `List.sum`, which is a
  conflict only if both are loaded. Should it be refused now to avoid that
  later, or handled then as a clash at import?

## What I couldn't verify

**About other systems.** These were checked against primary sources by a
research pass on 16 October 2026, except as noted here.

- **Lean.** That a `def` (not just an `abbrev`) is unfolded when looking for
  a namespace. This is a reading of `resolveLValLoop` [L5], not tested. That
  `def List.foo`'s body has `List` opened is an inference from two sentences
  of [L1]; the page has no example.
- **Agda's constructor overloading by expected type.** Only secondary sources
  were found. The data-types page itself says constructor names "must be
  new w.r.t. the current signature and context" [A3].
- **Rust.** The Reference pages fetched don't state in so many words that
  local items shadow the standard prelude, or that an unresolved `use` or a
  clash between an explicit `use` and a local item (E0255) is an error. Both
  are well-known behaviour.
- **Scala.** That importing a non-existent member is an error.
- **Smaller gaps.** Gleam's exact unqualified-import syntax, OCaml's
  `-nopervasives`, and the details of Unison's `use` clauses. Koka's
  overloading algorithm [K1] is cited from the book, not from the paper.

**About Stitchwort.**

- (Draft 1.1 asked whether inferred types are still folded when dot
  notation looks at them. Draft 2 makes it irrelevant: the type-head view of
  §4.8 reads the elaborated type term by rule.)
- Whether the JS name clash `a''b` / `a.b` (§7.3) is reachable today through
  generated ability names. The mapping is clearly not injective, but no test
  exercises it.
- How `auto`'s linear scan performs with a much larger library (§7.1).
- The records lane is unfinished (`0d05f53`, a WIP commit). §1.7 and §4.8.1
  describe its design note and current branch, which may change.
- The occurrence counts in §6 are rough `grep` counts, and include comments.

## Sources

Lean 4
- [L1] Lean Language Reference, "Namespaces and Sections".
  https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/
- [L2] Lean Language Reference, "Declaration modifiers" (`private`,
  `protected`). https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/
- [L3] Lean Language Reference, "Identifiers" (dotted identifiers,
  ambiguity, leading dot).
  https://lean-lang.org/doc/reference/latest/Terms/Identifiers/
- [L4] Lean Language Reference, "Function application" (generalized field
  notation). https://lean-lang.org/doc/reference/latest/Terms/Function-Application/
- [L5] Lean 4 source, `src/Lean/Elab/App.lean` (`resolveLValLoop`,
  `resolveLValAux`), at commit `88539871`.
  https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean

Agda
- [A1] Agda documentation, "Module System".
  https://agda.readthedocs.io/en/latest/language/module-system.html
- [A2] Agda documentation, "Record Types".
  https://agda.readthedocs.io/en/latest/language/record-types.html
- [A3] Agda documentation, "Data Types".
  https://agda.readthedocs.io/en/latest/language/data-types.html

Haskell
- [H1] Haskell 2010 Language Report, chapter 5, "Modules" (§5.3 imports,
  §5.5.2 name clashes, §5.6.1 the Prelude).
  https://www.haskell.org/onlinereport/haskell2010/haskellch5.html
- [G1] GHC User's Guide, `OverloadedRecordDot`;
  and GHC proposal 282, record dot syntax, §2.3 (whitespace).
  https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_record_dot.html,
  https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html

Elm
- [E1] elm/core README, "Default Imports".
  https://github.com/elm/core/blob/master/README.md
- [E2] Elm compiler source: `compiler/src/Elm/Compiler/Imports.hs`,
  `compiler/src/Canonicalize/Environment/Local.hs` (`addVars`),
  `compiler/src/Canonicalize/Environment.hs` (`Ambiguous`),
  `compiler/src/Canonicalize/Environment/Foreign.hs`
  (`ImportExposedValueNotFound`). https://github.com/elm/compiler

Python, Scala, Rust, OCaml
- [P1] Python Language Reference, "The import statement".
  https://docs.python.org/3/reference/simple_stmts.html#the-import-statement
- [S1] Scala 3 Book, "Packaging and Imports".
  https://docs.scala-lang.org/scala3/book/packaging-imports.html
- [S2] Scala 3.4 Language Specification, chapter 2, "Identifiers, Names and
  Scopes". https://scala-lang.org/files/archive/spec/3.4/02-identifiers-names-and-scopes.html
- [R1] The Rust Reference, "Use declarations".
  https://doc.rust-lang.org/reference/items/use-declarations.html
- [R2] The Rust Reference, "Name resolution" (glob-vs-glob ambiguity).
  https://doc.rust-lang.org/reference/names/name-resolution.html
- [R3] The Rust Reference, "Preludes".
  https://doc.rust-lang.org/reference/names/preludes.html
- [O1] OCaml manual, "The core library".
  https://ocaml.org/manual/latest/core.html
- [O2] OCaml manual, "Expressions", local opens.
  https://ocaml.org/manual/latest/expr.html
- [O3] OCaml manual, "Overriding in open statements"; warnings 44 and 45 in
  `utils/warnings.ml`. https://ocaml.org/manual/latest/overridingopen.html,
  https://github.com/ocaml/ocaml/blob/trunk/utils/warnings.ml

Unison, Idris, Koka, Gleam
- [U1] Unison, "The big idea". https://www.unison-lang.org/docs/the-big-idea/
- [U2] Unison language reference, "Name resolution and the environment".
  https://www.unison-lang.org/docs/language-reference/name-resolution-and-the-environment
- [U3] Unison language reference, "Type-directed name resolution".
  https://www.unison-lang.org/docs/language-reference/_type-directed-name-resolution
- [I1] Idris 2 documentation, "Modules and Namespaces".
  https://idris2.readthedocs.io/en/latest/tutorial/modules.html
- [I2] Idris 2 documentation, "Records" (dot syntax, lexing of `Foo.bar`).
  https://idris2.readthedocs.io/en/latest/reference/records.html
- [I3] Idris 2 source, `src/TTImp/Elab/Ambiguity.idr`, at commit `89ba32eb`.
  https://github.com/idris-lang/Idris2/blob/main/src/TTImp/Elab/Ambiguity.idr
- [K1] The Koka Programming Language (book), §3.1.2 "Dot selection" and
  §3.1.3 (overloading). https://koka-lang.github.io/koka/doc/book.html
- Gleam language tour, "Unqualified imports" (background only).
  https://tour.gleam.run/basics/unqualified-imports/

Stitchwort (commit `787fa54` unless noted)
- `crates/elab/src/lib.rs`, `module.rs`, `check.rs`, `auto.rs`,
  `autobind.rs`, `effects.rs`, `prelude.sw`; `crates/core/src/hash.rs`,
  `native.rs`, `pretty.rs`, `globals.rs`; `crates/js/src/lib.rs`;
  `crates/syntax/src/lexer.rs`; `crates/driver/src/driver.rs`, `run.rs`.
- [records.md](records.md) draft 2 (commit `d0940d4`), and the records lane's
  branch at `0d05f53` (`Expr::Field`, the `.` token).
- [mutual-recursion.md §10.2](mutual-recursion.md#102-as-built-milestone-2-function-groups-and-forward-references).
- DESIGN.md §4, §11, §12, §16; [syntax.md](../syntax.md); `TODO.md`.
