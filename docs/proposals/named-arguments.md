# Named and default arguments

Status: design only (SW-390). Nothing here is built. Decisions D1092 to D1101
are open (§8).

Claims about the codebase cite `file:line` and are marked **[checked]** (read
in the source, or run against `target/debug/stitchwort` built from `main` on
23 Oct 2026) or **[inferred]**. Claims about other languages cite a URL;
**[unverified]** marks the ones written from memory.

## 0. Summary

- **Named arguments** for explicit parameters, `between (low := 1) (high := 5)`,
  spelt like today's named implicit arguments `[x := e]` but with round
  brackets. They are sugar: the call elaborates to the same positional term,
  so it has the same content hash as `between 1 5`.
- **Default values on record fields** (and constructor fields), not on
  function parameters, at first:
  `type RangeOptions = { start: Nat := 0, stop: Nat, step: Nat := 1 }`, so
  `range { stop = 10 }` works. A function still takes one record, so
  currying, partial application, pipes, sections and function values don't
  change at all. At the JS boundary it is the options object TypeScript
  programmers already write.
- **Defaults in signatures**, `(step: Nat := 1)`, are designed here (§5) but
  deferred: they are the part that fights currying, and the record form
  covers most uses.

## 1. The problem, goals and non-goals

**Readability with several arguments of one type.** `between 1 5`,
`Text.replace line "a" "b"`, `Rect.make 10 20 3 4`: the reader has to know the
order, and swapping two `Nat`s still type-checks. Named arguments make the
call say what each value is, and make a swap impossible.

**Optional configuration.** A function with five settings, most of which
callers leave alone (a pretty-printer's width, indent, line ending), needs a
way to give only the ones that differ, and to add a sixth setting later
without editing every caller.

Goals:

1. A call can name its arguments, in any order, with no change to what the
   call means or to its hash.
2. A caller can leave out settings that have a sensible default, and a
   library can add a defaulted setting without breaking callers.
3. No silent argument swaps: adding a default or a named argument must never
   make an existing positional call mean something else.
4. Works with what's there: currying and partial application, dot notation
   (`x.f`), method sections (`.f`), pipes (`|>`), implicit and `auto`
   arguments, proofs, and the JS/TS boundary.

Non-goals:

- Defaults on implicit or `auto` parameters (Idris's `{default 0 lag: Nat}`).
  `auto` already is "a default found by search", and `[ord := …]` already
  overrides it (`docs/syntax.md:504-507`) **[checked]**.
- Default *types*, variadic functions, or Python's `**kwargs`.
- Making parameter names part of a function's type. A function value's type
  stays a plain arrow type (§4.3).

## 2. What Stitchwort can do today

### 2.1 Named implicit arguments

An implicit or `auto` argument can be given by name: `f [x := e]`
(`docs/syntax.md:494`, `:504`) **[checked]**, including implicit fields of a
constructor, `VCons [n := k] x xs` (`docs/syntax.md:254`, `:257`)
**[checked]**, and `auto` parameters of types, `Map Nat Nat [ord := descending]`
(`docs/syntax.md:510`) **[checked]**.

How it works: the parser makes `Expr::NamedArg` from `[name := expr]`
(`crates/syntax/src/parser.rs:3018-3037`, `crates/syntax/src/ast.rs:55-57`)
**[checked]**. The elaborator collects the application spine into
`Arg::Explicit | Arg::Named | Arg::Piped` (`crates/elab/src/check.rs:541-546`)
**[checked]**, and for a named one walks the function's type, inserting
unknowns for the implicit parameters it passes, until it reaches the implicit
binder with that name (`insert_until`, `check.rs:1521-1548`; used at
`check.rs:1102-1109`) **[checked]**. The name comes from the binder in the
function's type (`Value::Pi(x, …)`), and the result is an ordinary
application term.

Two limits found by running it **[checked]**:

- **Order matters.** With `def pick [count: Nat] [label: Text] (x: Nat)`,
  `pick [count := 3] [label := "a"] 1` works, but
  `pick [label := "a"] [count := 3] 1` is `E-UNKNOWN-NAME` ("no implicit
  parameter named `count` here"): `insert_until` has already passed `count`.
- **Explicit parameters can't be named.** `between [high := 5] [low := 1]` is
  `E-UNKNOWN-NAME` ("not an implicit parameter of this function"), and
  `between (high := 5) (low := 1)` is `E-PARSE` ("expected `)`, but found
  `:=`"). So round brackets with `:=` are free syntax.

### 2.2 Records as an options parameter

A function can take a record, with a value of defaults that callers update
(`{ e | f = … }`, `docs/syntax.md:279, :290`) **[checked]**:

```
type RangeOptions = { start: Nat, stop: Nat, step: Nat }

def RangeOptions.defaults: RangeOptions := { start = 0, stop = 10, step = 1 }

def RangeOptions.span (options: RangeOptions): Nat :=
  (options.stop - options.start) * options.step

test "update the defaults" := { RangeOptions.defaults | stop = 20, step = 2 }.span == 40
```

This checks and passes today **[checked]**. Where it falls short:

- **Every field must be given in a literal.** `span { stop = 20 }` is
  `E-RECORD-FIELD` ("missing `start`, `step`") **[checked]**, so callers must
  know the name of the defaults value and write the update form.
- **Required settings don't fit.** If `stop` has no sensible default, the
  defaults value has to invent one, or `stop` becomes a separate positional
  parameter.
- **One type per function** (or per family of functions) has to be declared.
  That is also its strength: the settings get a name, documentation, and a
  type that can be passed around and stored.

### 2.3 Related machinery a design must fit

- **Named construction** `C { f = v, … }` (D605 (a), D1085 (a); SW-387, in
  progress). Braces right after a constructor name its fields, and a record
  argument is written `C ({ … })` (`docs/proposals/variant-fields.md:460-480`,
  `:1311-1320`) **[checked]**. That doc also left Lean's `(name := p)` open as
  "a reasonable later addition for mixing named and positional arguments"
  (`variant-fields.md:464-465`) **[checked]**. After a *function*, braces stay
  a record literal argument; this note keeps that, since §2.2's convention
  depends on it.
- **Dot notation** puts the receiver in the first parameter of the receiver's
  type, at any position (`docs/syntax.md:289`) **[checked]**.
- **Method sections** `.f a` are `x => x.f a`, or the partial application
  itself when the receiver is last (`docs/syntax.md:958-963`) **[checked]**;
  `dot.rs:505` gives up the partial-application form if a named argument is
  present **[checked]**.
- **Pipes**: `x |> f a b` is `f a b x`, with `x` elaborated first
  (`crates/elab/src/pipe.rs:1-3`) **[checked]**. Named arguments are already
  passed through (`pipe.rs:33`) **[checked]**.
- **Evaluation order**: arguments are evaluated left to right as written
  (`docs/syntax.md:540`) **[checked]**.
- **Content hashes leave out binder names** (`crates/core/src/hash.rs:29-30`;
  `Pi` and `Lam` hash only their `icit`, `hash.rs:545-554`) **[checked]**. So
  renaming a parameter doesn't change a function's hash.
- **The check cache is keyed by source text** and the keys of imports, not by
  content hash (`docs/proposals/check-cache.md:41-50`, `:148-170`)
  **[checked]**. So when a callee's parameter names change, every caller is
  re-elaborated, and a call by a name that no longer exists is reported.
- **The JS boundary** exports an uncurried function whose TypeScript
  parameters are the binder names (`crates/js/src/lib.rs:1005-1018`), and an
  `Option` parameter is `x: T | undefined`, not optional, while a record's
  `Option` field is an optional property `f?: T`
  (`crates/cli/tests/extract.rs:866-867`) **[checked]**. A record parameter
  crosses as a plain object: `render(settings: Settings, count: bigint)` with
  `type Settings = { readonly width: bigint; readonly label?: string }`
  **[checked]** (built with `build --js`).

## 3. Other languages

| Language | Named | Defaults | Notes |
|---|---|---|---|
| Kotlin | `f(x = 1)`, any order | `(x: Int = 0)`, may use earlier params; evaluated only when needed; overriding methods keep the base's defaults | "after the first skipped argument, you must name all subsequent arguments"; no named syntax for Java callees. https://kotlinlang.org/docs/functions.html#named-arguments |
| Scala | `f(x = 1)` | `(x: Int = 0)` | Defaults are compiled to extra methods the call site calls **[unverified]**; a function *value* made from a method loses its defaults **[unverified]**. https://docs.scala-lang.org/tour/named-arguments.html, https://docs.scala-lang.org/tour/default-parameter-values.html |
| Swift | argument labels, required by default | `(x: Int = 0)` | SE-0111 removed labels from function types: "Function types may only be defined in terms of the types of the formal parameters and the return value"; labels only apply when calling a declared name. https://github.com/swiftlang/swift-evolution/blob/main/proposals/0111-remove-arg-label-type-significance.md |
| Python | `f(x=1)`, keyword-only after `*` | `def f(x=0)` | The default is evaluated once, at definition, so a mutable default is shared between calls. https://docs.python.org/3/tutorial/controlflow.html#default-argument-values |
| OCaml | labels `~x` | optional `?x`, `?(step = 1)` | Labels are part of the type; total applications commute. An optional argument is dropped only when a *later unlabelled* argument is applied, so a function needs a positional parameter after its optional ones; with higher-order functions "the compiler assumes that there are no optional arguments". https://ocaml.org/manual/latest/lablexamples.html |
| Lean 4 | `f (x := e)`, for any parameter kind | `(x : Nat := 5)` (`optParam`), `(h : p := by tac)` (`autoParam`) | Naming a later parameter while earlier explicit ones are missing makes a lambda: `sum3 (z := 8)` is `fun x y => sum3 x y 8`. A default is used "if it is not supplied" when no positional argument is available. https://lean-lang.org/doc/reference/latest/Terms/Function-Application/#optParam |
| Idris 2 | `f {x = e}` (implicits) | `{default 0 lag : Nat}` on implicits | The docs say defaults are "primarily intended" for proof search, the Fibonacci example is "illustrative only". https://idris2.readthedocs.io/en/latest/tutorial/miscellany.html |
| Agda | `f {x = e}`, implicit and instance arguments only **[unverified]** | none **[unverified]** | https://agda.readthedocs.io/en/latest/language/implicit-arguments.html |
| Haskell | records (`f defaultOpts { width = 80 }`) | the `Default` class | https://hackage.haskell.org/package/data-default |
| Unison | none | none: "use the Optional type … and then provide a default value inside the function body" | https://www.unison-lang.org/compare-lang/unison-for-python-devs/ |
| Roc | records | optional record fields with a default, given in the function's destructuring pattern; spelling has changed between versions **[unverified]** | https://github.com/roc-lang/roc/blob/main/roc-for-elm-programmers.md |
| Elm | records | none; a defaults record and update | **[unverified]** |
| TypeScript | options objects | `x?: T`, `x = 0` (trailing in practice) | https://www.typescriptlang.org/docs/handbook/2/functions.html#optional-parameters |

What went wrong elsewhere, and what this design avoids:

1. **Defaults versus currying** (OCaml). In `f a`, is the call finished, so
   the default applies, or is it waiting for more? OCaml's answer (a later
   positional argument settles it) means a trailing optional argument can't
   be dropped, and gives a warning. Lean settles it per written application.
2. **Defaults lost through function values** (Scala, Swift, OCaml's
   inference note). Defaults belong to a declaration, not to a type, so
   `xs.map f` can't use them. Every language that keeps types simple accepts
   this.
3. **Names in types** (OCaml labels, pre-3.0 Swift) make unification compare
   names, and higher-order code needs annotations. Swift took them out.
4. **Renaming a parameter breaks callers** (Kotlin, Python). It is an API
   change once callers can use names.
5. **Evaluation time of defaults** (Python's shared mutable default).
   Stitchwort values are immutable, so only effects matter (§6.4).

## 4. Named arguments for explicit parameters

### 4.1 Syntax

```
def between (low: Nat) (high: Nat): List Nat := …

let window := between (low := 3) (high := 9)
let sameWindow := between (high := 9) (low := 3)
let mixed := between 3 (high := 9)
```

`(name := expr)` in argument position names an explicit parameter;
`[name := expr]` keeps naming implicit and `auto` ones. The bracket says
which kind of parameter it is, as in declarations (D1093). Writing the wrong
bracket is an error with the fix ("`high` is an explicit parameter: write
`(high := …)`"). It reuses `:=` ("gives a value") and Lean's spelling, and
`(x :=` can't start any expression today (§2.1).

### 4.2 Elaboration: sugar over positional application

For a spine `h a₁ … aₙ`:

1. Walk `h`'s type. Collect the named arguments by name; each must name a
   parameter of the right kind that hasn't been given (`E-UNKNOWN-NAME`
   listing the parameters, or `E-DUPLICATE-ARGUMENT`).
2. Positional arguments (and a piped value, last) fill the explicit
   parameters that aren't named, left to right. Implicit and `auto`
   parameters not named are inserted as today.
3. The result is the same `Term::App` chain as the positional call. When the
   arguments are pure, `between (high := 9) (low := 3)` and `between 3 9`
   are the same term, so the same hash **[inferred]**: switching a call
   between styles reruns no tests.
4. Arguments are checked in the parameters' order (dependent types need
   that), but **performed** in the written order (`docs/syntax.md:540`). When
   a reordered argument may perform an operation, the elaborator binds it
   with a `let` first, in written order. A pure call has no `let`s.

The same rule applies to implicit names (D1094): `[label := …] [count := …]`
in either order, which fixes the order limit in §2.1.

**Naming a later parameter while an earlier one is missing** gives a function
of the missing ones, as Lean does (D1095):

```
def clampTo (low: Nat) (high: Nat) (value: Nat): Nat := …

let capped := readings.map (clampTo (low := 0) (high := 100))
let atMostTen := clampTo (high := 10)       -- low value => clampTo low 10 value
```

The second is a lambda over `low`, not a partial application. If the named
value performs an operation it is bound by a `let` outside the lambda, so it
runs once, where it's written.

### 4.3 Where the names come from

The names are the binders of the head's type, exactly as `insert_until` reads
them today (`check.rs:1530`) **[checked]**. So:

- **Top-level definitions, local definitions and constructors** have the
  names in their headers or fields. A parameter written only as a type after
  the colon (`def length: List a -> Nat`) has no name and can't be named.
- **Function values** keep their names when their declared type has them:
  in `def retry (attempt: (count: Nat) -> (delay: Nat) -> Bool)`,
  `attempt (delay := 5) (count := 1)` works. But names never take part in
  unification (they aren't in the hash either), so any `Nat -> Nat -> Bool`
  can be passed as `attempt`. This is Swift's SE-0111 position: names are a
  calling convenience of the thing named, not part of the type.
- **Constructors**: `Circle (radius := 1) (id := "a")` works as for any
  function. It complements D605's `Circle { radius = 1, id = "a" }`: braces
  give every field (or use defaults, §5) and build a value; round brackets
  can name some and leave a function of the rest (D1096).

### 4.4 Interaction with the rest of the language

| Feature | Behaviour |
|---|---|
| Currying / partial application | `f a` stays a partial application. A named argument after missing positional ones gives a lambda (§4.2). |
| Dot notation `x.f` | The receiver fills its parameter first; named arguments then fill theirs. Naming the receiver's parameter too is `E-DUPLICATE-ARGUMENT`. `p.distanceTo (other := q)` is fine. |
| Sections `.f (x := e)` | `y => y.f (x := e)`. It stays a lambda, never the bare partial application (as `dot.rs:505` already does for `[x := e]`). |
| Pipes | `5 |> clampTo (low := 0) (high := 10)` is `clampTo 0 10 5`: the piped value is the last positional argument, filling the first explicit parameter not otherwise given. |
| Implicit / `auto` | Unchanged; `[x := e]` for them (any order, D1094). |
| Proofs | A theorem statement may use named calls; the term is the positional one, so `rfl` and rewriting see no difference. |
| Hover, errors, `show` | Terms print positionally; hover on a named argument shows the parameter. |
| JS | Nothing changes: JS calls are positional, and the `.d.ts` already uses the binder names. |

**Renaming a parameter is now a source-breaking change** for callers that
use the name. Callers are re-elaborated because the check cache is keyed by
source (§2.3), so it's reported, never silent. One silent case remains: a
library swaps two names *and* the order of their parameters in one edit.
Named callers stay correct; positional callers swap. That is today's risk,
and named calls are the fix for it.

## 5. Default values

### 5.1 First: defaults on record and constructor fields

```
type RangeOptions = {
  start: Nat := 0,
  stop: Nat,
  step: Nat := 1
}

def range (options: RangeOptions): List Nat := …

let small := range { stop = 10 }
let evens := range { stop = 10, step = 2 }
```

- **Syntax.** `field: Type := value` in a record declaration, and
  `(field: Type := value)` in a constructor's fields (so it works with D605's
  `Circle { radius = 1 }`). D1098.
- **Literals.** A record literal (or named construction) may leave out
  fields that have a default. A field without one is still required
  (`E-RECORD-FIELD`, as today). Positional construction `MkRange 0 10 1`
  still gives every field, so no existing call changes meaning (goal 3).
- **What a default may use.** Earlier fields and the type's parameters
  (`stop: Nat := start + 10`), as a dependent field type may (D1100). It must
  be pure.
- **Patterns, update, `==`, `show`, proofs** are unchanged: a value always
  has every field. Only literals get shorter.
- **Elaboration.** Each default becomes a generated definition taking the
  earlier fields it uses (as Scala compiles defaults to methods
  **[unverified]**, and as a `where` function is lifted to `f.go`,
  `docs/syntax.md:199`). A literal that leaves a field out calls it, so
  `{ stop = 10 }` is `MkRangeOptions defaultStart 10 defaultStep`.

Why fields first: a function still takes one value of a declared type, so
currying, partial application, pipes, sections, function values and `auto`
need no new rules at all. It improves §2.2's convention rather than adding a
second one, and it is the TypeScript options-object idiom (§5.3).

### 5.2 Defaults and identity

Should a default be part of what a type or function *is*? (D1099)

Recommended: **no**. The type's hash covers its fields' names and types as
now (`hash.rs:29-33`) **[checked]**; the default lives in the generated
definition, which has its own hash, and every literal that uses it refers to
it. Then:

- changing a default changes the hash of each place that relied on it, and of
  nothing else, so exactly those tests rerun;
- a literal that gave every field is unaffected;
- two types that differ only in defaults are still two different types,
  because data types are nominal (`hash.rs:31-33`) **[checked]**.

This matches how attributes are treated: metadata of the declaration that
"aren't part of content hashes" (`docs/syntax.md:433`) **[checked]**, except
that here the effect is visible in the uses' hashes, which is what a test
cache needs.

### 5.3 At the JS boundary

A record crosses as a plain object (`docs/syntax.md:299`) **[checked]**, so an
export taking `RangeOptions` takes an options object. A defaulted field is
optional going in, and the decoder fills it by running the default, in field
order. Coming out, a value always has the field. TypeScript needs two shapes
for that (D1101):

```ts
export type RangeOptions = { readonly start: bigint; readonly stop: bigint; readonly step: bigint };
export type RangeOptionsInput = { readonly start?: bigint; readonly stop: bigint; readonly step?: bigint };
export declare function range(options: RangeOptionsInput): bigint[];
```

(Sketch, not generated output.) This is the idiom TypeScript callers expect;
positional optional parameters (`step?: bigint`) only work at the end of a
list.

### 5.4 Later, if wanted: defaults in signatures

```
def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := …

let small := range 0 10
let evens := range 0 10 (step := 2)
```

This is the form Kotlin, Scala, Swift, Python and Lean users know. It is
deferred because of §3's first two problems; if it's built, these rules keep
it predictable (D1097):

1. **A defaulted parameter is named-only.** Positional arguments skip it:
   `range 0 10 2` is an error ("`step` has a default; write `(step := 2)`").
   So adding a default never shifts a positional argument (goal 3), and the
   question "is `f a` finished?" never comes up.
2. **A default is always filled when not named**, in every use of the
   declared name: a full call, a partial application (`range 0` is
   `stop => range 0 stop 1`), a bare name (`xs.map (range 0)`), dot
   notation, sections and pipes. So a function value never has a defaulted
   parameter in its type, and higher-order code is unchanged.
3. **To pass the whole function** with `step` still open, write the lambda:
   `start stop step => range start stop (step := step)`.
4. Identity and elaboration as in §5.2: a generated definition per default,
   taking the earlier parameters; the function's hash doesn't include it.
5. **JS**: an exported function's trailing defaulted parameters become
   optional, `range(start: bigint, stop: bigint, step?: bigint)`; a
   defaulted parameter followed by a required one is `T | undefined`.

Rule 2 makes a bare `range` mean the two-argument function, which is the
behaviour to check with users before building; Lean makes a similar choice
but **[unverified]** in its details for bare names.

## 6. Interactions checked against each option

### 6.1 Proofs and dependent types

Named arguments change no terms, so proofs are untouched. A default may
mention earlier parameters or fields, and a later parameter's type may
mention a defaulted one (`(size: Nat := 8) (cells: Vec Bool size)`):
elaboration fills the default before checking what follows, as it does for
an implicit argument. A proof field may have a default too (`ok: step > 0 :=
…`), written as a term; finding it by `auto` instead is a possible later
addition, not proposed.

### 6.2 `auto` and implicits

Out of scope for defaults (§1). Named implicits gain any-order (D1094).

### 6.3 Errors and tooling

- Unknown name: `E-UNKNOWN-NAME`, listing the parameters with their kinds.
- Missing required field: `E-RECORD-FIELD`, as now, noting which fields have
  defaults.
- The language server can complete parameter and field names after `(` or
  `{`, and hover shows defaults.

### 6.4 Effects

Named arguments run in written order (§4.2). Defaults must be pure, so when
they run doesn't matter (no Python-style shared state, §3 item 5).

## 7. Recommendation and staged plan

Build named arguments, then field defaults; keep signature defaults as a
later, separate decision. Record-based defaults give most of the value with
no new rules for function types, and match both D605's braces and the
TypeScript boundary.

| Stage | What | Lane | Cost |
|---|---|---|---|
| 0 | Document today's convention (a `T.defaults` value and `{ T.defaults \| … }`) in `docs/syntax.md` and the library guide; no compiler change | Sonnet | small |
| 1 | Named explicit arguments `(x := e)`; any-order `[x := e]`; lambda for skipped parameters; `let`s for effectful reordered arguments; dot, section and pipe cases; errors | **Opus** (application spine in `check.rs`, `pipe.rs`, `dot.rs`, `effects.rs`) | medium |
| 1b | Formatter, language-server completion and hover for parameter names; examples and docs | Sonnet; examples DeepSeek | small |
| 2 | Field defaults on records and constructors: syntax, generated default definitions, literals and named construction (after SW-387), library index and lazy loading of the generated names, check cache | **Opus** | medium |
| 2b | JS boundary: input alias, decoder fills defaults, `.d.ts` snapshots, `tsc` check | Sonnet | small to medium |
| 3 | (Only if D1097 says so) signature defaults per §5.4 | **Opus** | medium to large |

Acceptance for stage 1: every call in `examples/accept` gives the same hash
when rewritten with names (a differential test). For stage 2: a literal that
gives every field hashes as before; changing a default reruns only the tests
that use it.

## 8. Decisions for Matt

**D1092. Should explicit arguments be nameable at call sites?**
(a) **[Recommended]** Yes, `f (x := e)`, sugar over positional application
(§4). (b) Yes, but with the existing square brackets for every kind,
`f [x := e]`, losing the visible explicit/implicit distinction. (c) No;
records only.

**D1093. Must the bracket match the parameter's kind?**
(a) **[Recommended]** Yes: `(x := e)` for explicit, `[x := e]` for implicit
and `auto`, as in declarations; the wrong one is an error saying which to
write. (b) Either bracket names any parameter.

**D1094. Order of named arguments.**
(a) **[Recommended]** Any order, mixed freely with positional arguments;
positional ones fill the unnamed explicit parameters left to right; this
also applies to `[x := e]` (fixing §2.1's order limit). (b) Named after
positional only (Kotlin-like). (c) Declaration order only (today's rule for
implicits).

**D1095. Naming a later parameter while an earlier one is missing.**
(a) **[Recommended]** Gives a function of the missing ones, as Lean does:
`clampTo (high := 10)` is `low value => clampTo low 10 value`.
(b) An error ("`low` isn't given"), so a forgotten argument is caught at the
call rather than as a type mismatch later.

**D1096. Constructors: named arguments as well as D605's braces?**
(a) **[Recommended]** Yes, one rule for every function; braces build a whole
value (with defaults), `(x := e)` can name some fields and leave a function
of the rest. (b) Braces only for constructors, so there is one spelling.

**D1097. Defaults: where?**
(a) **[Recommended]** On record and constructor fields now (§5.1);
signature defaults (§5.4) decided again after stage 2 is in use.
(b) Both now. (c) Neither: document the `T.defaults` convention only.

**D1098. How a default is written.**
(a) **[Recommended]** `step: Nat := 1`, since `:=` gives a value everywhere
else (`let`, `def`, named arguments). (b) `step: Nat = 1` as in Kotlin,
Scala and TypeScript; but `=` is only equality in Stitchwort
(`docs/syntax.md:165`). (c) Idris's `default 1 step: Nat`.

**D1099. Is a default part of a declaration's identity (its hash)?**
(a) **[Recommended]** No: each default is its own generated definition, and
the uses that rely on it refer to it, so changing a default changes exactly
those uses' hashes (§5.2). (b) Yes: changing a default changes the type's
hash and so everything that mentions the type. (c) No, and the default's
value is copied into each use instead of referenced (same hashes as (a) in
effect, but no shared definition to hover or prove things about).

**D1100. What may a default refer to?**
(a) **[Recommended]** Earlier fields (or parameters) and type parameters,
pure only. (b) Constants only (no dependence on other fields).

**D1101. TypeScript shape for a record with defaulted fields.**
(a) **[Recommended]** A second alias `RangeOptionsInput` with `?` on the
defaulted fields, used for parameters; `RangeOptions` stays complete for
results. (b) One alias with `?` on defaulted fields everywhere; simpler, but
TypeScript readers of results must handle a missing field that is never
missing.

## 9. Risks

- **Two ways to write a call** (positional and named). The formatter keeps
  what was written; nothing forces either.
- **Parameter names become API.** Mitigated by re-elaboration through the
  check cache (§4.4); a library may want a lint for renamed public
  parameters later.
- **Lambda from a skipped parameter (D1095 (a))** can turn a forgotten
  argument into a confusing later type error. The error note should say
  "this call left out `low`, so it is a function".
- **Generated default definitions** add names the library index and lazy
  loading must know about, as shared-field projections did
  (`variant-fields.md`, §12.1). Stage 2 carries that risk.
