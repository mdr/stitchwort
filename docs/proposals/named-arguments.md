# Named and default arguments

Status: decided (SW-390). Built: stage 1 (named arguments, SW-399), stage 1b
(SW-400: formatter, completion and hover of parameter names) and stage 2
(field defaults, SW-401); see the "As built" sections. Stage 2b (JS input
shapes) and stage 3 (signature defaults) not built. Revised after external review
(24 Oct 2026). All decisions in §8 were taken as recommended (Matt, 24 Oct
2026).

Claims about the codebase cite `file:line` and are marked **[checked]** (read
in the source, or run against `target/debug/stitchwort` built from `main` on
23 Oct 2026, or `target/release/stitchwort` built from `main` at `ba8bdfc6`
on 24 Oct 2026) or **[inferred]**. Claims about other languages cite a URL;
**[unverified]** marks the ones written from memory.

## Changes after review

An external reviewer endorsed the split (named arguments and field defaults
now, signature defaults later) and every recommended option, and asked for a
precise elaboration specification first. What changed, by review point:

| Review point | Change |
|---|---|
| §2 Effects and dependencies | New §4.5, "Run order". It starts from what the elaborator already does (all effectful arguments run first, in written order, then the application stages; probes in §4.5) and adds rules for skipped parameters, the head, receivers and pipes. A computation that would have to run before something it depends on is refused (new D1113). The effect-trace invariant is stated. |
| §3 Skipped explicit parameters | §4.2 rule 5: a missing explicit parameter is a rigid variable, never inferred; `use (xs := three)` is an error with a fix. Diagnostics name what is still awaited (§6.3). D1095 updated. |
| §4 Names outside types | §4.3 rewritten as a contract: names come only from declared signatures, found syntactically, never from an unknown solved by unification (new D1115). `let g := f`, `if` branches, repeated names, synonyms and reduction are settled. The Swift attribution is fixed: SE-0111 forbids labels on calls through function values; Lean is the precedent. The "renames are always reported" claim is corrected with the `subtract` counterexample (§4.4). |
| §5 Slot reservation | §4.2 now gives the matching algorithm. `f 1 (x := 2)` is a duplicate under the recommended rule; Lean's rule is written out too (new D1112). D1094 now depends on it. |
| §6 Hash claims | The "always a lambda" rule for named method sections is gone: a named section uses the same partial-application shortcut as a positional one (§4.4). D1099 (c)'s "same hashes" claim is removed, and §5.2 separates "same term", "definitionally equal" and "same hash". |
| §7 Field-default rules | §5.1 now states: supplied fields run once and defaults get their values; each default is checked for arbitrary earlier field values (`ok: size = 8 := rfl` fails); omission commits to the default; a helper takes the dependency closure including types; update keeps existing values; patterns are unchanged; "pure" means no abilities and no `Partial`, which in Stitchwort also means it terminates. |
| §8 Default metadata | New §5.2 text: defaults are metadata of the declaration, kept by declaration, not by type hash. Two versions of one type can't meet in one environment (evidence in §5.2), so no conflict policy is needed. Elaborated terms name helpers directly; check-cache keys already cover defaults; JS output depends on them; the compatibility promise is narrowed. |
| §9 JS absence | New §5.3 text: an absent property means "use the default", a present `undefined` means `None`. Defaulted `Option` fields are always present in output (new D1114). Functions can't cross the boundary today, so stage 2b only has "parameter" and "result" directions. |
| Prior art, acceptance | Lean's structure-field defaults added to §3. §7 replaces the broad acceptance statements with ten invariants. |

## As built (stage 2)

Field defaults (§5.1, §5.2) are built as specified, with these build
details (SW-401). The kernel is unchanged: defaults are elaborator sugar.

1. **Syntax.** `field: T := v` in a record, `(field: T := v)` among a
   constructor's explicit fields (`ast::CtorDecl::defaults`, one entry per
   binder). `(a b: T := v)` gives each field its own default, the same
   expression. An implicit field can't have one (`[n: Nat := 0]` is
   `E-PARSE`, "expected `]`"). A default anywhere else is `E-PARSE`: in a
   `def` header, "a parameter can't have a default value", with a note to
   use a record; in a function type or a data type's parameter, "only a
   field can have a default value". The formatter needed no change
   (`crates/fmt/tests/golden/field-defaults.*`).
2. **Helpers** (`crates/elab/src/defaults.rs`). After a data type is
   admitted and its instances are derived, each default is elaborated in
   the empty row, in a context of the type's parameters and the fields
   before it (implicit ones included, so an indexed family's constructor
   works too), against the field's type, then lifted to a definition
   `RangeOptions.step.default`, or for a constructor's field
   `Shape.Circle.id.default`. Rule 5's closure is computed directly on the
   elaborated value and its type (the variables they mention, closed under
   the variables their types mention, in context order), with `lift.rs`'s
   variable collector and substitution. The general draft machinery of
   `lift.rs` isn't used: its frozen metavariables and refinements exist for
   helpers inside a body, while a default's context is only binders. A
   `match` inside a default is lifted by the ordinary machinery, under the
   helper. The type's parameters are implicit parameters of the helper and
   its fields explicit ones.
3. **Metadata.** For each constructor and field, the helper and the
   context levels it takes (`defaults::FieldDefault`), in
   `Elaborator::field_defaults`, keyed by `DataId`: by declaration, never
   by hash (§5.2). The check cache stores the table with the type's unit;
   the format is now 12.
4. **Not in the name table or the library index.** A name with two dots
   can't be written in source (`R.start.default` is dot notation on the
   projection), so the helpers are reached only through the metadata, and
   the library index, which maps names to files, needn't list them. They
   live in the type's file and load with it, as §5.2 asks.
5. **Literals.** `records::literal` and named construction
   (`records::ctor_fields`) leave the path they had when every field is
   given, so those terms and hashes don't move (tested). A literal or
   construction that leaves a defaulted field out goes through
   `defaults::construct`: fields are checked in declaration order, a field
   left out becomes the helper applied to the parameters and to the terms
   of the earlier fields it takes, and a written field a later default
   takes is bound by a transparent `let` unless it's a variable, a
   definition's name, a number, text or a constructor without fields
   (rule 1). A named
   construction that leaves fields out takes the type's parameters from
   the expected type, or makes unknowns for them, and makes unknowns for
   implicit fields, as a positional application does.
6. **Dependencies.** A default's free names are part of its data type's
   references (`module::decl_refs`), so a definition it names is checked
   first, and a definition that both a default names and mentions the type
   is a data/definition cycle, `E-MUTUAL-KIND`.
7. **Errors.** Missing fields: `E-RECORD-FIELD`, noting which fields have
   defaults. Rule 3: `E-TYPE-MISMATCH` with "`size` is left out, so it is
   its default value, `0`". Rule 2: the default's own error (`E-REFL`,
   `E-TYPE-MISMATCH`) with a note that it must work for any values of the
   earlier fields. An operation or a `Partial` call in a default:
   `E-ABILITY` or `E-PARTIAL`, the usual note (add it to the function's
   type) replaced by one saying a default can't perform operations. A
   later field: `E-UNKNOWN-NAME` with a note. A default on an interface's
   method: `E-FIELD-DEFAULT` (new), since every instance gives every
   method; default methods would be a separate design.
8. **Not done here.** The JS boundary (§5.3, stage 2b, SW-402): today an
   exported function taking a record with defaults still needs every field
   from JS, and generated code calls the helpers as ordinary definitions.
   The metadata in item 3 is what 2b's decoder and `.d.ts` input shapes
   need. Signature defaults (§5.4) aren't built.

Tests: `examples/accept/field-defaults.sw`,
`examples/reject/field-default-*.sw` (eight), and in
`crates/driver/tests/named_arguments.rs`:
`changing_a_default_changes_only_the_literals_that_use_it` (invariant 9),
`literals_giving_every_field_keep_their_hashes` and
`a_default_uses_a_written_field_through_a_let` (rule 1). Invariants 7 and
8 are the accept example's "a given field runs once" and the reject
examples `field-default-assumes-default.sw` and
`field-default-left-out-commits.sw`.

## 0. Summary

- **Named arguments** for explicit parameters, `between (low := 1) (high := 5)`,
  spelt like today's named implicit arguments `[x := e]` but with round
  brackets. They are sugar: the call elaborates to the positional term. A
  pure call written with names has the same content hash as `between 1 5`.
- **Default values on record fields** (and constructor fields), not on
  function parameters, at first:
  `type RangeOptions = { start: Nat := 0, stop: Nat, step: Nat := 1 }`, so
  `range { stop = 10 }` works. A function still takes one record, so
  currying, partial application, pipes, sections and function values don't
  change at all. At the JS boundary it is the options object TypeScript
  programmers already write.
- **Defaults in signatures**, `(step: Nat := 1)`, are designed here (§5.4) but
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
   call means. A pure call keeps its hash.
2. A caller can leave out settings that have a sensible default, and a
   library can add a defaulted setting without breaking callers that build
   the value by field name (§5.2 says exactly which uses do break).
3. No silent argument swaps: adding a default or a named argument must never
   make an existing positional call mean something else.
4. Works with what's there: currying and partial application, dot notation
   (`x.f`), method sections (`.f`), pipes (`|>`), implicit and `auto`
   arguments, abilities, proofs, and the JS/TS boundary.

Non-goals:

- Defaults on implicit or `auto` parameters (Idris's `{default 0 lag: Nat}`).
  `auto` already is "a default found by search", and `[ord := …]` already
  overrides it (`docs/syntax.md:504-507`) **[checked]**.
- Default *types*, variadic functions, or Python's `**kwargs`.
- Making parameter names part of a function's type. A function value's type
  stays a plain arrow type, and type equality ignores names (§4.3).

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
binder with that name (`insert_until`, `check.rs:1566-1593`; used at
`check.rs:1106-1113`) **[checked]**. The name comes from the binder in the
function's type (`Value::Pi(x, …)`, compared at `check.rs:1575`), and the
result is an ordinary application term.

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

The defaults-value convention stays useful for named presets
(`RangeOptions.wide`); field defaults describe the ordinary construction.

### 2.3 Related machinery a design must fit

- **Named construction** `C { f = v, … }` (D605 (a), D1085 (a); SW-387).
  Braces right after a constructor name its fields, and a record argument is
  written `C ({ … })` (`docs/syntax.md:292`,
  `docs/proposals/variant-fields.md:460-480`) **[checked]**. That doc left
  Lean's `(name := p)` open as "a reasonable later addition for mixing named
  and positional arguments" (`variant-fields.md:464-465`) **[checked]**.
  After a *function*, braces stay a record literal argument; this note keeps
  that, since §2.2's convention depends on it.
- **Dot notation** puts the receiver in the first parameter of the receiver's
  type, at any position (`docs/syntax.md:289`) **[checked]**.
- **Method sections** `.f a` are `x => x.f a`, or the partial application
  itself when the receiver is last (D506, `docs/syntax.md:958-963`)
  **[checked]**. `dot.rs:505` gives up the partial-application form if any
  argument is named **[checked]**. The reason is mechanical, not semantic:
  the shortcut collects only positional arguments and compares their count
  with the receiver's position (`dot.rs:500-528`) **[checked]**.
- **Pipes**: `x |> f a b` is `f a b x`, with `x` elaborated first
  (`crates/elab/src/pipe.rs:1-3`) **[checked]**. Named arguments are already
  passed through (`pipe.rs:28-35`) **[checked]**.
- **Evaluation order**: arguments are evaluated left to right as written
  (`docs/syntax.md:540`) **[checked]**. §4.5 says exactly what that means
  today for effectful heads, arguments and curried stages.
- **Content hashes leave out binder names** (`crates/core/src/hash.rs:29-33`;
  `Pi` and `Lam` hash only their `icit`, `hash.rs:545-554`) **[checked]**. So
  renaming a parameter doesn't change a function's hash. Hashing doesn't
  identify eta-equivalent terms: `x => f x` and `f` hash differently
  **[checked]** (no eta step in `hash.rs`), although conversion treats them
  as equal (`docs/core.md:202`) **[checked]**.
- **The check cache is keyed by source text** and the keys of imports, not by
  content hash (`docs/proposals/check-cache.md:41-50`, `:148-170`)
  **[checked]**. So when a callee's source changes, every caller is
  re-elaborated (§4.4 says what that does and doesn't catch).
- **The JS boundary** exports an uncurried function whose TypeScript
  parameters are the binder names (`crates/js/src/lib.rs:1005-1018`), and an
  `Option` parameter is `x: T | undefined`, not optional, while a record's
  `Option` field is an optional property `f?: T`
  (`crates/cli/tests/extract.rs:860-870`) **[checked]**. A record parameter
  crosses as a plain object: `render(settings: Settings, count: bigint)` with
  `type Settings = { readonly width: bigint; readonly label?: string }`
  **[checked]** (built with `build --js`). Functions can't cross at all
  ("functions can't cross the JS boundary yet", `lib.rs:409`) **[checked]**.

## 3. Other languages

| Language | Named | Defaults | Notes |
|---|---|---|---|
| Kotlin | `f(x = 1)`, any order | `(x: Int = 0)`, may use earlier params; evaluated only when needed; overriding methods keep the base's defaults | "after the first skipped argument, you must name all subsequent arguments"; no named syntax for Java callees. https://kotlinlang.org/docs/functions.html#named-arguments |
| Scala | `f(x = 1)` | `(x: Int = 0)` | Defaults are compiled to extra methods the call site calls **[unverified]**; a function *value* made from a method loses its defaults **[unverified]**. https://docs.scala-lang.org/tour/named-arguments.html, https://docs.scala-lang.org/tour/default-parameter-values.html |
| Swift | argument labels, required by default | `(x: Int = 0)` | SE-0111 removed labels from function types, and made labels an error on calls through a function value: "If the invocation refers to a value, property, or variable of function type, the argument labels do not need to be supplied. It will be an error to supply argument labels in this situation." https://github.com/swiftlang/swift-evolution/blob/main/proposals/0111-remove-arg-label-type-significance.md |
| Python | `f(x=1)`, keyword-only after `*` | `def f(x=0)` | The default is evaluated once, at definition, so a mutable default is shared between calls. https://docs.python.org/3/tutorial/controlflow.html#default-argument-values |
| OCaml | labels `~x` | optional `?x`, `?(step = 1)` | Labels are part of the type; total applications commute. An optional argument is dropped only when a *later unlabelled* argument is applied, so a function needs a positional parameter after its optional ones; with higher-order functions "the compiler assumes that there are no optional arguments". https://ocaml.org/manual/latest/lablexamples.html |
| Lean 4 (functions) | `f (x := e)`, for any parameter kind | `(x : Nat := 5)` (`optParam`), `(h : p := by tac)` (`autoParam`) | "Parameter names are taken from the function's type", and "the names of the arguments are preserved in the function type", so a partial application's remaining arguments can be named. Naming a later parameter while earlier explicit ones are missing makes a lambda. A named argument wins over an earlier positional one: "If an argument is provided by name, it is used, even if it occurs after a positional argument that could have been used." https://lean-lang.org/doc/reference/latest/Terms/Function-Application/ |
| Lean 4 (structures) | `{ x := 1 }` | `structure S where x : Nat := 0` | "Structure fields may have default values, specified with `:=`"; a field with no default must be given. Unlike this note, a structure pattern that leaves out a defaulted field "only matches the default". Defaults are stored in auxiliary definitions **[unverified]**. https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structure-fields |
| Idris 2 | `f {x = e}` (implicits) | `{default 0 lag : Nat}` on implicits | The docs say defaults are "primarily intended" for proof search, the Fibonacci example is "illustrative only". https://idris2.readthedocs.io/en/latest/tutorial/miscellany.html |
| Agda | `f {x = e}`, implicit and instance arguments only **[unverified]** | none **[unverified]** | https://agda.readthedocs.io/en/latest/language/implicit-arguments.html |
| Haskell | records (`f defaultOpts { width = 80 }`) | the `Default` class | https://hackage.haskell.org/package/data-default |
| Unison | none | none: "use the Optional type … and then provide a default value inside the function body" | https://www.unison-lang.org/compare-lang/unison-for-python-devs/ |
| Roc | records | optional record fields with a default, given in the function's destructuring pattern; spelling has changed between versions **[unverified]** | https://github.com/roc-lang/roc/blob/main/roc-for-elm-programmers.md |
| Elm | records | none; a defaults record and update | **[unverified]** |
| TypeScript | options objects | `x?: T`, `x = 0` (trailing in practice) | An absent property and a present property holding `undefined` are different under `exactOptionalPropertyTypes`. https://www.typescriptlang.org/docs/handbook/2/functions.html#optional-parameters, https://www.typescriptlang.org/tsconfig/#exactOptionalPropertyTypes |

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
   names, and higher-order code needs annotations. Swift took them out, and
   also stopped labels working on function values. Lean keeps names in the
   type but never compares them; this note follows Lean.
4. **Renaming a parameter breaks callers** (Kotlin, Python). It is an API
   change once callers can use names.
5. **Evaluation time of defaults** (Python's shared mutable default).
   Stitchwort values are immutable, so only effects matter (§5.1).

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

### 4.2 Elaboration: matching arguments to parameters

The **head's signature** is the telescope of parameters the names are read
from (§4.3 says where it comes from). For a spine `h a₁ … aₙ`, with a dot
receiver or a piped value if there is one:

1. **Fill slots in written order** (D1112 (a), recommended). Start with no
   parameter filled. A dot receiver fills its parameter first (as today).
   Then take the written arguments left to right:
   - a **positional** argument fills the first explicit parameter that is
     not yet filled;
   - a **named** argument `(x := e)` fills the explicit parameter `x`, or
     `[x := e]` the implicit or `auto` parameter `x`. If `x` is already
     filled, by an earlier positional or named argument or by the receiver,
     it is `E-DUPLICATE-ARGUMENT`. If the signature has no such parameter, it
     is `E-UNKNOWN-NAME`, listing the parameters with their kinds. If the
     bracket is the wrong kind, the D1093 error.
   - A piped value comes last, and fills the first explicit parameter still
     unfilled.

   So, with `def f (x: Nat) (y: Nat): Nat`:

   ```
   f (y := 2) 1       -- f 1 2
   f 1 (y := 2)       -- f 1 2
   f 1 (x := 2)       -- E-DUPLICATE-ARGUMENT: x is already given by 1
   ```

   With this rule a spine can be split anywhere without changing its
   meaning: `(f 1) (x := 2)` is also an error (`f 1` has only `y` left), and
   `(f (y := 2)) 1` is `f 1 2`, as `f (y := 2) 1` is **[inferred]**.

   Lean's rule, D1112 (b), differs only in the third line: all named
   arguments of the spine are placed first, then the positional ones fill
   the rest, so `f 1 (x := 2)` is `f 2 1`, while `(f 1) (x := 2)` is still
   an error.
2. **Implicit and `auto` parameters** not named are inserted as unknowns, as
   today. Named implicits may come in any order (D1094), which removes
   §2.1's order limit; under D1112 (a) a repeated implicit name is a
   duplicate.
3. **Missing explicit parameters.** If, after filling, some explicit
   parameter before the last filled one is still empty, the result is a
   function of the missing ones, in parameter order, as Lean does (D1095):

   ```
   def clampTo (low: Nat) (high: Nat) (value: Nat): Nat := …

   let capped := readings.map (clampTo (low := 0) (high := 100))
   let atMostTen := clampTo (high := 10)       -- low value => clampTo low 10 value
   ```

   Missing explicit parameters after the last filled one are left to
   currying as today: `clampTo 0` is the partial application, not a lambda.
   The lambda's binders keep the parameters' names, so
   `atMostTen (low := 0)` works.
4. **Checking order.** Arguments are checked against their parameters in
   parameter order (later parameter types may mention earlier arguments).
   Effectful arguments are run in written order; §4.5 has the rules.
5. **A missing explicit parameter is rigid.** It is a variable bound by the
   lambda, never an unknown to be solved. So the result must work for every
   value of it. With

   ```
   def use (n: Nat) (xs: Vec Nat n): Nat := …
   def three: Vec Nat 3 := …
   ```

   `use (xs := three)` is an error, not `use 3 three`:

   ```
   E-TYPE-MISMATCH: expected `Vec Nat n`, but this has type `Vec Nat 3`
   note: this call leaves out `n`, so it must work for every `n`.
         To mean `n = 3`, write `(n := 3)`.
   ```

   Missing *implicit* parameters stay unknowns that unification may solve,
   as today. A parameter never switches between the two behaviours.
6. **The result** is the same `Term::App` chain as the positional call
   (wrapped in a lambda for rule 3, and in `bind`s or `let`s for §4.5). When
   the arguments are pure and none is skipped, `between (high := 9) (low := 3)`
   and `between 3 9` are the same term, so the same hash **[inferred]**:
   switching a pure call between styles reruns no tests.

### 4.3 Where the names come from

Names guide elaboration into a positional application, which is then
type-checked as usual. Type equality and unification ignore names, as they
do today (names aren't in the hash, §2.3). The names a call may use come
from the **signature of the head**, which is found syntactically from the
head expression, never from an unknown solved by unification (D1115 (a),
recommended):

| Head | Signature |
|---|---|
| A top-level definition, local definition or constructor | Its declared type: header parameters and the type after the colon |
| A variable bound by a parameter, a lambda binder or a `let` with a type annotation | The annotation |
| A `let` without an annotation whose value is itself a head with a signature (`let g := f`, `let g := clampTo 0`) | That value's signature |
| `(e: T)` | `T` |
| A positional partial application `h a…` | What is left of `h`'s signature (Lean keeps names this way too) |
| A call with skipped parameters (§4.2 rule 3) | The missing parameters, in order |
| Dot notation `x.f` | `f`'s signature without the receiver's parameter |
| A full call of a definition whose declared result type is a function type (`makeCheck() (limit := 3)`) | That declared result type |
| A record field or constructor field of function type (`settings.render (width := 80)`) | The field's declared type |
| Anything else: `if`, `match`, a lambda without annotation, an element taken out of a list, a call whose result type was solved by unification | None |

With no signature, a named argument is `E-UNKNOWN-NAME` with the note "the
parameter names of this function aren't known here; add a type annotation,
as in `let g: (low: Nat) -> (high: Nat) -> Nat := …`". The most common
"anything else" case is an `if` whose branches name their parameters
differently. Today its type is an unknown solved from the first branch
(`check.rs:761-771`) **[checked]**, so its names would be the `then` branch's
by accident. The table rules that out.

Further rules:

- **An annotation decides the names, and never permutes arguments.**
  `let g: (start: Nat) -> (stop: Nat) -> Nat := between` makes `start` the
  name of `between`'s first parameter (`low`), and `g (stop := 9) (start := 3)`
  is `between 3 9`. The same function can be seen through
  `(left: Nat) -> (right: Nat) -> Nat` and `(right: Nat) -> (left: Nat) -> Nat`;
  a call naming `left` then picks a different position in each view. That is
  the contract, not a type error.
- **Synonyms and reduction.** A type synonym is unfolded, and the names are
  those of its body: with `def Picker: Type := [count: Nat] -> (x: Nat) -> Nat`,
  `(h: Picker)` then `h [count := 3] 1` checks today **[checked]**. A type
  computed by a definition gives the names of what it computes to. Both are
  deterministic evaluation, not unification.
- **Anonymous arrows have no names.** `Nat -> Nat` binds `_`
  (`check.rs:746-756`) **[checked]**, which no named argument can spell.
- **Repeated names.** A definition's header can't repeat a name
  (`E-DUPLICATE-PARAMETER`) **[checked]**, but a function type can:
  `(h: (x: Nat) -> (x: Nat) -> Nat)` checks today **[checked]**. A name that
  appears more than once among the explicit parameters a call can still
  fill is `E-AMBIGUOUS` when used ("`x` names two parameters here; pass
  them by position").
- **Names after implicit insertion.** `let g := pick` with
  `def pick [count: Nat] (x: Nat)` inserts the implicit at the `let`, so
  `g [count := 3] 1` is `E-UNKNOWN-NAME` today **[checked]**. Explicit
  parameters aren't inserted, so `let g := between` keeps `low` and `high`.
- **Constructors**: `Circle (radius := 1) (id := "a")` works as for any
  function (D1096). It complements D605's braces: `Circle { radius = 1 }`
  builds a whole `Circle`, filling omitted fields from their defaults (§5),
  while `Circle (radius := 1)` is a partial application that still waits for
  every other explicit field, defaulted ones included:

  ```
  type Shape = Circle (radius: Nat) (id: Text := "anonymous") | …

  Circle { radius = 1 }     -- a Shape: id is "anonymous"
  Circle (radius := 1)      -- a function: id => Circle 1 id
  ```

Lean is the precedent: it keeps names in function types, uses them after
partial application, and never compares them. Swift's SE-0111 is not: it
makes labels an error on calls through a function value (§3).

### 4.4 Interaction with the rest of the language

| Feature | Behaviour |
|---|---|
| Currying / partial application | `f a` stays a partial application. A named argument after missing positional ones gives a lambda (§4.2 rule 3). |
| Dot notation `x.f` | The receiver fills its parameter first; named arguments then fill theirs. Naming the receiver's parameter too is `E-DUPLICATE-ARGUMENT`. `p.distanceTo (other := q)` is fine. |
| Sections `.f (x := e)` | Named arguments are matched to parameters first (§4.2), then the section is elaborated as a positional one would be: if the receiver lands in the last explicit parameter and every explicit parameter before it is filled, it is the partial application `T.f a…` (D506), with the arguments in parameter order; otherwise `y => y.f (x := e)`. So `.split (separator := ',')` is `Text.split ','`, the same term as `.split ','`. Only `dot.rs:500-528` changes: it collects named arguments too. As today, an argument that performs an operation makes the shortcut fail and the section stays a lambda (`dot.rs:536-551` restores and returns `None` on an error) **[checked]**, for positional and named alike. |
| Pipes | `5 \|> clampTo (low := 0) (high := 10)` is `clampTo 0 10 5`: the piped value is the last positional argument, filling the first explicit parameter not otherwise given. |
| Implicit / `auto` | Unchanged; `[x := e]` for them, in any order (D1094). |
| Abilities | §4.5. |
| Proofs | A theorem statement may use named calls; the term is the positional one, so `rfl` and rewriting see no difference. |
| Hover, errors, `show` | Terms print positionally; hover on a named argument shows the parameter. |
| JS | Nothing changes: JS calls are positional, and the `.d.ts` already uses the binder names. |

**Renaming a parameter is now an API change.** Because the check cache is
keyed by source (§2.3), a caller is always re-elaborated against the new
names, so nothing stale is reused. But not every breaking rename gives a
diagnostic:

- A call by a name that no longer exists is an error (`E-UNKNOWN-NAME`).
- A change that keeps the names but moves them changes what a named call
  means, silently. With

  ```
  -- before
  def subtract (a: Nat) (b: Nat): Nat := a - b
  -- after
  def subtract (b: Nat) (a: Nat): Nat := b - a
  ```

  the edit is a pure renaming: the function computes the same thing from
  the same positions, and its hash is unchanged (binder names aren't
  hashed). Positional `subtract 7 2` is `5` before and after. But
  `subtract (a := 7) (b := 2)` still elaborates, because both names still
  exist: before it was `subtract 7 2`, which is `5`; after, `a` is the
  second parameter, so it is `subtract 2 7`, which is `0`. No diagnostic is
  possible: the call is well typed both times.
- The opposite edit (swap both the names and the positions, keeping the
  body's meaning) leaves named callers right and positional callers wrong,
  silently, as it does today.

So the accurate guarantee is: renaming a parameter invalidates the
callers' cached checks; calls using removed names fail; changes that keep
the names but alter their positions can still change the meaning of named
calls. A lint for renamed or reordered public parameters is a possible later
addition (§9).

### 4.5 Run order

This section is the effect specification. It only matters in a
**computation** (code checked against an ability row). In pure code an
effectful call is refused unless it can perform nothing
(`docs/syntax.md:540`, `docs/core.md:292`) **[checked]**, so a named call
there is only a reordering of pure values.

**What happens today** (`comp_app`, `crates/elab/src/effects.rs:1539-1652`)
**[checked]**:

1. The head runs first if it isn't a plain name (an expression such as
   `(readFunction())`), or, for dot notation, the receiver
   (`effects.rs:1564-1575`). A piped value runs before both
   (`pipe_call`, `effects.rs:1687`).
2. Every argument that may perform runs next, in written order, each bound
   to a fresh variable (`run_first`, `effects.rs:1738-1749`). Arguments that
   can't perform are left in place.
3. Then the head is applied one argument at a time. When a partial
   application is itself a computation, as for
   `f: (x: Nat) -> {IO} ((y: Nat) -> (z: Nat) -> Nat)`, it runs there and the
   call continues with its result (`effects.rs:1588-1601`).
4. The bound variables are sequenced with `bind`. If the call's result type
   mentions one of them, it is `E-EFFECT-ESCAPE` (`wrap`,
   `effects.rs:1753-1768`).

A probe confirms the order. With `say n` printing `arg n` and returning `n`,
and `f` above printing `stage x=…` before returning its function
**[checked]**:

```
def main(): {IO} () :=
  let r := f (say 1) (say 2) (say 3)    -- prints arg 1, arg 2, arg 3, stage x=1
  let g := f 10                         -- prints stage x=10, once
  IO.print "g=${g 1 2}"                 -- no stage printed
  IO.print "g=${g 3 4}"                 -- no stage printed
```

So effectful functions may return functions, and a partial application runs
its stage when it is made. But **no argument runs between two stages**: all
effectful arguments run before the first stage. The worry that naming might
move an argument across a stage can't arise, because the stages already run
after every argument.

**Rules for named calls.** They keep steps 1 to 4 and add:

- **R1. Written order.** Step 2 uses the order the arguments are written in
  the source, named or not. Steps 1 and 2 together are: piped value, then
  head or receiver, then arguments as written.
- **R2. Stages in parameter order.** Step 3 applies the arguments in
  parameter order, as the positional call would.
- **R3. Skipped parameters.** For a call with missing explicit parameters
  (§4.2 rule 3), let `p` be the first missing one. The application up to
  `p` happens outside the lambda, running any stage it reaches, as
  `let g := f 10` does. The lambda binds the missing parameters and applies
  the rest; a stage reached after a missing parameter runs each time the
  lambda is called, as it would in the hand-written `y => g y 3`. So
  `f (x := 1) (z := 3)` is

  ```
  let g := f 1        -- stage x=1 runs now, once
  y => g y 3
  ```

  never `y => f 1 y 3`, which would run the stage on every call.
- **R4. Once, outside.** The piped value, the head or receiver, and every
  effectful supplied argument run once, outside the lambda, at the call
  (steps 1 and 2). So `let g := (readFunction()) (high := 10)` runs
  `readFunction()` once and is `let h := readFunction(); low => h low 10`.
  Arguments that can't perform are elaborated inside the lambda, where the
  missing parameters are in scope; their inserted implicits may mention
  them (`use (xs := emptyVec)` with `emptyVec: [n: Nat] -> Vec Nat n` is
  `n => use n (emptyVec [n := n])`).
- **R5. Dependencies win over hoisting; conflicts are refused** (D1113 (a),
  recommended). A computation that runs in step 1 or 2 may need, once
  elaborated, a missing parameter or the result of a computation written
  after it. The dependency can be invisible in the source: it can come
  from an inserted implicit argument, an `auto` dictionary or a solved
  unknown. Then the call is refused with `E-EFFECT-ORDER`, naming the
  computation and what it needs. Examples, with
  `readVec: [n: Nat] -> () -> {IO} (Vec Nat n)` and
  `readNat: () -> {IO} Nat`:

  ```
  use (xs := readVec())                        -- needs the missing n
  use (xs := readVec()) (n := readNat())       -- needs n, read after it
  ```

  ```
  E-EFFECT-ORDER: `readVec()` runs first, where it's written,
                  but its type needs `n`, which comes later
  note: run them in the order you need, then call:
          let n := readNat()
          use (xs := readVec()) (n := n)
  ```

  The check is on the elaborated term, so it sees inserted implicits. Today
  the same situation in a positional call is already refused, but with an
  unhelpful message: an earlier argument's unknowns are created before later
  results are bound, so they can't be solved with them. With
  `def sized [n: Nat] (xs: Vec Nat n) (k: Nat) (same: n = k): Nat`,
  `sized (readVec()) (say 2) rfl` fails with `E-REFL` "`?2 _` and `%2`
  aren't equal" **[checked]**, and `use (say 2) (readVec())`, where the
  dependency runs first, checks and prints `arg 2` then `readVec`
  **[checked]**. The new work is detecting this case and reporting it
  clearly; the same diagnostic should then replace today's message for
  positional calls.

**The effect-trace invariant.** The *trace* of a call is the sequence of
operations it performs. Adding names to a call's arguments, without changing
the written order or how the call is bracketed, leaves its elaborated term,
and so its trace, unchanged. Reordering named arguments changes only the
order in which the effectful arguments run, which is the new written order.
Stages run as in the positional call, after all the arguments. A skipped
parameter runs the stages before it once, at the call (R3).

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
- **Literals.** A record literal, or a named construction, may leave out
  fields that have a default. A field without one is still required
  (`E-RECORD-FIELD`, as today). Positional construction `MkRange 0 10 1`,
  and `Circle (radius := 1)` (§4.3), still give every field, so no existing
  call changes meaning (goal 3).
- **Elaboration.** Each default becomes a generated definition, a *helper*,
  whose parameters are the type's parameters and the earlier fields it needs
  (below). It is lifted the way a `where` function is lifted to `f.go`
  (`docs/syntax.md:199`). A literal that leaves a field out calls the helper,
  so `{ stop = 10 }` is `MkRangeOptions RangeOptions.start.default 10
  (RangeOptions.step.default)` (the generated names are a stage 2 detail;
  they must be in the library index, §5.2).

The rules that make this precise:

1. **Supplied fields run once, and defaults get their values.** With
   `type R = { x: Nat, twice: Nat := x + x }`, the literal `{ x = readNat() }`
   is `let x := readNat(); MkR x (R.twice.default x)`, never
   `MkR readNat() (R.twice.default readNat())`. In a computation, record
   fields already run in written order and are then built from their
   results (`comp_compound`, `effects.rs:1782-1793`; `docs/syntax.md:296`)
   **[checked]**, so this reuses that path. In pure code, a supplied field
   that a default uses and that isn't already a variable or a literal is
   bound by a transparent `let`, so it isn't computed twice; a pure `let` is
   transparent to the checker (`docs/syntax.md:13`) **[checked]**.
2. **Each default is checked for arbitrary earlier field values.** The
   helper takes the earlier fields as parameters of their declared types, so
   the default can't assume an earlier default was used. This must fail:

   ```
   type Bad = {
     size: Nat := 8,
     ok: size = 8 := rfl
   }
   ```

   because a caller may give `size = 3`. This works, since it uses the
   actual `size`:

   ```
   type Sized = {
     size: Nat := 8,
     cells: Vec Bool size := Vec.replicate size false
   }
   ```

   Lifting the default to a helper with the earlier fields as parameters
   gives this rule for free **[inferred]**: `def Bad.ok.default (size: Nat):
   size = 8 := rfl` is an ordinary definition that fails to check.
3. **Leaving a field out commits to its default.** No inference: with
   `size: Nat := 0`, `{ cells = threeCells }` is a type mismatch
   ("`cells` should be a `Vec Bool 0`, since `size` is left out and defaults
   to `0`"), not `size = 3`. Otherwise defaults would be a hidden second
   kind of implicit argument.
4. **Helpers are transparent.** A later field's type must see the value a
   default gives: `{ cells = Vec.replicate 8 false }` for `Sized` needs
   `Sized.size.default` to compute to `8`. A helper is an ordinary
   definition, not folded by name, so it unfolds when applied to all its
   arguments (`docs/core.md:197`) **[checked]**.
5. **A helper's parameters are the dependency closure of the elaborated
   default and its type**, not just the fields the written expression
   mentions. A default mentioning `xs: Vec a n` needs `a` and `n`; a proof
   default needs every field its proposition mentions. This is ordinary
   lifting of a local definition (as `where` and `match` helpers are
   lifted) and must reuse that machinery.
6. **Update keeps existing values.** `{ r | a = 5 }` for
   `type R = { a: Nat, b: Nat := a + 1 }` keeps `r.b`; a default is a
   construction recipe, not a computed property. The existing update rule
   still applies: a later field whose type mentions a replaced one must be
   replaced too (`E-RECORD-UPDATE`, `docs/syntax.md:290`) **[checked]**; a
   default doesn't waive it.
7. **Patterns are unchanged.** A record pattern without `..` names every
   field, and `..` matches any values. Unlike Lean (§3), leaving out a
   defaulted field in a pattern never means "matches only the default".
8. **What a default may use** (D1100): earlier fields and the type's
   parameters, and anything in scope at the declaration.
9. **"Pure" means elaborated in the empty row, with no `Partial`.** In
   Stitchwort that also means it terminates: every definition that isn't
   `Partial` passes the kernel's termination check
   (`docs/core.md:150`, `:267`) **[checked]**. So when a default runs, and how
   often, can't be observed. A default may still be a function that
   performs operations when called (`onDone: Nat -> {IO} () := n => IO.print
   "done"`): building that function performs nothing.
10. **`==`, `show`, proofs** are unchanged: a value always has every field.
    Only literals get shorter.

Why fields first: a function still takes one value of a declared type, so
currying, partial application, pipes, sections, function values and `auto`
need no new rules at all. It improves §2.2's convention rather than adding a
second one, and it is the TypeScript options-object idiom (§5.3).

### 5.2 Defaults and identity

Should a default be part of what a type *is*? (D1099)

Recommended: **no**. The type's hash covers its fields' names and types as
now (`hash.rs:29-33`) **[checked]**. The default lives in its helper, which has
its own hash, and every literal that uses it refers to the helper.

**Three different properties**, which the old version of this note blurred:

- A pure named call and the positional call with the same arguments are
  **the same term**, so they have the same hash (§4.2 rule 6).
- A literal that leaves a field out is **definitionally equal** to one that
  gives the default's value: `MkRangeOptions RangeOptions.start.default 10 …`
  and `MkRangeOptions 0 10 …` are equal to the checker after unfolding the
  helper (rule 4).
- Those two **don't have the same hash**: they are different terms.

Consequences:

- changing a default changes the helper's hash, and so the hash of each
  literal that left that field out, and of nothing else, so exactly those
  tests rerun (the test cache is keyed by the test's content hash,
  `docs/proposals/check-cache.md:34-38`) **[checked]**;
- a literal that gave every field is unaffected;
- two types that differ only in defaults are still two different types,
  because data types are nominal (`hash.rs:31-33`) **[checked]**.

**Where defaults are kept, and how the elaborator finds them.** A default is
metadata of the declaration: for each field of each constructor, the helper
to call, if any. It is kept with the declaration (the `DataId` and its
constructors), not in a table keyed by type hash. When a literal is checked
against `RangeOptions`, the elaborator already knows which declaration that
is (`Value::Data(id, …)`), so it finds that declaration's helpers. The
elaborated literal names the helper directly (`Term::Def`), so running or
checking it later never looks up "the current default".

The reviewer asked what happens when two versions of one type, differing
only in a default, meet in one program. That can't happen in Stitchwort
today:

- a project is one set of namespaces plus the embedded library; there is no
  package system or versioned dependency (`docs/projects.md`) **[checked]**;
- the library index rejects any full name declared twice, before any user
  code is checked (`docs/proposals/std-library.md:309-312`) **[checked]**;
  in a project, a name declared twice in one namespace is `E-DUPLICATE`,
  one namespace can't add to another (`E-FOREIGN-NAMESPACE`), and the
  library's namespaces are reserved (`docs/projects.md:98-112`)
  **[checked]**;
- the elaborator refers to a data type by its `DataId`, one per declaration
  (`crates/core/src/globals.rs:358-372`) **[checked]**, never by hash.

So each type has exactly one declaration, and one set of defaults, in any
elaboration. No conflict policy is needed now. If a package system with
several versions of one library is ever added, defaults must be looked up by
declaration (as above), never by type hash, and that design will need a
conflict rule then.

**What has to track defaults:**

- **Check cache.** A namespace's key covers the full text of its files and
  the keys of everything it imports (`check-cache.md:148-170`) **[checked]**.
  Defaults are written in the declaring file's text, so changing one changes
  that namespace's key and every importer's. The cache entry must store the
  default metadata with the declaration, which is a cache format change
  (item 1 of the key, the format version).
- **Library index and lazy loading.** Helper names are generated names, so
  the index's declaration-collection phase must list them, as it lists
  constructors and record fields (`std-library.md:304-308`) **[checked]**.
  They live in the type's own file, so they load with it.
- **JS output.** A generated decoder runs the default helpers, and a field's
  optionality in the `.d.ts` depends on whether it has a default (§5.3). So
  `build --js` output depends on the defaults even when no core type
  changes. There is no cache in `crates/js` (no match for "cache" in
  `crates/js/src`) **[checked]**: every build regenerates from the current
  metadata. The `.d.ts` snapshot tests in `crates/cli/tests/extract.rs` must
  include a type with defaults so a change shows up there.

**What stays compatible, narrowly:**

- **Changing a default** is source compatible. It changes the meaning of
  every literal that left that field out (after re-elaboration), and the
  behaviour of JS callers that leave it out. Nothing else changes.
- **Adding a field with a default** keeps record literals and named
  construction compiling. It doesn't keep everything: positional
  constructor calls get one argument short, so an old full application
  becomes a partial one (usually a type error later); patterns that name
  every field without `..` become `E-RECORD-FIELD`; the type's hash, and the
  hash of everything that mentions it, changes.
- **Removing a default** breaks every literal that left the field out.

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

**Absence versus `None`.** Today a record's `Option` field is an optional
property: on input, a missing property and a property holding `undefined`
both mean `None` (`lib.rs:1635`), and on output `None` is left out
(`lib.rs:1725`; `docs/syntax.md:348`) **[checked]**. A defaulted `Option` field
needs three meanings:

```
type Config = {
  colour: Option Text := Some "blue"
}
```

| Input | Meaning |
|---|---|
| `{}` | the default, `Some "blue"` |
| `{ colour: "red" }` | `Some "red"` |
| `{ colour: undefined }` | `None` |

The rule (D1114 (a), recommended):

- **Input:** an absent own property asks for the default; a present property
  is decoded as given, so `undefined` is `None`. The decoder can already
  tell the two apart: `own` returns `MISSING` for an absent property and the
  value otherwise (`lib.rs:1431-1435`) **[checked]**. For a defaulted field
  that isn't an `Option`, a present `undefined` is refused, as any wrong
  value is.
- **Input type:** a defaulted `Option T` field is `colour?: T | undefined`.
  The `| undefined` matters: under `exactOptionalPropertyTypes`, `colour?: T`
  doesn't allow writing `undefined`, and the existing `tsc` checks use that
  flag (`crates/cli/tests/extract.rs:145`; `docs/syntax.md:348`)
  **[checked]**.
- **Output:** a defaulted `Option` field is always present, with `None` as
  `undefined`: `readonly colour: string | undefined`. Otherwise encoding a
  `Config` holding `None` and decoding it again would give `Some "blue"`.
  `Option` fields without a default keep today's encoding (absent for
  `None`, `nick?: string`), since for them absence and `None` mean the same.

**Direction.** Functions can't cross the boundary (`lib.rs:409`)
**[checked]**, so a value is only ever passed in (an export's parameter) or
returned (its result); there are no callbacks whose arguments go the other
way. So the rule is simply: parameters use the input shape, results use the
complete shape. It must be applied all the way down: a type that contains a
defaulted record anywhere (a field, a list element, a constructor field, an
`Option`, a `Map` value) needs its own input shape too, `JobInput` with
`options: RangeOptionsInput`. If functions are ever allowed to cross, the
shapes must follow each position's direction (a callback's parameter is an
output, its result an input), and that is a separate design.

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
4. Identity and elaboration as in §5.2: a helper per default, taking the
   earlier parameters (with §5.1's rules 1 to 5); the function's hash doesn't
   include it.
5. **JS**: an exported function's trailing defaulted parameters become
   optional, `range(start: bigint, stop: bigint, step?: bigint)`; a
   defaulted parameter followed by a required one is `T | undefined`.

Rule 2 makes a bare `range` mean the two-argument function, which is the
behaviour to check with users before building; Lean makes a similar choice
but **[unverified]** in its details for bare names.

## 6. Interactions checked against each option

### 6.1 Proofs and dependent types

Named arguments change no terms, so proofs are untouched. A default may
mention earlier fields, and a later field's type may mention a defaulted one
(`Sized` in §5.1): the literal fills the default before checking what
follows, and the helper unfolds (§5.1 rule 4). A proof field may have a
default too (`ok: step > 0 := …`), written as a term, and checked for every
value of the earlier fields (§5.1 rule 2); finding it by `auto` instead is a
possible later addition, not proposed.

### 6.2 `auto` and implicits

Out of scope for defaults (§1). Named implicits gain any order (D1094).

### 6.3 Errors and tooling

- Unknown name: `E-UNKNOWN-NAME`, listing the parameters with their kinds,
  or saying the names aren't known here (§4.3).
- A parameter filled twice: `E-DUPLICATE-ARGUMENT` (new), pointing at both.
- A name used by two parameters: `E-AMBIGUOUS` (§4.3).
- A missing explicit parameter that an argument's type would fix:
  `E-TYPE-MISMATCH` with the note of §4.2 rule 5.
- A computation that would run before what it needs: `E-EFFECT-ORDER` (new,
  §4.5 R5).
- **What is still awaited.** When a call with skipped parameters, or any
  partial application, meets a type error because it is a function, the
  note names what remains: "this expression is a function still waiting for
  `low` and `value`".
- Missing required field: `E-RECORD-FIELD`, as now, noting which fields have
  defaults. Leaving out a field whose default doesn't fit a later field:
  `E-TYPE-MISMATCH` with a note naming the default (§5.1 rule 3).
- The language server can complete parameter and field names after `(` or
  `{`, and hover shows defaults.

### 6.4 Effects

Named arguments: §4.5. Field defaults: supplied fields run once, in written
order, and defaults are pure, so when they run doesn't matter (§5.1 rules 1
and 9; no Python-style shared state, §3 item 5).

## 7. Recommendation, staged plan and acceptance

Build named arguments, then field defaults; keep signature defaults as a
later, separate decision. Record-based defaults give most of the value with
no new rules for function types, and match both D605's braces and the
TypeScript boundary.

| Stage | What | Lane | Cost |
|---|---|---|---|
| 0 | Document today's convention (a `T.defaults` value and `{ T.defaults \| … }`) in `docs/syntax.md` and the library guide; no compiler change | Sonnet | small |
| 1 | Named explicit arguments `(x := e)`; any-order `[x := e]`; slot filling (D1112); the signature rules (§4.3); lambda for skipped parameters with rigid binders; run order R1 to R5 and `E-EFFECT-ORDER`; dot, section and pipe cases; errors | **Opus** (application spine in `check.rs`, `pipe.rs`, `dot.rs`, `effects.rs`) | medium |
| 1b | Formatter, language-server completion and hover for parameter names; examples and docs | Sonnet; examples DeepSeek | small |
| 2 | Field defaults on records and constructors: syntax, helpers (§5.1 rules 1 to 9), literals and named construction, default metadata in the cache format and the library index | **Opus** | medium |
| 2b | JS boundary: input shapes (all the way down), decoder fills defaults, absence rule and `Option` output (D1114), `.d.ts` snapshots, `tsc --strict --exactOptionalPropertyTypes` check | Sonnet | small to medium |
| 3 | (Only if D1097 says so) signature defaults per §5.4 | **Opus** | medium to large |

**As built (stage 1b).** The formatter needed no change (tokens keep their
spacing; `crates/fmt/tests/golden/named-arguments.*` holds the round trip
and idempotence case). The language server (`crates/cli/src/completion.rs`)
completes names after `(` or `[` from the text before the cursor and the
function's parameters with their names (`NavSymbol::signature`, since the
printed type leaves out the names nothing depends on); the function is found
by its written name among the file's last published references, so it works
while the call doesn't parse. It covers definitions, not constructors,
local functions or method receivers (a dot call also offers the receiver's
parameter). Hover on a name in `(x := e)` shows the parameter's type: the
elaborator notes the name as a local that is its own binder
(`Elaborator::note_parameter`). Go to definition on the name is not offered:
a function type's binders carry no source position.

**As built (stage 1 leftovers, SW-404).** Three things stage 1 left undone:

1. *Positional `E-EFFECT-ORDER`* (§4.5 R5, last paragraph). A failed call
   that ran computations first, named or not, is diagnosed by
   `effects::effect_order`. Besides R5's two cases it finds an implicit
   parameter (an unknown made before later results are bound) that another
   parameter's type relates to a parameter a later computation gives:
   `sized (readVec()) (say 2) rfl` is now "its type needs `n`, which is
   found from `k`, which comes later", with a note to `let k := …` first
   (`examples/reject/effect-order-positional.sw`).
2. *Stages after a skipped parameter* (R3). Stage 1 refused them; now a
   stage reached after a missing parameter runs inside the lambda, each time
   it's called (`named::bind_missing`, `effects::Stages`): the lambda's body
   is a computation in the stage's row, and a missing parameter after it is
   a lambda in that computation's result, so `staged (z := 3)` has type
   `(x: Nat) -> {Log} ((y: Nat) -> Nat)`. Later stages run in the first
   one's row. A call with no stage after a missing parameter gives the same
   term as before.
3. *Names after a computed result type* (§4.3, "Synonyms and reduction").
   The signature walk stops at a type that can't compute with the
   parameters as variables (`Scaler n`). When a call names a parameter the
   signature lacks, `named::split` matches the arguments it can, and if
   that fills every explicit parameter, the call is elaborated as
   `(f a…) (rest…)`, which means the same (rule 1); the rest's names come
   from the computed type. Dot notation's receiver path doesn't split
   (`examples/accept/named-arguments.sw`, "names after a computed result
   type").

**Acceptance invariants.** Each is a test (an accept or reject example, or
a differential test), in the stage shown:

1. (Stage 1) Naming a call's arguments, without changing the written order
   or the bracketing, gives the same elaborated term, so the same hash and
   the same effect trace. Checked by rewriting calls in `examples/accept`
   with names.
2. (1) Reordered named arguments that perform independent operations run
   them in written order; the stages of a curried effectful function run
   after all of them, as in the positional call.
3. (1) A named call that skips a parameter runs an effectful head, receiver,
   piped value and supplied arguments once, at the call, and the stages
   before the first skipped parameter once (R3, R4). A supplied computation
   that needs a skipped parameter or a later result is `E-EFFECT-ORDER`
   (R5).
4. (1) A missing explicit parameter is never inferred: `use (xs := three)`
   is an error with the `(n := 3)` note.
5. (1) A pure named method section and its positional spelling elaborate
   to the same term (`.split (separator := ',')` and `.split ','`).
6. (1) Names never depend on unification order: an `if` whose branches name
   parameters differently has no names (§4.3); `f 1 (x := 2)` follows D1112.
7. (2) A supplied field that performs an operation, and that a default uses,
   runs once.
8. (2) A default that assumes an earlier default was used is refused
   (`Bad` in §5.1); leaving a field out commits to its default.
9. (2) Changing a default changes the hashes of exactly the literals that
   left that field out (and so reruns their tests) and the generated
   decoders; a literal that gives every field keeps its hash.
10. (2b) A JS round trip keeps an explicit `None` in a defaulted `Option`
    field whose default isn't `None`; an absent property gets the default.

(The reviewer's ninth invariant, "conflicting default metadata can't
silently overwrite itself", is replaced by §5.2's evidence that two sets of
defaults for one type can't meet; metadata is kept per declaration.)

## 8. Decisions for Matt

**Decided (Matt, 24 Oct 2026):** D1092 to D1101 and D1112 to D1115, each as
recommended below.

**D1092. Should explicit arguments be nameable at call sites?**
(a) **[Recommended]** Yes, `f (x := e)`, sugar over positional application
(§4). (b) Yes, but with the existing square brackets for every kind,
`f [x := e]`, losing the visible explicit/implicit distinction. (c) No;
records only.
Reason: the readability goal, and it is Lean's proven design.

**D1093. Must the bracket match the parameter's kind?**
(a) **[Recommended]** Yes: `(x := e)` for explicit, `[x := e]` for implicit
and `auto`, as in declarations; the wrong one is an error saying which to
write. (b) Either bracket names any parameter.
Reason: the call shows what kind of parameter it fills, as declarations do.

**D1094. Order of named arguments.**
(a) **[Recommended]** Any order, mixed freely with positional arguments,
filling parameters by the rule chosen in D1112; this also applies to
`[x := e]` (fixing §2.1's order limit). (b) Named after positional only
(Kotlin-like). (c) Declaration order only (today's rule for implicits).
Reason: order freedom is most of the point; D1112 removes the ambiguity in
mixed calls.

**D1095. Naming a later parameter while an earlier one is missing.**
(a) **[Recommended]** Gives a function of the missing ones, as Lean does:
`clampTo (high := 10)` is `low value => clampTo low 10 value`. Missing
explicit parameters are rigid (never inferred, §4.2 rule 5), effectful parts
run once at the call (§4.5), and errors say what is still awaited.
(b) An error ("`low` isn't given"), so a forgotten argument is caught at the
call rather than as a type mismatch later.
Reason: currying already turns a short call into a function; good notes
deal with the confusion better than a ban.

**D1096. Constructors: named arguments as well as D605's braces?**
(a) **[Recommended]** Yes, one rule for every function; braces build a whole
value (with defaults), `(x := e)` can name some fields and leave a function
of the rest, defaulted fields included (§4.3). (b) Braces only for
constructors, so there is one spelling.
Reason: one application rule everywhere.

**D1097. Defaults: where?**
(a) **[Recommended]** On record and constructor fields now (§5.1);
signature defaults (§5.4) decided again after stage 2 is in use.
(b) Both now. (c) Neither: document the `T.defaults` convention only.
Reason: field defaults need no new rules for currying or function values.

**D1098. How a default is written.**
(a) **[Recommended]** `step: Nat := 1`, since `:=` gives a value everywhere
else (`let`, `def`, named arguments), and Lean writes structure defaults so.
(b) `step: Nat = 1` as in Kotlin, Scala and TypeScript; but `=` is only
equality in Stitchwort (`docs/syntax.md:165`). (c) Idris's
`default 1 step: Nat`.
Reason: `=` already means equality.

**D1099. Is a default part of a declaration's identity (its hash)?**
(a) **[Recommended]** No: each default is its own generated helper, kept as
metadata of its declaration (by declaration, not by type hash), and the
literals that rely on it refer to it, so changing a default changes exactly
those literals' hashes (§5.2). (b) Yes: changing a default changes the
type's hash and so everything that mentions the type. (c) No, and the
default's value is copied into each literal instead of referenced. The
dependency behaviour is similar to (a), but the hashes differ from (a)'s,
and there is no shared definition to hover or prove things about.
Reason: precise test reruns, and one place that defines each default.

**D1100. What may a default refer to?**
(a) **[Recommended]** Earlier fields (or parameters) and type parameters,
pure only (no abilities, no `Partial`), and checked for arbitrary values of
the earlier fields (§5.1 rules 2, 8, 9). (b) Constants only (no dependence
on other fields).
Reason: dependent defaults (`cells := Vec.replicate size false`) are useful,
and rule 2 keeps them sound.

**D1101. TypeScript shape for a record with defaulted fields.**
(a) **[Recommended]** A second alias `RangeOptionsInput` with `?` on the
defaulted fields, used for parameters, and propagated to every type that
contains such a record; `RangeOptions` stays complete for results. Absence
follows D1114. (b) One alias with `?` on defaulted fields everywhere;
simpler, but TypeScript readers of results must handle a missing field that
is never missing.
Reason: results keep their guarantees.

**D1112. In a mixed call, can a later name take a slot an earlier
positional argument filled?** (`def f (x: Nat) (y: Nat)`)
(a) **[Recommended]** No: arguments fill slots in written order, and a
positional argument takes the first slot still free, so `f 1 (x := 2)` is
`E-DUPLICATE-ARGUMENT`, while `f (y := 2) 1` and `f 1 (y := 2)` are both
`f 1 2`. (b) Yes, as Lean: names are placed first, then positional
arguments fill the rest, so `f 1 (x := 2)` is `f 2 1`, although
`(f 1) (x := 2)` is an error.
Reason: (a) catches a likely mistake, and a call means the same however it
is bracketed.

**D1113. A computation that would have to run before something it depends
on** (`use (xs := readVec())`, where `readVec`'s length is the missing `n`).
(a) **[Recommended]** Refuse it with `E-EFFECT-ORDER`, checked on the
elaborated term (inserted implicits included), with a note showing how to
order it with `let`s (§4.5 R5). (b) Move the computation after what it
needs, or inside the lambda, so it runs later or on every call (breaks
"runs where it's written, once"). (c) Refuse every named call that reorders
or skips around an effectful argument, whether or not it depends on
anything (simplest, but refuses harmless calls).
Reason: keeps written order and run-once, and refuses only the calls that
can't have both.

**D1114. JS: absence and `None` for a defaulted `Option` field**
(`colour: Option Text := Some "blue"`).
(a) **[Recommended]** An absent property means the default, a present
`undefined` means `None`; the input type is `colour?: string | undefined`;
on output a defaulted `Option` field is always present (`None` as
`undefined`). `Option` fields without a default keep today's encoding.
(b) As (a), but every `Option` field in a record becomes always present on
output (one rule for all, but changes D582's encoding and every existing
snapshot). (c) Refuse to export a type with a defaulted `Option` field
whose default isn't `None` (`E-EXPORT`). (d) Absent and `undefined` both mean
the default, so JS can't pass `None` at all.
Reason: (a) can express all three meanings, round-trips, and changes nothing
that exists.

**D1115. Where do the names for a call come from?**
(a) **[Recommended]** From the head's signature, found syntactically
(§4.3's table: declarations, annotations, aliases by `let`, partial
applications, declared result and field types); anything else, such as an
`if` with differently named branches, has no names and needs an annotation.
(b) From whatever function type the elaborator holds for the head,
including one solved by unification (more calls work without annotations,
but names can depend on which branch was checked first, `check.rs:761-771`).
Reason: names must never depend on unification order; the rule can be
loosened later without breaking anything.

## 9. Risks

- **Two ways to write a call** (positional and named). The formatter keeps
  what was written; nothing forces either.
- **Parameter names become API.** Re-elaboration catches removed names but
  not moved ones (§4.4). A library may want a lint for renamed or reordered
  public parameters later.
- **Lambda from a skipped parameter (D1095 (a))** can turn a forgotten
  argument into a confusing later type error. The note names what is still
  awaited (§6.3).
- **`E-EFFECT-ORDER` is a new kind of error** that users may not expect from
  a reordering. The note shows the `let` form; the same check improves
  today's message for positional calls (§4.5).
- **Generated helpers** add names the library index and lazy loading must
  know about, as shared-field projections did (`variant-fields.md`, §12.1),
  and default metadata enters the check-cache format. Stage 2 carries that
  risk.
- **A future package system** with two versions of one library would need a
  conflict rule for defaults (§5.2). Not a risk today.
