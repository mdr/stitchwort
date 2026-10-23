# Proposal: attributes, `@[…]`, starting with the JavaScript wire format

**Status:** draft 1, 23 October 2026, for external review. Ticket SW-341, decision D590.
Design-review gate: nothing is implemented. Decisions D597 to D599 ([§11](#11-decisions))
are for Matt. Written against commit `e9829f37`. Related: DESIGN.md §12 (JavaScript
extraction), [records.md](records.md) §11 (records at the boundary),
[check-cache.md](check-cache.md), and two lanes running in parallel: SW-339 (D582, `Option T`
as an optional property) and D583 (pending: refuse `null` by default, opt in to it).

Claims about Stitchwort cite files at that commit and are **[checked]** against the source.
Claims about other languages are **[cited]** (read in the primary source while writing this),
**[inferred]** (my reading, not stated in a source), or **[unverified]** (from memory, not
re-checked). [Sources](#sources) lists the pages.

## Contents

0. [Summary](#0-summary)
1. [What Stitchwort is (for a reviewer who doesn't know it)](#1-what-stitchwort-is)
2. [The problem](#2-the-problem)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design)
5. [Errors](#5-errors)
6. [Identity: hashing and caches](#6-identity-hashing-and-caches)
7. [Interactions](#7-interactions)
8. [Alternatives considered](#8-alternatives-considered)
9. [Staging and cost](#9-staging-and-cost)
10. [What we'd like reviewed](#10-what-wed-like-reviewed)
11. [Decisions](#11-decisions)
12. [Sources](#sources)

## 0. Summary

Exported Stitchwort data crosses into JavaScript as `{ tag: "Ctor", …fields }`, with the
constructor's name as the tag value and the field names as keys. A TypeScript app usually has
its own wire format already: the discriminant is `type`, its values are `"CIRCLE"`, a key is
`center_x`, an optional field is `T | null`. Today the only way to match it is to name the
Stitchwort constructors and fields after the JSON, and the tag key can't be changed at all.

The proposal:

```
@[js.tag "type"]
type Shape =
  | @[js.name "DOT"]     Dot
  | @[js.name "CIRCLE"]  Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)
  | @[js.name "POLYGON"] Polygon (sides: Nat) (@[js.nullable] label: Option Text)
```

crosses as

```ts
export type Shape =
  | { readonly type: "DOT" }
  | { readonly type: "CIRCLE"; readonly radius: bigint; readonly center_x: bigint }
  | { readonly type: "POLYGON"; readonly sides: bigint; readonly label: string | null };
```

- **Syntax.** `@[name argument?, …]`, written before what it applies to: a declaration (its own
  line or the same line), a constructor (after its `|`), or a field (inside its brackets). Lean 4's
  form, with `@` as in Scala, Kotlin, TypeScript, ReScript and Gleam.
- **A closed set.** Every attribute the compiler accepts is listed in one table in the compiler
  and in the docs. An unknown one is an error with a suggestion; a known one in the wrong place,
  or with the wrong argument, is an error. There is no user-defined attribute and no
  "ignored if not understood".
- **Namespaced.** The first set is `js.tag`, `js.name` and `js.nullable`, all about the JS
  boundary. Bare names (`@[inline]`) are reserved for later language-level attributes.
- **One rule about meaning.** An attribute never changes what a program means to the type
  checker, the kernel, the evaluator, tests or proofs. Anything that does stays a keyword
  (`export`, `instance`, `theorem`, `decreasing`). So the kernel never sees attributes.
- **Identity.** Recommended: attributes are **not** part of a declaration's content hash. They
  are an elaborator side table, cached with the other side tables, read only by the JS backend.
  Changing a JS name reruns no tests. The alternative (hash them into the data type, as the
  `record` flag already is) is weighed in [§6](#6-identity-hashing-and-caches) and is D598.
- **Cost.** Only the boundary changes: the generated code inside the module keeps `tag` and
  the Stitchwort names, and the table-driven decoder and encoder translate keys as they copy.
  Rough size: one lane for `js.tag` and `js.name` on constructors and fields, a small one for
  `js.nullable` once D582 and D583 have landed, a small one for names of types and exports.

## 1. What Stitchwort is

Stitchwort is a total, dependently typed functional language implemented in Rust, with a
browser playground (WASM), a language server, and a JavaScript backend. The surface is
Scala/TypeScript-like: `def f (x: Nat): Nat := …`, `type Pet = | Cat (lives: Nat) | Dog
(age: Nat)`, records `type Person = { name: Text, age: Nat }`, dot calls `xs.length`.
There are no users yet, so nothing needs a migration path.

The facts that matter here:

- **A small trusted kernel** (`crates/core`) re-checks everything the elaborator
  (`crates/elab`) produces. Nothing about JS names belongs there.
- **Content hashes.** Every checked declaration has a BLAKE3 content hash
  (`crates/core/src/hash.rs`; `docs/core.md` "Tests and content hashes") **[checked]**.
  References are hashed as their targets' hashes, so a hash covers its dependencies. Names of
  definitions, binders and locals are *not* hashed (renaming a function changes no hash). But
  **data types are nominal**: their hash includes the type's name, its constructors' names, its
  fields' names and whether it's a record. The comment in `hash.rs` (`fn ctors`) says field names
  are hashed "because they change the JS (each field's key)", and the record flag "because it
  changes the JS representation" **[checked]**.
- **What uses the hash.** The test cache keys each test result by the test's hash
  (`docs/core.md`), so a test reruns only when something it depends on changes. Three
  boundary codecs (`Nat`, `Text`, and the library's `SafeNat`/`SafeInt`, which cross as JS
  `number`) are switched on by the content hash of the data type they were written for
  (`crates/js/src/lib.rs:27`, `NAT_DATA_HASH`, `SAFE_NAT_HASH`, …) **[checked]**. The check cache
  (`docs/proposals/check-cache.md`) skips *elaboration* of an unchanged file, keyed by the
  compiler build, the file's text and its dependencies' keys; every cached declaration still goes
  through the kernel again, and each cross-file reference records the hash it expects
  **[checked]**. The cache also stores about twenty elaborator *side tables* (scope entries,
  derived-instance reasons, lifted helpers…) that the hash doesn't cover (check-cache.md §4.4,
  risks: "forgetting a table").
- **The JS boundary** (DESIGN.md §12) **[checked]**. `export def` makes a function callable from
  TS. Each export is wrapped: *decode* every input into fresh internal values (reading each own
  property once; inherited properties, holes, cycles refused), *validate* (decidable
  preconditions run as checks), *compute*, *encode*. A `.d.ts` is generated. Decoding and
  encoding are a loop driven by per-type description tables (`info$…`), not recursion
  (`crates/js/src/lib.rs` around 1060–1170). The current representations:
  - a variant: `{ tag: "Square"; side: bigint }`; constructors must name their fields;
  - a record: a plain object, no tag, keys in declared order;
  - `Option a`: tagged today (`{ tag: "None" } | { tag: "Some"; value: A }`); SW-339 (D582,
    running) changes an `Option` record field to an optional property, `T | undefined` elsewhere,
    missing or `undefined` read as `None`, an inner `Option` of a nested one still tagged; D583
    (pending) refuses `null` by default and opts in to it;
  - **names**: a field's key is its name with `'` written `$`; the keys `tag` and `__proto__` are
    taken, so a variant field called `tag` gets the key `$tag` (`field_key`,
    `crates/js/src/lib.rs:2936–2945`; a record's field `tag` keeps `tag`, `record_key`). A type's
    TS name is its short name; two boundary types with the same short name are `E-EXPORT`; an
    export's JS name is its short name, which must be a JS identifier that isn't reserved.
  - **Inside the module the same objects are used**: generated code builds `{ tag: "Square",
    side: … }` and reads `.side` (`lib.rs:1921–1928`). The decoder's output *is* the internal value.
- **Derived instances.** Every data type gets `==`, `Show` and an order derived automatically
  (`crates/elab/src/derive*.rs`); `Show` prints Stitchwort syntax (constructor names).
- **Tooling.** The language server offers hover, go to definition, references, document and
  workspace symbols, selection ranges; no completion yet (`crates/cli/src/lsp.rs:75–88`)
  **[checked]**. There is a VS Code grammar (`editors/vscode/syntaxes/stitchwort.tmLanguage.json`).
  There is no formatter **[checked]**.
- **Syntax today.** `@` and `#` are not tokens: the lexer rejects them as "unexpected character"
  (`crates/syntax/src/lexer.rs`, the `_ =>` arm of the operator match) **[checked]**, so `@[` is
  free. `%` is the remainder operator. Comments are `--`. Declarations start at column 0, and the
  parser first splits a file into one token group per column-0 token (`split_decls`,
  `crates/syntax/src/parser.rs:254`) **[checked]**.

## 2. The problem

A generic case from a real-world TypeScript app, which already has

```ts
type Shape =
  | { type: "DOT" }
  | { type: "CIRCLE"; radius: bigint; center_x: bigint }
  | { type: "POLYGON"; sides: bigint; label: string | null };
```

and the Stitchwort library must take and return exactly this. Four gaps:

1. **The discriminant key** is `type`, not `tag`. Nothing can change it today.
2. **Discriminant values** are `"CIRCLE"`. Possible today only by naming the constructor
   `CIRCLE` (a legal constructor name), which leaks the wire format into every pattern match.
3. **Field keys** are `center_x`. Possible only by naming the field `center_x`; impossible for keys
   that aren't Stitchwort names (`"center-x"`, `"$type"`, `"0"`).
4. **`null` versus missing.** `label: string | null` is required and nullable; D582 gives
   `label?: string` (optional property), and D583 would refuse `null`. The app needs a per-field
   way to say "this one is `T | null`".

All four are properties of *one data type's JS form*, set where the type is declared, and none
changes anything inside Stitchwort. A wider need is in sight (inlining hints, deprecation,
`simp`-like lemma sets, `@[implemented_by]`-style natives), so the syntax should be general even
though the first set is small.

**Non-goals.** Untagged/unboxed unions (ReScript `@unboxed`, serde `untagged`), adjacent tagging
(`{ tag, content }`), numeric or boolean discriminants, multiple wire formats for one type,
changing the format of library types (`Option`, `List`), and user-defined attributes.

## 3. How other languages do it

### 3.1 Summary

| System | Syntax | Where | Set | Unknown name | Affects identity? |
|---|---|---|---|---|---|
| Rust | `#[path]`, `#[path = "s"]`, `#[path(…)]`; inner `#![…]` | before items, fields, variants | open: built-ins, macro attributes, derive helpers, tool attributes | error ("cannot find attribute") **[cited]** | n/a |
| serde (Rust derive) | `#[serde(tag = "type", rename = "…", rename_all = "…")]` | container, variant, field | closed per derive | compile error from the derive **[unverified]** | n/a |
| Lean 4 | `@[simp, inline]`; `attribute [simp] f` later; `-simp` erases; `local`/`scoped` | before declarations | open (extensible syntax category) | error **[unverified]** | not in the kernel's declaration **[inferred]** |
| Kotlin + kotlinx.serialization | `@SerialName("x")`, `@JsonClassDiscriminator("type")` | classes, properties | open (annotation classes) | error (must resolve to a class) **[inferred]** | n/a |
| C# / System.Text.Json | `[JsonPolymorphic(TypeDiscriminatorPropertyName = "kind")]`, `[JsonDerivedType(typeof(D), "d")]` | on the base type | open (classes) | error **[inferred]** | n/a |
| Swift Codable | `enum CodingKeys: String, CodingKey { case name = "user_name" }` | a nested declaration, not an attribute | n/a | n/a | n/a |
| Haskell aeson | `Options { sumEncoding = TaggedObject "tag" "contents", constructorTagModifier = f }` as *values* passed to the derivation | the instance | functions | n/a | n/a |
| OCaml + ppx | `[@key "k"]`, `[@name "N"]`, `[@@deriving yojson]` | `[@…]` on expressions, constructors, labels; `[@@…]` on items; `[@@@…]` floating | open | **ignored** by the compiler unless known **[cited]**; warnings 47/53 only for known ones | n/a |
| ReScript (v11) | `@tag("kind")` on a type, `@as("x")` on constructors and record fields, `@unboxed` | before type, constructor, field | closed set of decorators | **[unverified]** | n/a |
| F# + FSharp.SystemTextJson | `[<JsonName "x">]` on cases and fields; tag key by converter option `UnionTagName` | case, field; option | open (.NET) | **[inferred]** | n/a |
| Idris 2 | `%inline`, `%foreign`, `%name`, … | before declarations, or file-level | closed list in the reference **[cited]** | **[unverified]** | n/a |
| Scala | `@tailrec`, `@deprecated("…")` | before definitions; order irrelevant **[cited]** | open (classes) | error **[inferred]** | n/a |
| Gleam | `@external(javascript, "./m.mjs", "f")`, `@deprecated` | before functions/types | closed **[unverified]** | **[unverified]** | n/a |
| Unison | none; names, docs and metadata stored *beside* the hash | separate | n/a | n/a | names "don't affect the function's hash" **[cited]** |
| Elm, PureScript, Roc | no attributes; JSON by value-level decoders (Elm `Json.Decode`, PureScript codecs) **[unverified]** | n/a | n/a | n/a | n/a |
| TypeScript | decorators `@d` are runtime functions on classes and members; not on type aliases or unions **[unverified]** | classes | open | error (an unresolved name) | n/a |

### 3.2 The closest match: ReScript

ReScript compiles to JS and, since v11, lets a variant match an existing TS discriminated union
exactly **[cited]**:

```rescript
@tag("state") type loadingState =
  | @as("loading") Loading({ready: bool})
  | @as("error") Error({message: string})
  | @as("done") Done({data: data})
```

gives `{ state: "error", message: "Something went wrong!" }`. Record fields take `@as` too:
`type action = { @as("type") type_: string }` **[cited]**. The blog post's motivation is ours:
before v11 there was "no way to customize the discriminator (the `TAG` property)", so external data
needed hand-written conversion **[cited]**. Placement is ours too: on the type, after a
constructor's `|`, before a field. The difference is that ReScript changes the *runtime*
representation (zero-cost binding); Stitchwort already copies at the boundary, so it only needs
to change the boundary codec.

### 3.3 Serialisation libraries: the same three knobs everywhere

Everyone who maps sum types to JSON objects ends up with the same small set:

- **The discriminant key**: serde `tag = "type"` (internally tagged), aeson
  `TaggedObject { tagFieldName }` (default `"tag"`), STJ `TypeDiscriminatorPropertyName`
  (default `"$type"`), kotlinx `@JsonClassDiscriminator`, FSharp.SystemTextJson `UnionTagName`
  (default `"Case"`), ReScript `@tag` **[cited]**.
- **Discriminant values and field keys**: serde `rename`, kotlinx `@SerialName`, STJ
  `JsonDerivedType(…, "x")`, ppx `[@name]`/`[@key]`, F# `JsonName`, ReScript `@as`, Swift
  `CodingKeys` raw values **[cited]** (Swift **[unverified]**).
- **A casing rule** applied to all names: serde `rename_all` (eight conventions:
  `lowercase`, `UPPERCASE`, `PascalCase`, `camelCase`, `snake_case`, `SCREAMING_SNAKE_CASE`,
  `kebab-case`, `SCREAMING-KEBAB-CASE`), aeson `constructorTagModifier`/`fieldLabelModifier`
  (arbitrary functions) **[cited]**.

Lessons:

- **Clashes between the tag key and a field.** aeson's docs warn that a record field with the
  tag field's name overwrites the tag; STJ's docs say to avoid a discriminator name that
  "conflicts with a property in your type hierarchy" **[cited]**. These are warnings, not errors.
  Stitchwort today avoids the clash by renaming the field to `$tag`; with a user-chosen key it
  should be an error ([§5](#5-errors)).
- **Casing rules are ambiguous for sums with fields.** serde's `rename_all` on an enum renames
  the *variants*, so serde later added `rename_all_fields`, "a `rename_all` on every struct
  variant of an enum" **[cited]**. A casing helper must say which names it renames.
- **Order dependence at runtime.** STJ by default needs `$type` first in the JSON object, and
  has a flag to allow it elsewhere at the cost of buffering **[cited]**. Stitchwort's decoder
  reads own properties by key, so key order never matters on input **[checked]**.
- **null versus missing is its own knob.** kotlinx: a `null` for a non-nullable property is an
  error even with a default; `explicitNulls` controls emitting nulls **[cited]**. aeson has
  `omitNothingFields` and `allowOmittedFields` **[cited]** (signatures only). ppx_deriving_yojson
  `[@default]`: "not required to be present in inputs and will not be emitted in outputs"
  **[cited]**.

### 3.4 Attribute systems: syntax, closure, validation

- **Rust** has four kinds: built-in, proc-macro, derive-helper, and *tool* attributes
  (`#[rustfmt::skip]`), where "when a tool is not in use, the tool's attributes are accepted
  without a warning"; rustc knows the tools `clippy`, `rustfmt`, `diagnostic`, `miri`,
  `rust_analyzer` **[cited]**. A misspelt attribute (`#[sede(…)]`) is an error with a
  "similarly named" suggestion (rustc UI test `missing-derive-1`) **[cited]**. Meta forms: a
  word, `name = "string"`, `name(list)` **[cited]**.
- **Lean 4**: `@[attr, …]` sits "between the documentation comment and the visibility
  modifiers"; `attribute [attr] ident` adds or removes attributes after the fact (`-attr`);
  `local` and `scoped` limit them to a section or to when a namespace is open; the syntax category
  "is designed to be extended" **[cited]**.
- **OCaml**: three forms by what they attach to (`[@…]`, `[@@…]`, `[@@@…]`); attributes are
  "mostly ignored by the type-checker but can be used by external tools" **[cited]**, so a typo in
  an unknown attribute is silently ignored **[inferred]**.
- **Scala**: "an annotation clause applies to the first definition or declaration following it",
  several are allowed and "their order doesn't matter"; some are *checked* (`@tailrec` fails
  compilation if the call isn't in tail position) **[cited]**.
- **Idris 2** uses `%` pragmas, a fixed list in the reference, some file-level and stateful
  ("change compiler behavior until the behavior is changed back using the same pragma")
  **[cited]**.
- **Unison** keeps names and metadata outside the hash: "names are just separately stored
  metadata that don't affect the function's hash" **[cited]**.

### 3.5 What to take

1. ReScript's shape and placement (type / constructor / field), and its three meanings.
2. Lean's `@[…]` brackets: Stitchwort application is juxtaposition (`f x`), so an attribute
   with an argument reads like one (`js.name "X"`), and the brackets say where it ends.
3. Rust's and Lean's "unknown is an error", not OCaml's and Rust-tools' "unknown is ignored":
   a misspelt wire-format attribute that's silently ignored is a production bug.
4. A closed set, so every attribute has an exact, documented meaning ("attribute soup" is what
   open annotation systems grow into **[inferred]**).
5. Not Lean's after-the-fact `attribute [...]`, nor `local`/`scoped`: the wire format of a type
   should be visible where the type is, and can't depend on what's imported or in what order.
6. Unison's position on identity, adapted ([§6](#6-identity-hashing-and-caches)).

## 4. The design

### 4.1 Grammar

```
attributes ::= "@[" attribute ("," attribute)* ","? "]"
attribute  ::= attrname argument?
attrname   ::= lower ("." lower)*          -- js.tag, js.name, js.nullable
argument   ::= string                       -- a plain string literal, no interpolation
```

- `@[` is one new token (`@` alone stays an error). The contents are read by the normal lexer.
- **Several attributes**: `@[js.tag "type", js.name "ShapeDto"]`, or two groups
  `@[js.tag "type"] @[js.name "ShapeDto"]`. The same. **Order never matters** (each attribute is
  independent); the same name twice is `E-ATTRIBUTE`.
- **Argument kinds.** The first set needs only *flags* (`js.nullable`) and *strings*. Other
  forms (identifiers, numbers, `key = value`) are reserved: a later attribute can add them
  without changing existing code. An argument written where none is taken, or missing where one is
  needed, is `E-ATTRIBUTE`.
- **Comments** inside `@[…]` are allowed; layout doesn't apply inside the brackets (rule 7 of
  the layout rules already says brackets end nothing).

### 4.2 Placement

| Target | Where `@[…]` goes | Example |
|---|---|---|
| data type, record | before `type`, on its own line(s) at column 0 or on the same line | `@[js.tag "type"]` then `type Shape =` |
| constructor | after its `\|`, before its name | `\| @[js.name "POLYGON"] Polygon (sides: Nat)` |
| constructor field | inside its brackets, before the name | `(@[js.name "center_x"] centerX: Nat)` |
| record field | before the name | `{ @[js.name "type"] kind: Text, … }` |
| `export def` | before `export`, on its own line(s) or the same line | `@[js.name "renderShape"]` then `export def render …` |

- **Declarations.** Attribute lines belong to the next declaration: the parser's column-0
  splitting (`split_decls`) treats a group that is only attributes as a prefix of the following
  group. Blank lines and comments may come between. Attributes followed by nothing, or by another
  attribute group then end of file, are `E-PARSE`.
- **A field binder with an attribute must name one field**: `(@[js.name "x"] a b: Nat)` is
  `E-ATTRIBUTE` (which of the two?). Write two binders.
- **Nowhere else** for now: local definitions, `def`s that aren't exported, theorems, tests,
  abilities and their operations, interfaces, synonyms, parameters of functions, expressions.
  Each is `E-ATTRIBUTE` ("`js.name` can't be used on a theorem; it applies to data types,
  constructors, fields and exports"). The grammar allows `@[…]` before every declaration, so the
  error is about meaning and the message can be specific.
- **Not after the fact.** There is no `attribute [js.name "X"] Shape.Circle`. A type's wire
  format is written where the type is, once. Consequence: a library type's format (`Option`,
  `List`, `Pair`) can't be changed by a program; that's what D582/D583 decide for everyone. A
  program that needs a different format declares its own type.

### 4.3 Namespaces

- `js.` is the JavaScript backend's. Only the compiler defines names in it.
- **Bare names are reserved** for language-level attributes (`@[inline]`, `@[deprecated "…"]`),
  none of which exist yet. Each would come with its own design note.
- Other namespaces (`ts.`, `lsp.`, `test.`) don't exist; using one is `E-ATTRIBUTE-UNKNOWN`. If
  external tools ever need attributes, the way in is a registered namespace (Rust's tool
  attributes), not "anything unknown is ignored".

### 4.4 The rule about meaning

**An attribute never changes what a program means**: not typing, elaboration, evaluation,
`stitchwort run`, tests, proofs, `Show`, `==`, the order, error messages about the program, or
what a pattern matches. It may change only *how something is represented outside Stitchwort*
(the JS boundary and `.d.ts`), or, for later attributes, how fast something runs or which
warnings are shown. A feature that changes meaning is a keyword or ordinary syntax instead
(`export`, `instance`, `theorem`, `decreasing`, `auto`).

This is the guard against "hidden semantics", and it's what makes the identity rule in §6
sound: nothing the kernel, the evaluator or a test can observe depends on an attribute.

### 4.5 The first set

All three apply only at the JS boundary: the *encoded* objects an export returns, the objects it
*decodes*, and the `.d.ts`. Inside the generated module, values keep `tag` and Stitchwort names.

#### `js.tag "KEY"` (on a data type)

The discriminant property of this type's variants is `KEY` instead of `tag`.

- Applies to a data type with a tag: not a record (`E-ATTRIBUTE`: "a record has no tag").
- `KEY` must be non-empty and not `__proto__` (`E-ATTRIBUTE`).
- **A field whose key equals `KEY` is `E-JS-NAME-CLASH`**, at the field, with a note suggesting
  `js.name` on the field. With `js.tag`, the `$`-renaming rule for `tag` is off for this type: a
  field `tag` has the key `tag`, a field `type` under `js.tag "type"` is the clash. (Without
  `js.tag`, today's rule is unchanged: a field `tag` is `$tag`.) Reason: a user who picks the key
  is designing the wire format and should see the conflict, not get an invented `$type`
  (aeson and STJ only warn, [§3.3](#33-serialisation-libraries-the-same-three-knobs-everywhere)).
- Decoding reads `own(x, KEY)`; messages say "no `type`; expected "CIRCLE" or "POLYGON"".

#### `js.name "NAME"` (on a constructor, a field, a data type, or an export)

| On | Changes | Rules (`E-JS-NAME-CLASH` / `E-ATTRIBUTE`) |
|---|---|---|
| a constructor | its discriminant value | non-empty; distinct from every other constructor's value in the type (after renaming) |
| a field (variant or record) | its key | non-empty; not `__proto__`; distinct from the other keys of the same constructor (after renaming); not the type's tag key |
| a data type | its name in the `.d.ts` (`export type NAME`) | a TS identifier, not reserved, not `StitchwortInputError`/`StitchwortResourceError`; two boundary types with the same TS name stay `E-EXPORT`, but now one can be renamed |
| an `export def` | the name the module exports it under | a JS identifier that isn't reserved; two exports with the same JS name stay `E-EXPORT` |

- A renamed field's key is exactly `NAME`: no `$` for primes, no escaping. Any string is a valid
  property key, and the `.d.ts` quotes it when it isn't an identifier (`ts_key`, which exists).
- A name is checked where the attribute is written, when the type is declared, even if the type
  never reaches an export. Clashes that only exist at the boundary (two types' TS names) are
  found at the export, as today.
- The Stitchwort name is still used everywhere inside the language: patterns, `Show`, error
  messages, the playground's value display. Hover shows both ([§7.4](#74-tooling)).

#### `js.nullable` (on a field of type `Option T`)

The field is `T | null`: always present, `null` for `None`.

- **Encode**: `None` is `null`, `Some v` is `v`'s encoding. The property is always written.
- **Decode**: `null` is `None`; so are a missing property and `undefined` (D582's rule for
  optional properties, kept so that `js.nullable` only *adds* `null`); anything else is decoded
  as `T`.
- **`.d.ts`**: `readonly label: string | null`. (It describes what the module returns; input
  is more permissive, as it is for extra properties today. Question 6 in §10.)
- The field's type must be `Option T` after unfolding synonyms (`E-ATTRIBUTE`: "`js.nullable`
  needs a field of type `Option T`; this one is `Text`"). On `Option (Option T)`, `null` is the
  outer `None`; the inner `Option` keeps whatever form D582 gives it, so the encoding stays
  unambiguous.
- Without the attribute, a field of type `Option T` follows D582 (optional property) and D583
  (whether `null` is refused). `js.nullable` is the opt-in D583 calls for.
- It depends on SW-339 landing first ([§9](#9-staging-and-cost)).

#### Not in the first set: a casing helper

A `rename_all`-style attribute would save writing `js.name` on every constructor of a long
enum. Research says it has a real pitfall (serde had to split `rename_all` and
`rename_all_fields`), and the motivating app has a handful of constructors. **Recommended:
defer**; if it comes, two separate attributes on the type, `js.tagCase "SCREAMING_SNAKE_CASE"`
(constructor values) and `js.fieldCase "snake_case"` (field keys), with serde's eight convention
names, an explicit `js.name` winning, and the clash checks run on the result. D599.

### 4.6 A complete example

```
namespace Drawings

@[js.tag "type"]
type Shape =
  | @[js.name "DOT"]     Dot
  | @[js.name "CIRCLE"]  Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)
  | @[js.name "POLYGON"] Polygon (sides: Nat) (@[js.nullable] label: Option Text)

type Drawing = {
  @[js.name "type"] kind: Text,
  shapes: List Shape,
}

@[js.name "renderDrawing"]
export def render (d: Drawing): Text := …
```

```ts
export type Shape =
  | { readonly type: "DOT" }
  | { readonly type: "CIRCLE"; readonly radius: bigint; readonly center_x: bigint }
  | { readonly type: "POLYGON"; readonly sides: bigint; readonly label: string | null };
export type Drawing = { readonly type: string; readonly shapes: readonly Shape[] };
export declare function renderDrawing(d: Drawing): string;
```

Inside Stitchwort nothing changes: `match s with | Dot => … | Circle r x => … | Polygon n l => …`,
`d.kind`, and `Show` prints `Circle 3 0`.

### 4.7 Where it lives in the compiler

- **`crates/syntax`**: a token for `@[`; an `Attribute { name: Name, arg: Option<(String,
  Span)>, span }`; an `attrs: Vec<Attribute>` on `Decl::Data`, `Decl::Signature` (for
  `export`), `CtorDecl`, and per field (`Binder` gets `attrs`; record fields are binders already,
  `parser.rs:1168`). `split_decls` joins attribute-only groups to the next group. The parser
  checks only the grammar; it knows no attribute names.
- **`crates/elab`**: one module, `attributes.rs`, holding **the** table: name, allowed targets,
  argument kind, one-line doc, long doc. It validates every attribute (unknown, place, argument,
  duplicate, the per-type clash rules) and fills a side table, roughly
  `js_repr: HashMap<DataId, JsRepr { tag_key, ts_name, ctor_tags, field_keys, nullable }>` and
  `js_export_names: HashMap<DefId, String>`. Lifted helpers, derived instances and
  everything else ignore it.
- **`crates/core`**: unchanged.
- **`crates/js`**: the per-type description (`info$…`, built around `lib.rs:810`) gets, per
  constructor, the external tag value and, per field, the external key next to the internal one;
  the decoder reads external keys and builds internal objects (it already builds fresh objects,
  `out: { tag }`, so this costs nothing extra); the encoder does the reverse; `nullable` fields get
  a small leaf-like wrapper; the `.d.ts` printer (`lib.rs:2540–2560`) uses the external names.
  Function bodies, `field_key_at` for internal access, and the internal tag are untouched.

## 5. Errors

| Code | When | Example message |
|---|---|---|
| `E-ATTRIBUTE-UNKNOWN` | a name not in the table, in any namespace | "unknown attribute `js.rename`; did you mean `js.name`? The `js` attributes are `js.tag`, `js.name`, `js.nullable`" |
| `E-ATTRIBUTE` | a known attribute in a place it doesn't apply; a missing, extra or wrong-kind argument; the same attribute twice on one target; `js.tag` on a record; `js.nullable` on a non-`Option` field; an attribute on a binder with two names | "`js.tag` applies to a data type, not a constructor" |
| `E-JS-NAME-CLASH` | after renaming, two constructors with the same tag value, two fields of one constructor with the same key, a field key equal to the tag key, a key `__proto__`, a type or export name that isn't a valid (non-reserved) JS identifier | "two constructors of `Shape` cross as `"CIRCLE"`: `Circle` (here) and `Ring` (line 4)" |
| `E-EXPORT` (existing) | boundary-wide clashes: two boundary types with one TS name, two exports with one JS name | as today, naming the attribute when one is involved |
| `E-PARSE` (existing) | malformed `@[…]`; attributes with no declaration after them | "attributes must be followed by the declaration they apply to" |

Every attribute error points at the attribute's span. There's no warning for an attribute on a
type that no export reaches: types are often declared before the export that uses them.

## 6. Identity: hashing and caches

### 6.1 The question

Content hashes in Stitchwort decide when a test reruns, which built-in codec applies to a
type, and whether a cached cross-file reference still matches. Should `js.*` attributes be part
of a data type's hash?

### 6.2 Today's precedent points both ways

- **For hashing them:** data types are nominal, and their hash *already* includes facts that
  matter only to JS: the `record` flag "because it changes the JS representation", and field
  names partly because they are JS keys (`hash.rs`, `fn ctors`) **[checked]**. So the content
  hash of a data type today means "the type *and* its JS shape".
- **Against:** names of definitions aren't hashed; Unison's model is that names and metadata live
  beside the hash. And the field-name reason is weaker after this note, since a field's JS key
  is no longer always its name; field names stay hashed for their other reason (they decide
  which field `p.name` means).

### 6.3 Options

**(A) Hash `js.*` attributes into the data type**, only when present (as the `implicit` field
flags are, so no existing hash changes), passed to the kernel as an opaque, never-interpreted
blob like the record flag. Exports' `js.name` stays unhashed (export names aren't hashed today).

- + One identity: two types with different wire formats are different hashes; the hash-keyed
  codecs (`SAFE_NAT_HASH`…) can't apply to a renamed copy; anything later keyed by hash (a cache
  of generated JS, an API-compatibility check between releases) is correct without a second key.
- − Renaming a JS key changes the type's hash and every dependent's, so their **tests rerun**,
  though no test can observe the change (§4.4). The kernel carries data it never reads.

**(B) Not hashed; a side table** (recommended). The logical hash is unchanged by attributes. The
elaborator keeps the `js_repr` table; the check cache stores it with the other side tables; the
JS backend is the only reader.

- + Matches §4.4: what the kernel and tests can see is exactly what's hashed. Renaming a JS key
  reruns nothing. The kernel is untouched.
- + No cache becomes unsound: the check cache keys on file text and dependency keys
  (check-cache.md §4.2) **[checked]**, so an edited attribute re-elaborates its file and the files
  that depend on it; and the JS backend reads a type's attributes from the type's own file's
  tables, never from a dependent's cache entry. The planned "early cutoff" (§4.3 there: key a
  dependent on the *exported* hashes and side tables, not the text) must include this table;
  that's one line in its list.
- − Two declarations with equal hashes may cross differently. Today that can only be the same
  type (data types hash their names), so the case is the *same type after an attribute edit*,
  which every build recomputes anyway.
- − The hash-keyed codecs must refuse attributes on their types: an attribute on `Nat`, `Text`,
  `SafeNat`, `SafeInt` (or any type with a built-in boundary form) is `E-ATTRIBUTE`. Programs
  can't annotate library types anyway (§4.2), so this guards the library's own sources.

**(C) A separate boundary hash** next to the logical one: for each export, a hash of its
content hash and the `js_repr` of every type its boundary reaches, computed by `crates/js`.
This is (B) plus a derived fingerprint. Useful later for "did this release change the JS API?"
(written into the generated module's header, compared in CI). Not needed now; (B) doesn't
prevent it.

### 6.4 Recommendation

(B) now, with (C) as a later addition if a use appears. The record flag stays hashed (it does
change meaning: a record has projections and `{ … }` syntax). `docs/core.md`'s list of what's
hashed gets one line: "attributes aren't hashed". D598.

### 6.5 The check cache

The side table joins the others the cache stores (check-cache.md's "forgetting a table" risk).
Its defence applies: the differential test (cached versus uncached elaboration of the library
must agree) should compare the `js_repr` tables too, and an extraction test should run once
with a warm cache.

## 7. Interactions

### 7.1 Derived instances and `Show`

Unchanged. `==`, the order and `Show` are about Stitchwort values; `Show` prints `Circle`, not
`"CIRCLE"`. A program that wants the JS name as text writes a function (or, later, a
reflection feature; out of scope).

### 7.2 Records

`js.name` on a record field changes its key; `js.tag` on a record is an error. D582's optional
properties apply to records' `Option` fields; `js.nullable` overrides them per field.

### 7.3 Codecs, `.d.ts`, validation

- Decoding still reads only own properties, each once; a renamed key is just a different key.
  Path messages use the external keys (`d.shapes[2].center_x: expected a non-negative bigint`), since
  they describe the JS input.
- Validators of record proof fields (DESIGN.md §12) are unaffected: they run on decoded values.
- `.d.ts`: external names; keys that aren't identifiers quoted; a renamed type's alias name.
  The awkward-names property test (`awkward_names_never_collide`, `crates/cli/tests/extract.rs`)
  extends to generated `js.name` values drawn from a pool including `tag`, `__proto__`,
  `constructor`, `""`, `"0"`, `"a-b"` and non-ASCII strings.

### 7.4 Tooling

- **Hover** on an attribute: its documentation from the table (one line plus the long doc).
  Hover on a constructor, field or type with JS attributes adds a line: "crosses to JS as
  `{ type: "CIRCLE", … }`".
- **Completion** (when the server gets it): after `@[`, the attributes valid at that place.
- **Highlighting**: the VS Code grammar and the playground's colouring get an `@[ … ]` scope.
- **Outline and navigation**: attributes aren't symbols; go to definition on an attribute name
  could open its section of the docs (later).
- **Formatter**: none exists; when one does, attributes go on their own line before a
  declaration and inline before constructors and fields.

### 7.5 The parallel lanes

- SW-339 (D582): `js.nullable` builds on its optional-property codec; staged after it.
- D583 (pending): if the default refuses `null`, `js.nullable` is the opt-in; if the default
  accepts `null` for `None` on input, `js.nullable` still matters for *output* (`null` written
  rather than the property omitted) and the `.d.ts`.
- SW-340 (D587, shared fields on variants): independent; a shared field's `js.name` would have
  to agree across constructors (checked as a clash).

## 8. Alternatives considered

**8.1 A clause on the type declaration.** `type Shape = … with js { tag = "type", Circle =
"CIRCLE", Polygon.label nullable }`. Keeps all JS facts in one place, but repeats every
name it changes (drift, checked but noisy), is far from the constructor it describes, and is a
new syntax form useful only to JS. Attributes are one general form for this and later uses.

**8.2 A separate `export encoding` block** (Swift `CodingKeys`, aeson `Options`, STJ's contract
model). Like 8.1 but anywhere, possibly in another file, possibly several per type. Real
advantages: logic types stay clean, and a type could have two encodings (API v1 and v2) or a
library type could get one. Costs: a new top-level form with its own ordering and scoping rules
(which encoding applies where?), and the format is no longer visible at the type. Rejected for
now; one type per wire format (a mirror type plus a conversion) covers the rare second encoding.
Reviewer question 4.

**8.3 Naming convention.** Name the constructor `CIRCLE` and the field `center_x`. Works
today for values that happen to be Stitchwort names, at the cost of pattern matches that read
like JSON; impossible for the tag key and for keys that aren't Stitchwort names. Rejected.

**8.4 Pragmas in comments** (`-- @js.name CIRCLE`). Comments that change behaviour are
hidden semantics, the parser drops comments today, and a typo would be a comment. Rejected.

**8.5 Value-level codecs** (Elm decoders, PureScript codec libraries, aeson's functions). Most
flexible, but the boundary codec is trusted, table-driven and stack-safe (DESIGN.md §12);
user-written codecs would be ordinary code at the boundary, losing the own-property, cycle and
sharing guarantees and the generated `.d.ts`. Rejected for this need; maybe for exotic formats.

**8.6 Build-wide options** (`--js-tag-key type`, kotlinx naming strategies, STJ naming policies).
Wrong granularity: one app's types disagree with each other. Rejected.

**8.7 Lean-style after-the-fact and scoped attributes.** `attribute [js.name "X"] Shape.Circle`,
`local`/`scoped`. Makes a type's format depend on what's imported and in what order. Rejected.

**8.8 `#[…]` (Rust) or `@name(…)` (Scala, Kotlin, ReScript).** `#` is free too, but every
Scala/TS-like language and ReScript use `@`. `@name("x")` with parentheses would look like a call
in a language whose calls are `f x`, and `@js.name "x"` without brackets can't say where an
argument ends before a constructor name. `@[…]` also groups several. Lean uses exactly this.

## 9. Staging and cost

Sizes are rough **[inferred]** from comparable lanes (records' boundary stage, SW-337).

| Stage | Content | Depends on | Size |
|---|---|---|---|
| 1 | Grammar, AST, `split_decls`, the table, all errors; `js.tag`; `js.name` on constructors and fields; codec and `.d.ts`; check-cache table; examples (`examples/extract/attributes.sw`, `examples/reject/attribute-*.sw`); extract runtime tests; awkward-names test; docs (`syntax.md`, DESIGN.md §12) | D597, D598 | one lane, roughly 600–900 lines with tests |
| 2 | `js.nullable` | SW-339 merged, D583 decided | small |
| 3 | `js.name` on types and exports; hover lines; grammar colouring | stage 1 | small |
| later | casing helpers (D599), boundary fingerprint (§6.3 C), other namespaces or bare attributes | each its own decision | — |

Risks: the boundary is trusted code, so each stage needs round-trip and refusal tests through a
real JS engine (as `crates/cli/tests/extract.rs` does today); and the side table must be in the
check cache or a warm build loses attributes silently (§6.5).

## 10. What we'd like reviewed

1. **The rule in §4.4** (attributes never change meaning; anything that does is a keyword). Is
   it the right line, and is it sustainable once performance attributes (`inline`) or
   `implemented_by`-style natives come? Lean's `@[implemented_by]` is an attribute that changes
   run-time behaviour; would you keep such a thing out of attributes?
2. **Identity (§6).** Is (B), not hashing attributes, sound and wise given that data types are
   otherwise nominal and the record flag is hashed for JS reasons? Is there a use of content
   hashes we've missed where two equal hashes crossing differently would bite?
3. **Closed set and errors.** Is "unknown is an error, no tool namespaces" right for a language
   with no users, or should a reserved namespace for external tools exist from the start?
4. **Placement versus a separate encoding block (§8.2).** Is one wire format per type,
   written on the type, the right default? Would you expect a second encoding to be needed soon?
5. **Clash policy.** A field whose key equals the chosen tag key is an error rather than
   renamed (`$type`). Agree? And should constructor values and keys be restricted further
   (identifier-like only), or is any non-empty string right?
6. **`js.nullable` (§4.5).** Decode accepts `null`, missing and `undefined`; encode writes
   `null`; the `.d.ts` says `T | null` (the output shape). Is the asymmetry acceptable, or should
   the `.d.ts` say `T | null | undefined` / `?: T | null`, or decoding be strict?
7. **Casing helper (§4.5).** Defer, or ship `js.tagCase`/`js.fieldCase` now? Is serde's list of
   conventions the right vocabulary, and how should acronyms (`HTTPRequest`) split?
8. **Grammar (§4.1).** `@[name "arg"]` with juxtaposed arguments and comma-separated
   attributes: any parsing or readability trap you see, especially on constructors
   (`| @[js.name "X"] X (f: T)`) and inside field brackets?
9. **Anything missing from the first set** that a TS interop user hits within a week:
   numeric or boolean discriminants, `untagged` unions, a constructor-less "enum as string
   literal" form (`"UP" | "DOWN"` for a type whose constructors have no fields)?

## 11. Decisions

| ID | Question | Recommendation | Alternatives |
|---|---|---|---|
| D597 | Adopt attributes: `@[name arg?, …]` before declarations, after a constructor's `\|`, before a field's name; a closed, namespaced, documented set; unknown or misplaced is an error; attributes never change meaning (§4.4) | **Yes**, as §4 | a `with js { … }` clause (§8.1); an `export encoding` block (§8.2) |
| D598 | Are `js.*` attributes part of content hashes? | **No** (option B): an elaborator side table, stored by the check cache, read only by the JS backend; the kernel never sees them; a boundary fingerprint later if needed | (A) hash them into the data type like the record flag; (C) B plus a boundary hash now |
| D599 | The first set | **`js.tag`, `js.name` (constructors, fields; then types and exports), `js.nullable`**; a casing helper deferred, and if added, split as `js.tagCase`/`js.fieldCase` | add a casing helper now; leave out `js.name` on types/exports |

## Sources

- Rust Reference, Attributes: https://doc.rust-lang.org/reference/attributes.html
- rustc UI test for a misspelt derive helper (`#[sede]`): https://rust.googlesource.com/rust/+/HEAD/tests/ui/macros/missing-derive-1.stderr
- serde container attributes: https://serde.rs/container-attrs.html
- Lean 4 reference, Attributes: https://lean-lang.org/doc/reference/latest/Attributes/
- ReScript manual, variants: https://rescript-lang.org/docs/manual/variant
- ReScript blog, "Improving interop" (v11, `@tag`/`@as`): https://www.rescript-lang.org/blog/improving-interop
- ReScript syntax lookup, `@as`: https://rescript-lang.org/syntax-lookup/decorator_as
- kotlinx.serialization `JsonClassDiscriminator`: https://kotlinlang.org/api/kotlinx.serialization/kotlinx-serialization-json/kotlinx.serialization.json/-json-class-discriminator/
- kotlinx.serialization customisation (`@SerialName`, nulls): https://kotlinlang.org/docs/serialization-customization-options.html
- Kotlin annotations: https://kotlinlang.org/docs/annotations.html
- System.Text.Json polymorphism: https://learn.microsoft.com/en-us/dotnet/standard/serialization/system-text-json/polymorphism
- aeson `Data.Aeson.Types` (Options, SumEncoding): https://hackage.haskell.org/package/aeson/docs/Data-Aeson-Types.html
- ppx_deriving_yojson README: https://github.com/ocaml-ppx/ppx_deriving_yojson
- OCaml manual, attributes: https://ocaml.org/manual/latest/attributes.html; warnings 47 and 53: https://ocaml.org/manual/latest/comp.html
- FSharp.SystemTextJson customising: https://github.com/Tarmil/FSharp.SystemTextJson/blob/master/docs/Customizing.md
- Idris 2 pragmas: https://idris2.readthedocs.io/en/latest/reference/pragmas.html
- Scala tour, annotations: https://docs.scala-lang.org/tour/annotations.html
- Gleam tour, externals: https://tour.gleam.run/advanced-features/externals/
- Unison, "The big idea": https://www.unison-lang.org/docs/the-big-idea/

**Not verified:** Swift `CodingKeys` (Apple's page didn't render), Lean's and ReScript's
messages for an unknown attribute, serde's exact error for an unknown key inside `#[serde(…)]`,
Gleam's attribute set being closed, Elm/PureScript/Roc having no attribute syntax, TypeScript
decorators' limits. None of these changes the recommendation.
