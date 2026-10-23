# Proposal: attributes, `@[…]`, starting with the JavaScript wire format

**Status:** draft 2, 23 October 2026 (draft 1 was reviewed externally; this draft folds the
review in, D611). Ticket SW-341. **Stage 1 is built** ([As built](#as-built-stage-1)). D597 to
D599 are **decided, with the review's amendments**; D612 is **decided, amended by Matt** (the
default tag key is `$tag`), and D613 is **decided** ([§11](#11-decisions)). Written against commit `e5342b96`. Related: DESIGN.md §12 (JavaScript
extraction), [records.md](records.md) §11 (records at the boundary),
[check-cache.md](check-cache.md), [variant-fields.md](variant-fields.md) (SW-340, being revised
in parallel), and SW-339 (D582, merged as `2ba211a0`: `Option T` as `T | undefined`, an optional
property in a record's field, `null` refused).

Claims about Stitchwort cite files at that commit and are **[checked]** against the source.
Claims about other languages are **[cited]** (read in the primary source while writing this),
**[inferred]** (my reading, not stated in a source), or **[unverified]** (from memory, not
re-checked). [Sources](#sources) lists the pages.

## Contents

- [Response to review (draft 2)](#response-to-review-draft-2)

0. [Summary](#0-summary)
1. [What Stitchwort is (for a reviewer who doesn't know it)](#1-what-stitchwort-is)
2. [The problem](#2-the-problem)
3. [How other languages do it](#3-how-other-languages-do-it)
4. [The design](#4-the-design)
5. [Errors](#5-errors)
6. [Identity: hashing and caches](#6-identity-hashing-and-caches)
7. [Interactions](#7-interactions)
8. [Alternatives considered](#8-alternatives-considered)
9. [Staging, cost and tests](#9-staging-cost-and-tests)
10. [What we'd like reviewed (draft 1's questions, answered)](#10-what-wed-like-reviewed)
11. [Decisions](#11-decisions)
- [As built (stage 1)](#as-built-stage-1)
12. [Sources](#sources)

## Response to review (draft 2)

The reviewer approved the direction and D597 to D599, with amendments. Matt adopted all of
them. Each point, what changed, and what the code says where it bears on it.

| # | Review point | Change in draft 2 | Where |
|---|---|---|---|
| 1 | "Attributes never change meaning" promises too much: invalid attributes produce errors, an export rename resolves a name clash, and JS callers see a different shape | Replaced by the precise guarantee: valid `js.*` attributes don't change the checked core declarations, the kernel's judgments, or evaluation; they specify the external JS representation and are validated separately. A table places future attribute kinds against it; unchecked `implemented_by` stays outside. The `docs/core.md` line becomes "JS representation attributes are excluded from logical content hashes" | [§4.4](#44-what-an-attribute-may-change) |
| 2 | Option C's fingerprint misses export renames; a logical hash doesn't identify a JS interface; say which tests stay reusable; both metadata tables must be cached and remapped | Option B kept. New identity contract: logical identity, boundary-shape fingerprint (export names, effective schemas including defaults such as D582's, emitted TS names, codec policies), generated-artifact cache key. Which tests are reusable and which observe the boundary. `js_repr` and `js_export_names` both persisted and remapped. The ownership rule. The draft-1 claim that equal hashes crossing differently "can only be the same type after an edit" is dropped | [§6](#6-identity-hashing-and-caches) |
| 3 | `js.nullable` should be strict on input; state codec laws; resolve the `Option`-field inconsistency | Strict: `null` is `None`; a missing property or `undefined` is an error. Encode always writes the property. Codec laws stated. The baseline now matches what SW-339 landed: a *record* field `Option T` is an optional property `f?: T`; a *constructor* field (and everywhere else) is a required `T \| undefined`. Nested `Option` tested through a generic parameter too | [§4.5](#jsnullable-on-a-field-of-type-option-t), [§7.6](#76-codec-laws) |
| 4 | An explicit `@[js.tag "tag"]` behaved differently from omitting it | One uniform rule and one resolution order (tag key → tag values → field keys → clash check → one stored representation, read by both the codec and the `.d.ts` printer). No `$tag` fallback at the boundary: a field may ask for `"$tag"` explicitly. When an *unattributed* type's clash is reported is D612 | [§4.6](#46-resolving-a-types-representation), D612 |
| 5 | Every parsed attribute must be consumed or rejected; field attributes only on encoded slots; special-codec types; `@[` and layout; argument-shape errors | Invariant stated; the AST keeps attributes on every declaration form and every binder, and each handler consumes or rejects them. Field attributes only on fields with an encoded slot, classified by the kernel's `field_erased`, not by implicitness. Special-codec types (`Nat`, `Text`, `SafeNat`, `SafeInt`…) reject attributes anywhere inside them, from one shared registry. `@[` is an opening bracket everywhere the parser counts brackets, and in `split_decls`. Parser tests listed. Wrong-kind and extra arguments are grammar errors (`E-PARSE`), not promised as `E-ATTRIBUTE` | [§4.1](#41-grammar), [§4.2](#42-placement), [§4.8](#48-where-it-lives-in-the-compiler), [§5](#5-errors) |
| 6 | Shared fields needn't share a `js.name` | Requirement removed: each constructor's field keys are its own. Coordination with [variant-fields.md](variant-fields.md) noted | [§7.5](#75-the-parallel-lanes) |
| 7 | Arbitrary strings: prototype-named tag values, literal escaping, single reads, numeric keys, generated public names | Kept arbitrary strings, with the obligations listed: dispatch by `Map` (already so), "no escaping" means no key mangling, correct literal escaping (already so), single read (already so), ordering promise narrowed, export and type names checked against the whole generated public namespace | [§7.3](#73-codecs-dts-validation) |
| 8 | Closed registry, declaration-site encoding, casing, next encodings | Recorded: closed registry; the declaration-site encoding is the type's *default* JS encoding (named encodings possible later); casing deferred, and if added, tag casing and field casing separately, specified by examples; string-literal encodings for field-less variants are the likely next extension | [§4.3](#43-namespaces), [§4.5](#not-in-the-first-set-casing-helpers), [§8.2](#8-alternatives-considered), [§2](#2-the-problem) |
| 9 | A metadata-only-edit cache acceptance test, plus a list | Added, with the export-rename variant and the reviewer's list | [§9.2](#92-acceptance-tests) |

**Checked against the code while revising** (all at `e5342b96`):

- **Dispatch tables are already `Map`s.** A type's description is built by `datatype(name)` with
  `ctors: new Map()` and `flat: new Set()`, and the decoder dispatches with
  `t.info.ctors.get(tag)` (`crates/js/src/lib.rs`, the runtime prelude around lines 900 and
  1188) **[checked]**. So a tag value `"__proto__"`, `"constructor"` or `"toString"` is safe
  today; the obligation is to keep it so.
- **Literal escaping already exists.** Tag values and keys reach the generated JS through
  `js_string_literal` (escapes `"` and `\`, writes everything outside printable ASCII as
  `\u{…}`, `lib.rs:3367`), and `.d.ts` keys through `ts_key`, which quotes a non-identifier
  (`lib.rs:3146`) **[checked]**.
- **The encoder writes keys by assignment** onto a fresh object literal (`out: { tag: v.tag }`,
  then `f.out[key] = value`, `lib.rs` around 1283 and 1298) **[checked]**. Assigning `__proto__`
  that way sets the prototype instead of making a property, which is why `__proto__` stays
  forbidden as a *key* (§4.5). It is allowed as a *tag value*, which is a property value, not a
  key.
- **Each property is read once.** `own(x, key)` checks `hasOwn` (no getter runs) and then reads
  `x[key]` once; the decoder works on that captured value (`lib.rs:1115`) **[checked]**.
- **Private helpers can't collide with exports.** Each export's wrapper has an internal name and
  the module ends `export { wrapper as name }` (`lib.rs` around 727–735), so "exports aren't
  names in the module's scope" **[checked]**. Export and type names are already checked against
  `MODULE_NAMES` (`StitchwortInputError`, `StitchwortResourceError`; `lib.rs:178`, `:335`,
  `:3245`) **[checked]**; a renamed name must go through the same check.
- **What SW-339 landed.** In `define`, only a *record's* `Option` field gets the optional flag
  (`data.record && matches!(b, Boundary::Option(..))`, `lib.rs:2566`); a constructor's field
  without it is decoded as required (`refuse("missing")`) **[checked]**. DESIGN.md §12 and
  `docs/syntax.md` ("`Option` in an `export`") say the same: record field `nick?: string`;
  constructor fields, arguments, results and list elements `T | undefined`; `null` refused
  (`expected a value or undefined, not null`) **[checked]**. So draft 1's §4.5 sentence
  ("an unannotated `Option` field is an optional property") was wrong for constructor fields.
- **The check cache stores side tables by remappable reference.** An entry's `Tables`
  (`crates/elab/src/cache/mod.rs` around 1750) holds data-keyed tables (`records`,
  `interfaces`, `by_data`…) whose `DataId`s and `DefId`s are written as either an index into the
  unit's own declarations or an external dependency named by full path and expected hash, and
  read back through `In::data`/`In::def` (around 1648–1700) **[checked]**. `js_repr` and
  `js_export_names` would be two more tables of the same kind, with the format number bumped
  (`FORMAT`, line 63). The key covers the unit's text and its dependencies' keys, so an attribute
  edit misses the edited unit and everything that depends on it **[checked]**. A warm-versus-cold
  test harness already exists (`crates/cli/tests/check_cache.rs`) **[checked]**.
- **`split_decls` isn't bracket-aware.** It starts a group at *every* column-0 token except `:=`
  (`crates/syntax/src/parser.rs:254`) **[checked]**, so a `]` at column 0 closing a multi-line
  attribute group would start a group. Bracket depth is counted separately in several places
  (`parser.rs` around 186, 455, 474, and `parser/declarations.rs`), each matching
  `LParen | LBracket | LBrace` **[checked]**; `@[` must join every one.
- **Erasure is the kernel's.** Each constructor has `field_erased` (a proof or a type former;
  `crates/core/src/check.rs` around 1708, `globals.rs:199`) **[checked]**; "has an encoded slot"
  means "not erased", whatever the binder's implicitness.
- **Special codecs live in two places today.** The identities are `Builtin::SafeNat` and
  `Builtin::SafeInt` in `crates/core/src/registry.rs` (around 77 and 198), and the hashes the JS
  backend switches on are in `crates/rt/src/natives.rs` (`NAT_DATA_HASH` at 191, `SAFE_NAT_HASH`
  at 280) **[checked]**. `crates/elab` depends on `core` and `syntax` but not `rt`
  (`crates/elab/Cargo.toml`) **[checked]**, so the shared registry belongs in `core` (§4.8).
- **Generated declarations are already checked strictly.** The extraction tests run `tsc --strict
  --exactOptionalPropertyTypes` on the `.d.ts` (`crates/cli/tests/extract.rs` around 140)
  **[checked]**.

**Disagreements.** None of substance. Two notes:

- *Private helpers allocated collision-free* (point 7) is already true (above); draft 2 records it
  as an invariant to keep rather than new work.
- The uniform clash rule (point 4) also removes today's silent `$__proto__` key for a variant or
  record field called `__proto__`: with no fallbacks, its default key is `__proto__`, which is
  forbidden, so it needs a `js.name`. That follows from the rule rather than from the review's
  text, so it is part of D612.

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
  and in the docs. An unknown one is an error with a suggestion; a known one in the wrong place is
  an error. **Every parsed attribute is either consumed by its target's handler or is an error**:
  nothing is silently dropped. There is no user-defined attribute and no "ignored if not
  understood".
- **Namespaced.** The first set is `js.tag`, `js.name` and `js.nullable`, all about the JS
  boundary. Bare names (`@[inline]`) are reserved for later language-level attributes.
- **What they may change.** Valid `js.*` attributes don't change the checked core declarations,
  the kernel's judgments, or evaluation. They specify the external JS representation (the codec
  and the `.d.ts`) and are validated separately. Later attribute kinds are placed against this
  guarantee one by one ([§4.4](#44-what-an-attribute-may-change)).
- **Identity.** Decided (D598, option B): JS representation attributes are excluded from logical
  content hashes. They are elaborator side tables (`js_repr`, `js_export_names`), cached with the
  other side tables, read only by the JS backend. A logical hash therefore does **not** identify
  a JS interface or a generated artifact; anything that caches or compares those must key on the
  boundary metadata too ([§6](#6-identity-hashing-and-caches)).
- **`js.nullable`** is strict: the property must be present, `null` is `None`.
- **Cost.** Only the boundary changes: the generated code inside the module keeps `tag` and the
  Stitchwort names, and the table-driven decoder and encoder translate keys as they copy. Rough
  size: one lane for the grammar, the registry, `js.tag` and `js.name` on constructors and
  fields; a small one for `js.nullable`; a small one for names of types and exports.

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
  (`docs/core.md`), so a test reruns only when something it depends on changes. The boundary
  codecs for `Nat`, `Text` and the library's `SafeNat`/`SafeInt` (which cross as JS `number`) are
  switched on by the content hash of the data type they were written for (`NAT_DATA_HASH`,
  `SAFE_NAT_HASH`, … in `crates/rt/src/natives.rs`, used from `crates/js/src/lib.rs:27`)
  **[checked]**. The check cache (`docs/proposals/check-cache.md`) skips *elaboration* of an
  unchanged unit, keyed by the compiler build, the unit's text and its dependencies' keys; every
  cached declaration still goes through the kernel again, and each cross-unit reference records
  the full path and hash it expects **[checked]**. The cache also stores about twenty elaborator
  *side tables* (scope entries, records, derived-instance reasons, lifted helpers…) that the hash
  doesn't cover (check-cache.md §4.4, risks: "forgetting a table").
- **The JS boundary** (DESIGN.md §12) **[checked]**. `export def` makes a function callable from
  TS. Each export is wrapped: *decode* every input into fresh internal values (reading each own
  property once; inherited properties, holes, cycles refused), *validate* (decidable
  preconditions run as checks), *compute*, *encode*. A `.d.ts` is generated. Decoding and
  encoding are loops driven by per-type description tables (`define(info$…, …)`), not recursion
  (`crates/js/src/lib.rs`, `decode` and `encode` around 1147–1310). The current representations:
  - a variant: `{ tag: "Square"; side: bigint }`; constructors must name their fields;
  - a record: a plain object, no tag, keys in declared order;
  - `Option a` (D582, landed in `2ba211a0`): `T | undefined`; in a *record's* field, an optional
    property `readonly f?: T` (missing or `undefined` is `None`; `None` is encoded by leaving the
    property out). In a *constructor's* field, an argument, a result, a list element or a type
    argument it is `T | undefined` with the property required. `null` is refused. Only the
    outermost `Option` is `T | undefined`; an `Option` directly inside another stays the tagged
    `{ tag: "None" } | { tag: "Some"; value: T }`, also when it arrives through a type parameter;
  - **names**: a field's key is its name with `'` written `$`; the keys `tag` and `__proto__` are
    taken, so a variant field called `tag` gets the key `$tag` and one called `__proto__` gets
    `$__proto__` (`field_key`, `lib.rs:3089`; a record's field `tag` keeps `tag`, `record_key`).
    A type's TS name is its short name; two boundary types with the same short name are
    `E-EXPORT`; an export's JS name is its short name, which must be a JS identifier that isn't
    reserved or one of the module's own names.
  - **Inside the module the same objects are used**: generated code builds `{ tag: "Square",
    side: … }` and reads `.side`. The decoder's output *is* the internal value.
- **Derived instances.** Every data type gets `==`, `Show` and an order derived automatically
  (`crates/elab/src/derive*.rs`); `Show` prints Stitchwort syntax (constructor names).
- **Tooling.** The language server offers hover, go to definition, references, document and
  workspace symbols, selection ranges; no completion yet. There is a VS Code grammar
  (`editors/vscode/syntaxes/stitchwort.tmLanguage.json`). There is no formatter.
- **Syntax today.** `@` and `#` are not tokens: the lexer rejects them as "unexpected character"
  (`crates/syntax/src/lexer.rs`, the `_ =>` arm of the operator match) **[checked]**, so `@[` is
  free. `%` is the remainder operator. Comments are `--`. Declarations start at column 0, and the
  parser first splits a file into one token group per column-0 token (`split_decls`,
  `crates/syntax/src/parser.rs:254`) **[checked]**.

## 2. The problem

A TypeScript app already has

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
4. **`null` versus missing.** `label: string | null` is required and nullable. Today a
   constructor field `Option Text` is a required `string | undefined` and `null` is refused
   (D582). The app needs a per-field way to say "this one is `T | null`".

All four are properties of *one data type's JS form*, set where the type is declared, and none
changes anything inside Stitchwort. A wider need is in sight (inlining hints, deprecation,
`simp`-like lemma sets, natives), so the syntax should be general even though the first set is
small.

**Non-goals.** Untagged/unboxed unions (ReScript `@unboxed`, serde `untagged`), adjacent tagging
(`{ tag, content }`), numeric or boolean discriminants, several wire formats for one type,
changing the format of library types (`Option`, `List`), and user-defined attributes. **Likely
next**, after this note, and its own decision: string-literal encodings for field-less variants
(`type Direction = "UP" | "DOWN"`), which map directly and need no structural branch selection.
Numeric and boolean discriminants wait for a demonstrated need; untagged unions need a larger
design (overlapping alternatives, branch selection, diagnostics).

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
  Here it is an error ([§4.6](#46-resolving-a-types-representation)).
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
  "is designed to be extended" **[cited]**. Its `implemented_by` does not check that the two
  implementations agree; `csimp` is the alternative that requires an equality proof
  **[cited]** (via the review; see [§4.4](#44-what-an-attribute-may-change)).
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
6. Unison's position on identity, adapted, with the boundary's own identity kept separate
   ([§6](#6-identity-hashing-and-caches)).

## 4. The design

### 4.1 Grammar

```
attributes ::= "@[" attribute ("," attribute)* ","? "]"
attribute  ::= attrname argument?
attrname   ::= lower ("." lower)*          -- js.tag, js.name, js.nullable
argument   ::= string                       -- a plain string literal, no interpolation
```

- `@[` is one new token (`@` alone stays an error). The contents are read by the normal lexer.
- **`@[` is an opening bracket everywhere.** Every place the parser counts bracket depth or
  suppresses layout inside brackets (today the matches on `LParen | LBracket | LBrace` in
  `parser.rs` and `parser/declarations.rs`) treats `@[` as opening and its `]` as closing. In
  `split_decls`, a column-0 token inside an open `@[…]` doesn't start a declaration, so a group
  may close with `]` at column 0.
- **Several attributes**: `@[js.tag "type", js.name "ShapeDto"]`, or two groups
  `@[js.tag "type"] @[js.name "ShapeDto"]`. The same. **Order never matters** (each attribute is
  independent); the same name twice on one target is `E-ATTRIBUTE`.
- **Argument kinds.** The first set needs only *flags* (`js.nullable`) and *strings*. Other
  forms (identifiers, numbers, `key = value`) are reserved: a later attribute can add them
  without changing existing code. Because the grammar admits only an optional string, a number
  (`@[js.name 123]`) or a second string (`@[js.name "x" "y"]`) is a **grammar error**
  (`E-PARSE`). A missing argument (`@[js.name]`) or one where none is taken (`@[js.nullable
  "x"]`) parses, and is `E-ATTRIBUTE` from the registry. Draft 1 promised `E-ATTRIBUTE` for all
  four; that promise is relaxed.
- **Comments** inside `@[…]` are allowed; layout doesn't apply inside the brackets.

### 4.2 Placement

| Target | Where `@[…]` goes | Example |
|---|---|---|
| data type, record | before `type`, on its own line(s) at column 0 or on the same line | `@[js.tag "type"]` then `type Shape =` |
| constructor | after its `\|`, before its name | `\| @[js.name "POLYGON"] Polygon (sides: Nat)` |
| constructor field | inside its brackets, before the name | `(@[js.name "center_x"] centerX: Nat)` |
| record field | before the name | `{ @[js.name "type"] kind: Text, … }` |
| `export def` | before `export`, on its own line(s) or the same line | `@[js.name "renderDrawing"]` then `export def render …` |

- **Declarations.** Attribute lines belong to the next declaration: `split_decls` treats a group
  that is only attributes as a prefix of the following group. Blank lines and comments may come
  between. Attributes followed by nothing, or by another attribute group then end of file, are
  `E-PARSE`. An attribute group always attaches to the *next* declaration, whatever it is: before
  a `namespace`, a `theorem` or a `def` it attaches there and is an error there; it never drifts
  onto a later `type`.
- **Every parsed attribute is consumed or rejected.** Attributes are kept on every declaration
  form and every binder the parser builds, not only on the four targets that accept them; each
  elaboration path either hands them to the registry for its target or reports them. So
  `@[js.name "x"] theorem t : …`, `def f (@[js.nullable] x: Option Text): …`, an attribute on a
  lambda's or a `forall`'s binder, on a data type's *parameter*, on a local definition, or before
  a `namespace` are all errors, never silently ignored. A test per target in the "nowhere else"
  list below holds this.
- **Field attributes need an encoded slot.** A field attribute applies to a field that has a
  property in the JS object: one the kernel doesn't erase (`field_erased`: not a proof, not a
  type). On an erased field (a record's proof field, a type field) it is `E-ATTRIBUTE` ("`centerOk`
  is a proof, so it has no property in JS"). Implicitness doesn't decide this: an implicit field
  that carries data is encoded and can be renamed; an explicit proof field can't. Clash checks
  run only over encoded slots, so an erased field named `type` never clashes with `js.tag
  "type"`.
- **A field binder with an attribute must name one field**: `(@[js.name "x"] a b: Nat)` is
  `E-ATTRIBUTE` (which of the two?). Write two binders.
- **Special-codec types take no attributes anywhere.** A type with a built-in boundary form
  (`Nat`, `Text`, `Bool`, `Int`, `SafeNat`, `SafeInt`, `List`, `Option`, and any later one) rejects
  an attribute on itself, on its constructors and on their fields, since the built-in codec
  would ignore it. The set comes from one registry shared by the elaborator and the JS backend
  (§4.8).
- **Nowhere else** for now: local definitions, `def`s that aren't exported, theorems, tests,
  abilities and their operations, interfaces, instances, synonyms, namespaces, parameters of
  functions and of data types, lambda and `forall` binders, expressions. Each is `E-ATTRIBUTE`
  ("`js.name` can't be used on a theorem; it applies to data types, constructors, fields and
  exports").
- **Not after the fact.** There is no `attribute [js.name "X"] Shape.Circle`. A type's wire
  format is written where the type is, once. Consequence: a library type's format (`Option`,
  `List`, `Pair`) can't be changed by a program; D582 decides it for everyone. A program that
  needs a different format declares its own type.

### 4.3 Namespaces

- `js.` is the JavaScript backend's. Only the compiler defines names in it.
- **Bare names are reserved** for language-level attributes (`@[inline]`, `@[deprecated "…"]`),
  none of which exist yet. Each would come with its own design note.
- Other namespaces (`ts.`, `lsp.`, `test.`) don't exist; using one is `E-ATTRIBUTE-UNKNOWN`. If
  external tools ever need attributes, the way in is a registered namespace (Rust's tool
  attributes), not "anything unknown is ignored". Adding one later is compatible with rejecting
  it today.
- **The registry is closed** and is the single source for validation and for the reference
  documentation (D597, confirmed by the review).

### 4.4 What an attribute may change

Draft 1 said "an attribute never changes what a program means". That promised too much: an
invalid attribute is an error, an export rename can resolve an otherwise clashing public name,
and the JS attributes deliberately change what a JS caller sees. The guarantee is now precise:

> **Valid `js.*` attributes don't change the checked core declarations, the kernel's judgments,
> or the evaluation of Stitchwort values. They specify the external JavaScript representation
> and are validated separately.**

So, ignoring source locations, changing valid JS metadata leaves the checked core and its
logical hashes as they were. It does **not** promise that every stage of compilation behaves
the same (validation can fail), nor that removing an attribute still yields a valid JS interface
(two types might then share a TS name). Inside Stitchwort nothing observes them: patterns,
`Show`, `==`, the order, `stitchwort run`, `stitchwort test` and proofs see Stitchwort names.

Later attribute kinds are judged against this one by one, in their own notes:

| Future kind | Relation to the guarantee |
|---|---|
| `inline` | A semantics-preserving compilation hint: may change generated code, performance and generated-code cache keys; not the core or evaluation |
| `deprecated` | Preserves logical meaning; deliberately changes diagnostics (warnings) |
| `simp`-style lemma registration | Changes proof elaboration and whether automation succeeds. The kernel still checks the result, so soundness holds, but this is *not* "doesn't change elaboration": its own category, its own note |
| Proof-backed implementation replacement (Lean's `csimp` style: a replacement plus an equality proof) | Can fit a semantics-preserving compilation category, under the backend's correctness obligations |
| Unchecked `implemented_by` (execution may disagree with the checked definition) | **Kept outside this contract.** It adds a trust obligation; whether it ever exists, as an attribute or a keyword, is a separate decision about trust, not syntax |

A feature that changes the core or typing stays ordinary syntax or a keyword (`export`,
`instance`, `theorem`, `decreasing`, `auto`).

### 4.5 The first set

All three apply only at the JS boundary: the *encoded* objects an export returns, the objects it
*decodes*, and the `.d.ts`. Inside the generated module, values keep `tag` and Stitchwort names.

#### `js.tag "KEY"` (on a data type)

The discriminant property of this type's variants is `KEY` instead of `tag`.

- Applies to a data type with a tag: not a record (`E-ATTRIBUTE`: "a record has no tag").
- `KEY` must be non-empty and not `__proto__` (`E-ATTRIBUTE`).
- `@[js.tag "tag"]` is exactly the same as writing nothing ([§4.6](#46-resolving-a-types-representation)).
- Decoding reads `own(x, KEY)`; messages say "no `type`; expected "CIRCLE" or "POLYGON"".

#### `js.name "NAME"` (on a constructor, a field, a data type, or an export)

| On | Changes | Rules (`E-JS-NAME-CLASH` / `E-ATTRIBUTE`) |
|---|---|---|
| a constructor | its discriminant value | non-empty; distinct from every other constructor's value in the type (after resolution). Any other string is allowed, including `"__proto__"`, `"constructor"`, `"toString"` |
| a field with an encoded slot (variant or record) | its key | non-empty; not `__proto__`; distinct from the other encoded keys of the same constructor and from the type's tag key (after resolution) |
| a data type | its name in the `.d.ts` (`export type NAME`) | a TS identifier, not reserved, not a name the generated module declares itself; two boundary types with the same TS name stay `E-EXPORT`, but now one can be renamed |
| an `export def` | the name the module exports it under | a JS identifier, not reserved, not a name the generated module exports itself (`StitchwortInputError`, `StitchwortResourceError`, and any later one); two exports with the same JS name stay `E-EXPORT` |

- **"Exactly `NAME`" means no key mangling**: no `$` for primes, no prefix. The generated JS and
  TS still write it as a correctly escaped string literal (`js_string_literal`, `ts_key`), so
  quotes, backslashes, control characters and non-ASCII text round-trip.
- **A name is checked where the attribute is written**, when the type is declared, even if the
  type never reaches an export. Clashes that only exist at the boundary (two types' TS names, an
  export against the module's own names) are found at the export, as today.
- **Generated public names** are checked as one namespace: the module's own exports (the two
  error classes today), every emitted type alias (including `Option` when a nested one makes it
  appear), and every export. A later runtime export joins `MODULE_NAMES` and is thereby
  reserved. *Private* helpers are not part of this: they are already allocated so that no export
  can collide with them (exports are re-exported as `export { wrapper as name }`), and that stays
  an invariant, not a list of names users must avoid.
- The Stitchwort name is still used everywhere inside the language: patterns, `Show`, error
  messages about the program, the playground's value display. Hover shows both
  ([§7.4](#74-tooling)).

#### `js.nullable` (on a field of type `Option T`)

The field is a **required, nullable** property: `T | null`.

| JS input for `label` | Decoded as |
|---|---|
| `"hello"` | `Some "hello"` |
| `null` | `None` |
| the property is missing | error: `label: missing` |
| `undefined` | error: `label: expected a value or null, not undefined` |

- **Encode**: `None` is `null`, `Some v` is `v`'s encoding. The property is always written.
- **`.d.ts`**: `readonly label: string | null`, the same type for inputs and outputs, and it is
  now exact for both: what the module accepts is what it returns. (Separate input and output
  types, `label?: string | null | undefined` in, `label: string | null` out, would be needed only
  for a lenient decoder; not now.)
- The field's type must be `Option T` after unfolding synonyms (`E-ATTRIBUTE`: "`js.nullable`
  needs a field of type `Option T`; this one is `Text`"). The field must have an encoded slot.
- **Nested.** On `Option (Option T)`, `null` is the outer `None`; the inner `Option` is the
  tagged object as D582 already makes it (`Option<T> | null`), so `None`, `Some None` and
  `Some (Some v)` stay distinct. The same holds when the inner `Option` arrives through a type
  parameter (`type Box a = | MkBox (@[js.nullable] v: Option a)` at `Box (Option Nat)`): the
  runtime's `payload` already turns an option of an option into the tagged form after the
  parameter is filled in (`lib.rs:887`) **[checked]**, and a test covers it.
- **Without the attribute**, D582 applies unchanged: in a *record* field, an optional property
  `label?: string` (missing or `undefined` is `None`, `None` leaves it out); in a *constructor*
  field, a required `label: string | undefined`; `null` refused in both. `js.nullable` is the
  per-field opt-in to `null`; the type-level `Nullable` mentioned in DESIGN.md §12 as undecided
  is not needed for this.

#### Not in the first set: casing helpers

A `rename_all`-style attribute would save writing `js.name` on every constructor of a long
enum. **Deferred** (D599): explicit `js.name` covers the motivating case. If one comes, it is two
attributes on the type, one for constructor tag values and one for field keys (serde had to
split `rename_all` and `rename_all_fields`), specified by exact examples rather than by a
convention name alone, at least: `HTTPRequest → http_request`, `centerX → center_x`,
`Polygon2D → POLYGON_2D` (or whichever the note decides), with an explicit `js.name` winning and
the clash checks of §4.6 run on the transformed names.

### 4.6 Resolving a type's representation

Draft 1 kept today's `$tag` fallback (a variant field called `tag` silently got the key `$tag`)
but turned it off as soon as `js.tag` was written, so `@[js.tag "tag"]` and no attribute
differed. Draft 2 has one rule for every tagged type, with or without attributes, and one place
that applies it:

1. **The tag key**: `js.tag`'s argument, else `"$tag"` (D612 as amended; draft 2 said `"tag"`).
2. **Each constructor's tag value**: its `js.name`, else its Stitchwort name.
3. **Each encoded field's key**: its `js.name`, else its name with each `'` as `$`. No other
   change: no `$tag`, no `$__proto__`.
4. **Check**, on these final values: tag values distinct; per constructor, keys distinct and
   none equal to the tag key; no key `__proto__`. A failure is `E-JS-NAME-CLASH` at the
   offending field or constructor, with a note suggesting `js.name` (for a field called `tag`:
   "add `@[js.name "$tag"]` to keep today's key, or choose another").
5. **Store** the result once, as the type's `JsRepr` (tag key, tag values, per-field external
   keys in declaration order, nullable flags, TS name). The codec tables (`define`) and the
   `.d.ts` printer (`ts_alias`) both read it; neither derives names on its own.

A field may still have the key `"$tag"`, by asking for it. Internal names are a separate matter:
inside the module, field keys keep `field_key`'s escaping (`$tag`, `$__proto__`, `$i` for a
repeated name), so internal and external keys are independent, and the codec maps between them.

A record has no tag, so steps 1–2 don't apply and a field `tag` is fine, as today.

**When a clash in an *unattributed* type is reported** is D612: such a type is often never
exported (`examples/accept/dependent-fields.sw` has a constructor field `tag`), so the
recommendation is to report its clash when an export reaches it, while a type with any `js.*`
attribute is checked where it is declared.

**D612 as decided (amended by Matt).** The default tag key is `$tag`, not `tag`. A Stitchwort
identifier starts with a letter or `_` and holds only letters, digits, `_` and `'`
(`crates/syntax/src/lexer.rs`, the identifier rule), and a prime becomes `$` only after the
first character, so no field's default key can be `$tag`: a field called `tag` simply keeps the
key `tag`, and no type without attributes can have a tag clash. The only default key left that
can fail is `__proto__` (and a constructor with two fields of one name, which only the compiler
makes): it is `E-JS-NAME-CLASH` at the field, noted at the export, when an export reaches the
type. A type with any `js.*` attribute is checked where it's declared, including against a
chosen tag key (`@[js.tag "kind"]` on a type with a field `kind`).

### 4.7 A complete example

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

### 4.8 Where it lives in the compiler

- **`crates/syntax`**: a token for `@[`, counted as an opening bracket wherever brackets are
  counted (§4.1); an `Attribute { name: Name, arg: Option<(String, Span)>, span }`; an
  `attrs: Vec<Attribute>` on *every* declaration (one generic wrapper, or a field on each
  `Decl` variant; the implementation chooses), on `CtorDecl`, and on `Binder` (record fields
  are binders already). `split_decls` joins attribute-only groups to the next group and doesn't
  split inside an open `@[`. The parser checks only the grammar; it knows no attribute names.
- **`crates/elab`**: one module, `attributes.rs`, holding **the** registry: name, allowed
  targets, argument kind, one-line doc, long doc. Each target's elaboration hands its attributes
  to it; every other path reports them (§4.2). It validates (unknown, place, argument,
  duplicate, encoded slot, special-codec type), resolves each attributed type's representation
  (§4.6), and fills two side tables, roughly
  `js_repr: HashMap<DataId, JsRepr>` and `js_export_names: HashMap<DefId, String>`.
  Unattributed types get their default `JsRepr` from the same resolver, computed by the JS
  backend on demand. Lifted helpers, derived instances and everything else ignore the tables.
- **The special-codec registry** moves to one place both crates read: `crates/core`'s registry,
  which already names `Builtin::SafeNat` and `Builtin::SafeInt` (a predicate "this data type has
  a built-in boundary form"). `crates/elab` can't read `crates/rt`, where the hashes are; the JS
  backend keeps its hash comparison as a second check that the built-in really is the expected
  declaration, but no longer keeps its own list.
- **`crates/core`**: otherwise unchanged. The kernel never sees attributes.
- **`crates/js`**: `define` writes, per constructor, the external tag value, and per field, the
  external key next to the internal one; the decoder reads external keys and builds internal
  objects (it already builds fresh objects, so this costs nothing extra); the encoder does the
  reverse; nullable fields get a small leaf-like wrapper; `ts_alias` and `ts_type` use the
  external names. Function bodies, `field_key_at` for internal access, and the internal tag are
  untouched.

## 5. Errors

| Code | When | Example message |
|---|---|---|
| `E-ATTRIBUTE-UNKNOWN` | a name not in the registry, in any namespace | "unknown attribute `js.rename`; did you mean `js.name`? The `js` attributes are `js.tag`, `js.name`, `js.nullable`" |
| `E-ATTRIBUTE` | a known attribute on a target it doesn't apply to (including theorems, non-exported `def`s, function and lambda binders, data-type parameters, namespaces, local definitions); a missing argument or one where none is taken; the same attribute twice on one target; `js.tag` on a record; `js.nullable` on a non-`Option` field; a field attribute on an erased field; any attribute on or inside a special-codec type; an attribute on a binder with two names | "`js.tag` applies to a data type, not a constructor" |
| `E-JS-NAME-CLASH` | after resolution (§4.6): two constructors with the same tag value, two encoded fields of one constructor with the same key, a field key equal to the tag key, a key `__proto__`, a type or export name that isn't a valid, non-reserved JS identifier | "two constructors of `Shape` cross as `"CIRCLE"`: `Circle` (here) and `Ring` (line 4)" |
| `E-EXPORT` (existing) | boundary-wide clashes: two boundary types with one TS name, two exports with one JS name, a type or export name equal to one the module declares itself | as today, naming the attribute when one is involved |
| `E-PARSE` (existing) | malformed `@[…]`, including a non-string argument or two arguments; attributes with no declaration after them | "attributes must be followed by the declaration they apply to" |

Every attribute error points at the attribute's span. There's no warning for an attribute on a
type that no export reaches: types are often declared before the export that uses them. The
codes above are the intended ones; the exact code for an argument-shape mistake follows from
whether the grammar or the registry catches it (§4.1).

## 6. Identity: hashing and caches

### 6.1 The question

Content hashes in Stitchwort decide when a test reruns, which built-in codec applies to a
type, and whether a cached cross-unit reference still matches. Should `js.*` attributes be part
of a data type's hash? Decided: **no** (D598, option B). This section states what that decision
does and doesn't promise.

### 6.2 Today's precedent points both ways

- **For hashing them:** data types are nominal, and their hash *already* includes facts that
  matter only to JS: the `record` flag "because it changes the JS representation", and field
  names partly because they are JS keys (`hash.rs`, `fn ctors`) **[checked]**.
- **Against:** names of definitions aren't hashed; Unison's model is that names and metadata live
  beside the hash. The field-name reason is weaker after this note, since a field's JS key is no
  longer always its name; field names stay hashed for their other reason (they decide which
  field `p.name` means). The record flag also has source-language reasons (a record has
  projections and `{ … }` syntax), so it isn't revisited here.

### 6.3 Options (as reviewed)

**(A) Hash `js.*` attributes into the data type**, as an opaque blob the kernel never reads.
Renaming a JS key would change the type's hash and every dependent's, rerunning tests that can't
observe it; and it still wouldn't identify the JS interface, since export names stay unhashed
(the review's point). Rejected.

**(B) Not hashed; side tables** (**decided**). The logical hash is unchanged by attributes. The
elaborator keeps `js_repr` and `js_export_names`; the check cache stores both; the JS backend is
the only reader. The kernel is untouched.

**(C) B plus a boundary-shape fingerprint now.** Deferred: no consumer yet. §6.4 fixes what it
would contain, so that the contract is clear before anything relies on it.

### 6.4 The identity contract

**A logical declaration hash does not identify a JavaScript interface or a generated
artifact.** Anything that caches generated JS or `.d.ts`, compares APIs between releases, or
otherwise depends on the boundary must key on more than the logical hash. Three identities,
kept apart:

| Identity | Made from | Used for |
|---|---|---|
| **Logical** (exists: the content hash) | the checked declaration and its logical dependencies | the test cache, cross-unit references in the check cache, the hash-keyed built-in codecs |
| **Boundary-shape fingerprint** (deferred, option C) | the module's public export names (after `js.name`); for each export, the *effective* schema of every type its inputs and output reach: tag keys and values, field keys, optional / nullable / `undefined` policy, special codecs (`SafeNat` as `number`); the emitted TS names; the relevant codec policies (what's refused). *Effective* means after defaults: D582 changed the schema of every `Option` with no attribute involved | "did this release change the JS API shape?", e.g. a hash written into the generated module's header and compared in CI |
| **Generated-artifact cache key** (none yet) | the implementation's logical dependencies, the boundary metadata, the compiler and backend version, and the options that affect output (e.g. `Text` as a JS string) | caching generated `.js`/`.d.ts` |

The fingerprint deliberately leaves out implementation hashes: an implementation-only edit
shouldn't change "the API shape". And it detects changes in what it includes; it is not a
proof of compatibility (an export's accepted inputs can change, through a precondition, without
the printed TypeScript changing).

**Which results stay reusable after a metadata-only edit.** Changing JS representation metadata
preserves logical test identities. So:

- **Reusable**: `stitchwort test` results, `stitchwort run` and evaluator results, proofs, the
  kernel's checks.
- **Not reusable; each must depend on the metadata**: extraction snapshots, JS integration and
  round-trip tests, `.d.ts` type-checks, codec refusal tests, and any later generated-artifact
  cache. Today these aren't cached by hash at all (they run whenever their test suite runs), so
  nothing has to change now; the rule is for whoever adds such a cache.

**Ownership.** Within a build, each data type and export has exactly one effective
representation, owned by the unit that declares it; its metadata travels with that declaration
(in that unit's cache entry, remapped with its ids). A logical hash alone never selects or
overwrites representation metadata: no table is looked up by hash, and a dependent's cache entry
never carries another unit's `js_repr`. Draft 1 claimed that equal hashes with different
representations "can only be the same type after an edit"; that is dropped, since future
content-based deduplication or separately loaded dependencies could break it. The ownership rule
is what matters, and it is stated for future code, not because of a known failure today.

**Built-in codecs.** The hash-keyed codecs (`NAT_DATA_HASH`, `SAFE_NAT_HASH`, …) are safe because
special-codec types reject attributes anywhere inside (§4.2): a type the hash selects for a
built-in codec never has metadata that the codec would ignore.

### 6.5 The check cache

- **Both tables are persisted and remapped**: `js_repr` (keyed by `DataId`) and
  `js_export_names` (keyed by `DefId`) join the entry's `Tables`, written through the same
  reference scheme as `records` or `by_data` (an index into the unit's own declarations, or an
  external dependency by full path and expected hash), and read back through it, so the ids are
  correct after loading at any position. The format number is bumped.
- **Invalidation needs nothing new**: the key covers the unit's text and its dependencies' keys,
  so an attribute edit re-elaborates its unit and every unit that depends on it **[checked]**.
  The planned "early cutoff" (check-cache.md §4.3: key a dependent on the exported hashes and side
  tables rather than the text) must include both tables in what it compares.
- **Defence against "forgetting a table"**: the warm-versus-cold comparisons
  (`crates/cli/tests/check_cache.rs`) gain an attributed fixture and compare extraction output,
  and the acceptance test in §9.2 covers a metadata-only edit across two units.
- `docs/core.md`'s list of what's hashed gets one line: "JS representation attributes are
  excluded from logical content hashes."

## 7. Interactions

### 7.1 Derived instances and `Show`

Unchanged. `==`, the order and `Show` are about Stitchwort values; `Show` prints `Circle`, not
`"CIRCLE"`. A program that wants the JS name as text writes a function (or, later, a
reflection feature; out of scope).

### 7.2 Records

`js.name` on a record field changes its key; `js.tag` on a record is an error. D582's optional
properties apply to records' `Option` fields; `js.nullable` replaces that with a required
`T | null` per field.

### 7.3 Codecs, `.d.ts`, validation

- **Own properties, each read once.** Decoding still reads only own properties; each property is
  read once into a captured value, and the nullable check and the decoding of `T` both work on
  that value (as `own` does today). A test uses getters that count reads, on the tag property and
  on a nullable field.
- **Dispatch on tag values is prototype-safe.** Tag values are looked up in a `Map` (today's
  `info.ctors`), never as properties of an ordinary object, so `"__proto__"`, `"constructor"`,
  `"toString"` and `"hasOwnProperty"` dispatch correctly. Any later table keyed by an external
  string (a field-key lookup, a reverse map) must be a `Map` or a null-prototype object too. An
  object literal with a quoted `"__proto__"` key is not safe: in an object literal that spelling
  still sets the prototype.
- **`__proto__` as a key** stays forbidden (§4.5): the encoder writes keys by assignment, which
  for `__proto__` would set the prototype. Lifting the ban later means writing that key with
  `Object.defineProperty`; not now.
- **Escaping, not mangling.** External strings reach the JS and the `.d.ts` through
  `js_string_literal` and `ts_key`. The awkward-names property test
  (`awkward_names_never_collide`, `crates/cli/tests/extract.rs`) extends to generated `js.name`
  values drawn from a pool with `tag`, `"$tag"`, `constructor`, `toString`, `""` (expected to be
  refused), `"0"`, `"10"`, `"a-b"`, a double quote, a backslash, a newline and other control
  characters, a lone `$`, and non-ASCII text (accented letters, a character outside the BMP).
  `__proto__` is tested twice: refused as a key, accepted as a tag value.
- **Order.** Fields are decoded, checked and *written* in declaration order. That is the whole
  promise: a JS object enumerates integer-like keys (`"0"`, `"10"`) in numeric order before all
  other string keys, so a type whose external keys include such strings doesn't enumerate in
  declaration order, and the note doesn't claim it does. Keys like `"0"` stay allowed.
- **Paths in messages** use the external keys (`d.shapes[2].center_x: expected a non-negative
  bigint`), since they describe the JS input.
- Validators of record proof fields (DESIGN.md §12) are unaffected: they run on decoded values.
- **`.d.ts`**: external names; keys that aren't identifiers quoted; a renamed type's alias name;
  checked with `tsc --strict --exactOptionalPropertyTypes` as today.

### 7.4 Tooling

- **Hover** on an attribute: its documentation from the registry (one line plus the long doc).
  Hover on a constructor, field or type with JS attributes adds a line: "crosses to JS as
  `{ type: "CIRCLE", … }`".
- **Completion** (when the server gets it): after `@[`, the attributes valid at that place.
- **Highlighting**: the VS Code grammar and the playground's colouring get an `@[ … ]` scope.
- **Outline and navigation**: attributes aren't symbols; go to definition on an attribute name
  could open its section of the docs (later).
- **Formatter**: none exists; when one does, attributes go on their own line before a
  declaration and inline before constructors and fields.

### 7.5 The parallel lanes

- **SW-339 (D582)** has landed (`2ba211a0`); `js.nullable` builds on its optional-property
  codec. D583 (whether `null` is refused by default) is settled by what landed: `null` is
  refused, and `js.nullable` is the per-field opt-in.
- **SW-340 (variant fields, [variant-fields.md](variant-fields.md))**, being revised in
  parallel. A logical field shared by several constructors may have a **different `js.name` in
  each**: the decoder picks the constructor by the tag, then maps that constructor's external
  keys to its internal fields, so a shared projection keeps working on the logical field and the
  generated TS union describes each branch exactly. Draft 1's "a shared field's `js.name` must
  agree across constructors" is removed; agreeing names would be a separate API policy, and it
  would prevent matching some existing schemas. Example:

  ```
  type Message =
    | Note    (@[js.name "note_id"] id: Nat) (body: Text)
    | Picture (@[js.name "picture_id"] id: Nat) (url: Text)
  ```

  crosses as `{ tag: "Note"; note_id: bigint; body: string } | { tag: "Picture"; picture_id:
  bigint; url: string }`, and `m.id` (if variant-fields provides shared access) still works inside
  Stitchwort. The two notes need only agree that external keys are per constructor.

### 7.6 Codec laws

For every boundary type, with `≈` meaning equal as Stitchwort data (ignoring erased proofs and JS
object identity):

1. **`decode(encode(v)) ≈ v`** for every value `v`.
2. **`encode(decode(x)) = canonicalize(x)`** whenever decoding `x` succeeds, where
   `canonicalize` drops properties the type doesn't have (extra properties are ignored today),
   writes keys in declaration order, and, for a *record*'s unannotated `Option` field, removes
   a property that was present as `undefined`. With strict `js.nullable` there is no other
   accepted non-canonical form.

The extraction round-trip tests check law 1 on generated values and law 2 on hand-written
inputs, including the nullable and nested cases.

## 8. Alternatives considered

**8.1 A clause on the type declaration.** `type Shape = … with js { tag = "type", Circle =
"CIRCLE", Polygon.label nullable }`. Keeps all JS facts in one place, but repeats every
name it changes (drift, checked but noisy), is far from the constructor it describes, and is a
new syntax form useful only to JS. Attributes are one general form for this and later uses.

**8.2 A separate `export encoding` block** (Swift `CodingKeys`, aeson `Options`, STJ's contract
model). Like 8.1 but anywhere, possibly several per type. Real advantages: logic types stay
clean, and a type could have two encodings (API v1 and v2) or a library type could get one.
Costs: a new top-level form with its own ordering and scoping rules, and the format no longer
visible at the type. Not now. The attributes on a type define its **default** JS encoding;
named encodings could be added later without changing that. Until then a mirror type plus a
conversion is the escape hatch. What would reopen it: concrete pressure to expose one large type
through several API versions, or to adapt an imported type without duplicating its structure.

**8.3 Naming convention.** Name the constructor `CIRCLE` and the field `center_x`. Works
today for values that happen to be Stitchwort names, at the cost of pattern matches that read
like JSON; impossible for the tag key and for keys that aren't Stitchwort names. Rejected.

**8.4 Pragmas in comments** (`-- @js.name CIRCLE`). Comments that change behaviour are
hidden semantics, the parser drops comments today, and a typo would be a comment. Rejected.

**8.5 Value-level codecs.** Arbitrary user-written decoder functions (Elm decoders, aeson's
functions) would be ordinary code at the boundary, losing the own-property, single-read, cycle
and sharing guarantees and the generated `.d.ts`. Rejected for this need. A *declarative* codec
language is a different matter: it could compile into the same checked tables and keep those
guarantees. It is deferred for scope, not ruled out.

**8.6 Build-wide options** (`--js-tag-key type`, kotlinx naming strategies, STJ naming policies).
Wrong granularity: one app's types disagree with each other. Rejected.

**8.7 Lean-style after-the-fact and scoped attributes.** `attribute [js.name "X"] Shape.Circle`,
`local`/`scoped`. Makes a type's format depend on what's imported and in what order. Rejected.

**8.8 `#[…]` (Rust) or `@name(…)` (Scala, Kotlin, ReScript).** `#` is free too, but every
Scala/TS-like language and ReScript use `@`. `@name("x")` with parentheses would look like a call
in a language whose calls are `f x`, and `@js.name "x"` without brackets can't say where an
argument ends before a constructor name. `@[…]` also groups several. Lean uses exactly this.

## 9. Staging, cost and tests

### 9.1 Stages

Sizes are rough **[inferred]** from comparable lanes (records' boundary stage, SW-337).

| Stage | Content | Depends on | Size |
|---|---|---|---|
| 1 | Grammar, AST on every declaration and binder, `@[` as a bracket, `split_decls`; the registry and every error, including rejection on every unsupported target; the shared special-codec registry; the representation resolver (§4.6) and the uniform clash rule (D612); `js.tag`; `js.name` on constructors and fields; codec and `.d.ts`; both check-cache tables; examples (`examples/extract/attributes.sw`, `examples/reject/attribute-*.sw`); updating `examples/extract/names.sw` for the dropped `$tag`/`$__proto__` fallbacks; extract runtime tests; awkward-names test; docs (`syntax.md`, DESIGN.md §12, `docs/core.md`'s hashing line) | D597, D598, D612 | one lane, roughly 700–1000 lines with tests |
| 2 | `js.nullable` (strict) | stage 1 | small |
| 3 | `js.name` on types and exports, checked against the generated public namespace; hover lines; grammar colouring | stage 1 | small |
| later | casing helpers, string-literal encodings for field-less variants, boundary fingerprint (§6.4), other namespaces or bare attributes | each its own decision | — |

### 9.2 Acceptance tests

**The metadata-only-edit cache test** (the most likely contract to be missed):

1. Unit A declares an attributed type (`Shape` as in §4.7).
2. Unit B imports it and exports a function using it.
3. Build, filling the check cache.
4. Change only A's representation metadata (a `js.name` on a field).
5. Build again warm, and build fresh with no cache.
6. The two builds give the same generated JS behaviour and the same `.d.ts`, both showing the new
   key; and every logical hash is the same as before the edit.

Then the same for an **export rename** in B (`@[js.name "renderDrawing"]` → `@[js.name
"draw"]`), which exercises `js_export_names` rather than `js_repr`. The fixture must be
attributed; a differential test over the library, which has no attributes, would pass without
testing this.

**And:**

- Tag key, tag value and field key all differ from the Stitchwort names at once, and pattern
  matching and field access inside Stitchwort still work.
- `js.nullable`: `null` is `None`; a missing property and `undefined` are refused, with paths;
  encode always writes the property.
- Nested options stay distinct with and without `js.nullable`, directly (`Option (Option T)`)
  and through a type parameter (`Box (Option Nat)`).
- The tag property and a nullable field are each read once (counting getters).
- Tag values `"__proto__"`, `"constructor"`, `"toString"`, `"hasOwnProperty"` dispatch
  correctly; `__proto__` as a key is refused.
- Generated declarations compile under `tsc --strict --exactOptionalPropertyTypes`.
- Errors: an attribute on each unsupported target (theorem, non-exported `def`, function
  parameter, lambda binder, data-type parameter, namespace, local definition, interface,
  instance), on an erased field, on a field of a special-codec type; each is an error, none is
  silently accepted.
- `@[js.tag "tag"]` behaves exactly like no attribute, and a field `tag` under either is the
  clash of D612 unless renamed; `@[js.name "$tag"]` restores today's key.
- An export renamed to `StitchwortInputError` is refused; a type renamed to a name another
  boundary type has is refused.

**Parser tests:** a multi-line attribute group whose `]` is at column 0; two groups separated by
a comment; a group on the same line as its declaration; a group before `namespace` (attaches
there and fails, doesn't drift to the next `type`); a group at end of file; attributes on a
constructor after `|` and inside a field's brackets; `@[js.name 123]` and `@[js.name "x" "y"]`
as parse errors.

Risks: the boundary is trusted code, so each stage needs round-trip and refusal tests through a
real JS engine (as `crates/cli/tests/extract.rs` does today); and both side tables must be in the
check cache, or a warm build loses attributes silently (§6.5).

## 10. What we'd like reviewed

Draft 1's questions, with the outcome of the review. A second round, if wanted, would be on
D612, D613 and the identity contract (§6.4).

1. **The rule about meaning (§4.4).** Replaced by the precise guarantee and the table of future
   kinds; unchecked `implemented_by` outside the contract.
2. **Identity (§6).** B confirmed; identity contract, ownership rule, fingerprint contents fixed.
3. **Closed set.** Confirmed.
4. **Placement versus an encoding block.** Confirmed as the type's default encoding.
5. **Clash policy.** Uniform rule (§4.6); any non-empty string, with the obligations of §7.3.
6. **`js.nullable`.** Strict (§4.5).
7. **Casing helper.** Deferred; split and specified by examples if added.
8. **Grammar.** Confirmed; `@[` is a bracket everywhere; argument-shape errors are parse errors.
9. **Missing from the first set.** String-literal encodings for field-less variants next.

## 11. Decisions

| ID | Question | Outcome / recommendation | Alternatives |
|---|---|---|---|
| D597 | Adopt attributes | **Decided, with amendments**: `@[name arg?, …]` before declarations, after a constructor's `\|`, before a field's name; a closed, namespaced registry that is the single source for validation and docs; unknown or misplaced is an error and **every parsed attribute is consumed or rejected**; field attributes only on encoded slots; none on special-codec types; the guarantee of §4.4 replaces "never change meaning" | a `with js { … }` clause (§8.1); an `export encoding` block (§8.2) |
| D598 | Are `js.*` attributes part of content hashes? | **Decided, with amendments: no** (option B). A logical hash does not identify a JS interface or generated artifact; three identities (§6.4); both tables persisted and remapped; ownership rule; fingerprint deferred, with export names in it | (A) hash into the data type; (C) B plus a fingerprint now |
| D599 | The first set | **Decided, with amendments**: `js.tag`, `js.name` (constructors, fields; then types and exports), `js.nullable` **strict** (required property, `null` is `None`, missing or `undefined` refused); per-constructor field names allowed; casing helpers deferred | lenient `js.nullable` (normalising missing/`undefined` to `None`) |
| **D612** | With the `$tag`/`$__proto__` fallbacks gone (§4.6), a variant field called `tag`, or any field called `__proto__`, has no valid default key. When is that reported for a type with **no** `js.*` attribute? | **Decided, amended by Matt: the default tag key is `$tag`** (instead of `tag`). No Stitchwort field can produce the key `$tag` (identifiers start with a letter or `_`; primes become `$` only after the first character), so a field called `tag` simply stays `tag`, and the silent `$tag` field-renaming fallback goes away. A field called `__proto__` (no valid default key) is reported, `E-JS-NAME-CLASH` at the field and noted at the export, **only when an export reaches the type**; a type with any `js.*` attribute is checked where declared, including clashes with a user-chosen tag key such as `@[js.tag "type"]` on a type with a field `type`. `examples/extract/names.sw` renames its `__proto__` field with `@[js.name "$__proto__"]` | report at the declaration for every type (simpler; breaks never-exported types with a field `__proto__`); keep the tag key `tag` and report a field `tag` at the export (draft 2's recommendation) |
| **D613** | Where the special-codec registry lives | **Decided: `crates/core`'s registry**: `BOUNDARY_FORMS` and `Registry::boundary_form` next to `Builtin::SafeNat`/`SafeInt`, read by the elaborator to reject attributes and by the JS backend to pick codecs; the backend keeps its hash check as confirmation | a list in `crates/js` re-exported to `elab` (adds a dependency `elab` → `js`); a list in `crates/rt` (same problem) |

D613 is an implementation choice and could be settled without Matt; it is listed because it
moves a fact between crates that both the kernel side and the backend read.

## As built (stage 1)

Built in SW-341's stage-1 lane: the grammar, the registry with every error, the resolver and the
uniform clash rule, `js.tag`, `js.name` on constructors and fields, the codec and `.d.ts`, the
`js_repr` cache table, D612 as amended (the `$tag` default) and D613. Examples:
`examples/extract/attributes.sw`, `examples/accept/attributes.sw`, `examples/reject/attribute-*.sw`
(32 files, one per error and target); `names.sw` and `records.sw` rename their `__proto__` field.
Tests: parser tests in `crates/syntax/src/parser.rs` (`attributes_*`, `misplaced_attributes_*`,
the column-0 `]`, an unclosed group); `crates/cli/tests/extract.rs`
(`attributes_cross_the_boundary_as_declared`, `the_default_tag_key_written_out_changes_nothing`,
`built_in_boundary_types_take_no_attributes`, and `awkward_names_never_collide` extended with
random `js.tag`/`js.name` from the pool of §7.3); the metadata-only-edit acceptance test of §9.2
in `crates/driver/tests/check_cache.rs`
(`an_attributes_only_edit_in_an_imported_namespace_reaches_the_javascript`: warm, cold and fresh
builds give the same module and `.d.ts` with the new key, and no logical hash changes; it fails if
the cache stops restoring `js_repr`).

Deviations and choices, with why:

1. **Not built, later stages:** `js.nullable` (stage 2) and `js.name` on data types and exports
   (stage 3). They aren't in the registry yet, so `@[js.nullable]` is `E-ATTRIBUTE-UNKNOWN` and
   `js.name` on a type or an export is `E-ATTRIBUTE` ("applies to a constructor or a field").
   Per-constructor keys for a shared field need nothing more: keys are already per constructor,
   so they will work once variant fields exist (`attributes.sw`'s `Message` shows the shape).
2. **No `js_export_names` table.** It would be filled only by `js.name` on exports (stage 3), and
   a unit with an export is never cached today: `Elaborator::encode` refuses it ("`f` is
   exported", `crates/elab/src/cache/mod.rs`). The table comes with stage 3, if exports become
   cacheable by then; the export-rename variant of the §9.2 test goes with it.
3. **Where the representation lives.** `JsRepr` and the resolver are in `crates/core`
   (`js_repr.rs`), not `crates/elab`: the JS backend needs the same resolver for an unattributed
   type's default when an export reaches it (D612), and it can't depend on `elab`. The resolved
   value is kept on the data type (`Data::js: Option<Rc<JsRepr>>`) rather than in an elaborator
   `HashMap`, so every consumer of `Globals` (the CLI, the driver, the tests) reads it without a
   second argument, and rewinding removes it with the type. The kernel never reads it and
   `hash.rs` doesn't hash it. The check cache writes it as the `js_repr` table of the declaring
   unit's entry (format 7), by the same data references as `records`, and the canonical dump
   prints it, so the warm-versus-cold comparisons see it. An unattributed type has no stored
   value; the backend computes its default (`js_repr::names`) when needed.
4. **Inside the module nothing changed.** Generated code keeps the tag in `tag` and the field
   keys of `field_key` (`$tag`, `$__proto__`, `$i`); only the codec translates. `define` writes a
   constructor as `[tag, fields]`, with its external tag third only when it differs, and a field
   as `[key, type]`, with `optional` and the internal key third and fourth only when needed;
   `datatype(name, tagKey)` gives a tag key other than `$tag`. So the snapshots of function
   bodies didn't move; the runtime and the codec tables did.
5. **`@[` is two tokens**: `At` (only directly before `[`; `@` alone stays a lexical error) and an
   ordinary `[`. Every place that counts brackets therefore counts it with no change. In
   `split_decls`, a column-0 token inside an open `@[` doesn't start a declaration, except a
   declaration keyword, so an unclosed group can't swallow the rest of the file.
6. **The parser refuses attributes by position** where the AST has no place for them: a
   function's, a type's or an ability's parameter, an index, a function type's or a lambda's
   binder, any `@[` inside an expression (so a local definition), and before `test`, `ability`,
   `namespace` and `import`. Each is `E-ATTRIBUTE` ("attributes can't be used on …"), without
   looking at the names. Data types, constructors, fields and every `def`/`theorem`/`instance`/
   synonym/`export` keep their attributes, and the elaborator's registry consumes or refuses them
   there (in stage 1 it refuses all of the latter). Only `Decl::Data`, `Decl::Signature`,
   `CtorDecl` and `Binder` gained an `attrs` field.
7. **D612's report at an export** labels the type's declaration and the export and names the
   field in the message, rather than labelling the field: the kernel's data type keeps no field
   spans. A type with attributes is checked in the elaborator, which labels the attribute or the
   field. This check also replaced the backend's old "has two fields called `x`" (`E-EXPORT`).
8. **`type` is a keyword**, so no field can be called `type` (§4.2's erased field named `type` and
   §4.7's `Drawing` can't be written as such); the examples use `kind` and `@[js.name "type"]`.
   A record type whose `}` is at column 0 (§4.7) isn't valid layout today, with or without
   attributes; the examples indent it.
9. **Messages name the key**: a decoder says `no type; expected "DOT", "CIRCLE" or "POLYGON"` and
   `unknown type "Circle"`, and without attributes `no $tag; …`.
10. **Built-in boundary types** reject attributes in their own declarations (only the library can
    write those); `built_in_boundary_types_take_no_attributes` checks it with a changed prelude.
    `boundary()` in the JS backend now asks `Registry::boundary_form` first and confirms by hash
    as before.
11. Not done here: hover lines, completion and highlighting for attributes (§7.4; stage 3 lists
    the hover and colouring work).

## Sources

- Rust Reference, Attributes: https://doc.rust-lang.org/reference/attributes.html
- rustc UI test for a misspelt derive helper (`#[sede]`): https://rust.googlesource.com/rust/+/HEAD/tests/ui/macros/missing-derive-1.stderr
- serde container attributes: https://serde.rs/container-attrs.html
- Lean 4 reference, Attributes: https://lean-lang.org/doc/reference/latest/Attributes/
- Lean 4, `implemented_by` and `csimp` (cited by the reviewer): https://lean-lang.org/doc/reference/latest/
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
- ECMAScript, object-literal `__proto__` and property enumeration order (cited by the reviewer): https://tc39.es/ecma262/
- TypeScript, `exactOptionalPropertyTypes` (cited by the reviewer): https://www.typescriptlang.org/tsconfig/#exactOptionalPropertyTypes

**Not verified:** Swift `CodingKeys` (Apple's page didn't render), Lean's and ReScript's
messages for an unknown attribute, serde's exact error for an unknown key inside `#[serde(…)]`,
Gleam's attribute set being closed, Elm/PureScript/Roc having no attribute syntax, TypeScript
decorators' limits. The three reviewer-cited sources were not re-read for draft 2. None of these
changes the recommendation.
