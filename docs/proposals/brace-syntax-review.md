# Proposal: braces after a constructor, and record syntax in the round

**Status:** draft 1, 6 November 2026. Ticket SW-1613 (D2455, Matt, 6 Nov 2026: "maybe kick
that off now as a design session. It should look at other languages. It should try and
consider alternatives."). Nothing is built; this note stops for Matt's decisions
([§10](#10-decisions), Q1–Q6). Written against `main` at `cfa90ebf1`. Migration cost (hashes,
snapshots, sweeps) is not counted; options are judged by where they end up.

It revisits three decisions: **D593 (b)** (braces after a constructor in a pattern name its
fields), **D605 (a)** (the same in expressions, built as D1085) and **D1370 (a)** (keep that
rule, 26 Oct). Related notes: [record-argument-braces.md](record-argument-braces.md) (D1370's
analysis, whose §2 table this note relies on and doesn't repeat),
[variant-fields.md](variant-fields.md) §4 (named-field patterns and construction),
[records.md](records.md), [named-arguments.md](named-arguments.md).

Labels, as in the other notes:

- **[checked]**: read in this repository at the place given.
- **[ran]**: run for this note on 6 Nov 2026 with the release CLI from the main checkout
  (built 09:46 that morning), on scratch files outside the repository.
- **[cited]**: read in the source linked, on 6 Nov 2026 ([§11](#11-sources)).
- **[inferred]**: my reasoning from checked or cited facts.
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [How the rules fit together today](#2-how-the-rules-fit-together-today)
3. [How often each form is written](#3-how-often-each-form-is-written)
4. [Prior art](#4-prior-art)
5. [The alternatives](#5-the-alternatives)
6. [Side by side](#6-side-by-side)
7. [Recommendation](#7-recommendation)
8. [Staged plan](#8-staged-plan)
9. [Evidence still to collect](#9-evidence-still-to-collect)
10. [Decisions](#10-decisions)
11. [Sources](#11-sources)

## 0. Summary

- **The problem.** `Some { name = "tea", price = 3 }` is an error. Braces right after a
  constructor name *that constructor's* fields, and `Some`'s one field is `value`, so a record
  held by `Some`, `Ok`, `Cons` or a wrapper like `SetMask` has to be written in brackets,
  `Some ({ … })`. The error says so, but every AoC agent writes the unbracketed form first:
  2020 days 5, 8, 13 (four times), 14 and 16 each paid a round trip for it, and the bracketed
  reading was the only one that type-checked each time.
- **The numbers.** In the repository's code (§3), a constructor applied to a bracketed record
  is written **about 160 times**, 103 of them in `aoc/`. Building a constructor *by its field
  names*, `Circle { radius = 3, id }`, which is what the rule protects, is written **about 28
  times, all in the feature's own tests and the guide**; never in `aoc/`, `games/` or std.
  Matching by field names, `Circle { id, .. }`, the same: about 40 times, none in application
  code. So the rule favours a form nobody has used yet over the form everybody writes.
- **Why the rule exists** (D593 (b), D605 (a), D1370 (a)). `C { … }` can't mean both "build
  `C` from its fields" and "apply `C` to a record" without one of them depending on the field
  names or the types, and then adding a field (with a default, or matched with `..`) can
  silently change what working code means. That argument is right, and every alternative here
  is checked against it.
- **Prior art.** No language surveyed gives `C { … }` both meanings. The ones with named
  construction by braces (Haskell, Rust, OCaml's inline records) decide it **by how the
  constructor is declared**: a constructor declared with named fields takes braces as its
  fields, any other constructor takes braces as an ordinary record argument (OCaml: `Some { x =
  1 }` is `Some` applied to a record; `Point { x = 1; … }` builds an inline-record constructor).
  Languages with record literals and no named construction (Elm, PureScript, Lean) read
  `C { … }` as `C` applied to a record. Lean builds constructors by name with named arguments,
  `(x := e)`.
- **Recommendation: let the declaration decide (option D).** A constructor declared with its
  fields in braces, `| Meeting { title: Text, minutes: Nat := 30, room: Text }`, is built and
  matched by name exactly as today. Every other constructor, declared with brackets as all of
  them are today (`| Some (value: a)`), takes braces as an ordinary argument, as a function
  does: `Some { name = "tea", price = 3 }`, `Some { guard | facing = … }`, `| Some { name, .. }
  =>`. Which reading applies is fixed by the constructor's declaration, never by field names or
  types, and no edit short of changing the declaration's style changes it. About 140 of the 160
  bracketed records lose their brackets; the 28 named constructions stay as written once their
  types are redeclared with braces.
- **Decisions:** Q1 the direction (D, or keep the rule, or Lean's arrangement), Q2 patterns
  follow, Q3 braces in argument position, Q4 `show`, Q5 constructor defaults through named
  arguments, Q6 the sweep (§10).

## 1. The problem

### 1.1 What people write

From the AoC 2020 notes, in the order the agents met it **[checked]**
(`aoc/NOTES-2020.md:680`, `:1215`, `:2048`, `:3458`, `:3714`, `:4285`;
`docs/research/aoc-2020-friction-days-10-20.md`, "A bracket after a constructor"):

```
| (Some row, Some column) => Some { row, column }          -- day 5: E-UNKNOWN-FIELD
Some { instruction | operation = Nop }                     -- day 8: E-PARSE
Some { operation = Jmp, argument }                         -- day 8: E-UNKNOWN-FIELD
Some { id, offset }      Ok { … }      Witness { … } …     -- day 13, four times
SetMask { bits = … }                                       -- day 14
Ok (Some { … })                                            -- day 16, twice in one test
map.lookupOr Open { row = …, column = … }                  -- day 3: E-PARSE
```

Each is fixed by adding brackets, and the notes say the same thing each time: "It costs a
round trip each time, and the bracketed reading is the only one that typechecks"
(`NOTES-2020.md:3462`). The message itself is good **[ran]**:

```
[E-UNKNOWN-FIELD] Error: `Some` has no field `name`
 6 │ def a: Option Item := Some { name = "tea", price = 3 }
   │ Note 1: `Some`'s fields are `value`
   │ Note 2: braces right after a constructor name its own fields; to build the `Item` it
   │         holds, write `Some ({ … })`
```

So the cost isn't confusion; it is a check cycle per occurrence, paid by every new day, and
brackets that the reader then sees in about 160 places (§3). A quick fix in the editor
wouldn't remove the cycle: the agents who hit this write files and run `stitchwort check`,
they don't use the editor.

### 1.2 What the rule protects

Stitchwort has two things spelt with braces, and they meet after a constructor:

- **Record literals and updates take their type from where they are**: `{ name = "tea", price
  = 3 }` is an `Item` because an `Item` is expected there (records.md; `docs/syntax.md`,
  "Records") **[checked]**. Records are nominal, and a literal doesn't name its type.
- **Named construction and named-field patterns** (variant-fields.md §4): `Circle { radius =
  3, id }` builds a `Circle` from its fields in any order, filling defaults, and `| Circle {
  radius, .. } => radius` matches one by name. Both are the positional form underneath, with
  the same term and hash **[checked]** (`docs/syntax.md`, "Named construction").

D1370's note (record-argument-braces.md §3) shows that `C { … }` can't take both meanings by
looking at the names. Briefly:

1. `Some { value = 3 }` with `Item = { value: Nat, … }` is both readings; some rule has to pick.
2. For `Some { name = "tea" }`, whether `name` belongs to the held record depends on `Some`'s
   field type, `a`, which only the expected type fixes.
3. **Silent change.** Suppose braces fell back to the record argument when the names aren't
   the constructor's. `W { name, .. }` against `W (person: Person)` reads `person.name`. Add a
   field, `W (person: Person) (name: Text)`, and the same pattern reads `W`'s own `name`: it
   still checks and returns a different value (variant-fields.md §4.2). In an expression, a
   default on the other field does the same.

Any change must keep point 3: no edit to a type should make working code mean something else
without an error.

## 2. How the rules fit together today

Every place braces appear, and what decides their meaning **[checked]** (`docs/syntax.md`,
"Records", "Field defaults", "Named arguments"; `crates/syntax/src/parser.rs` `atom` (4334),
`ctor_fields_expr` (4419), `record_body` (4478); `crates/elab/src/records.rs` `ctor_fields`
(475), `not_a_ctor` (573)):

| Written | Meaning | Decided by |
|---|---|---|
| `type P = { x: Nat, y: Nat }` | record type (nominal) | declaration |
| `{ x = 1, y }` | record literal; `y` alone is `y = y`; defaults fill | expected type, else the field-name rule at the end of the declaration |
| `{ p \| x = 2 }` | record update (also shared-field update on variants) | the base's type |
| `\| { x, .. } =>` | record pattern | the matched type |
| `Circle { id = "a", radius = 1 }` | named construction (D605 (a)) | `Circle` is a constructor |
| `\| Circle { radius, .. } =>` | named-field pattern (D593 (b)) | `Circle` is a constructor |
| `Some ({ … })`, `\| Some ({ x, .. })` | constructor applied to a record | the brackets |
| `f { … }`, `x.f { … }`, `Mk { … }` (an uppercase function) | function applied to a record | not a constructor |
| `C { … } x` | E-PARSE: braces take no further arguments | parser |
| `f C { … }` | E-PARSE: braces after `C` as an argument need brackets | parser (uppercase name) |
| `Some { r \| a = 1 }` | E-PARSE: an update isn't a construction | parser |
| `Item { … }`, `Item` a record type | E-NOT-A-CONSTRUCTOR: write `({ … }: Item)` | elaborator |
| `-> {IO} Nat` | ability row | type position, a type after the braces |
| `Circle (id := "a") (radius := 1)` | named arguments: positional call, **no defaults filled** | parameter names |
| `[n := k]` | implicit argument by name | parameter names |

And what the printers do **[ran]**:

```
> Circle { id = "a", radius = 1 }        -- `stitchwort eval`
Circle "a" 1: Shape                      -- positional, always
> Some ({ name = "tea", price = 3 })
Some ({ name = "tea", price = 3 }): Option Item   -- bracketed so it reads back (§4.5)
```

Three things stand out:

- **Constructors are the only callee where braces aren't an argument.** For functions, dot
  calls and pipes, `f { … }` works (D1370's table). The capital letter decides it in the
  parser, so `readPackets Filling { unread = … }` is an error even though `Filling` has no
  fields at all.
- **Named construction fills defaults; named arguments don't.** `Circle { radius = 1 }` uses
  `id`'s default; `Circle (radius := 1)` is a function still waiting for `id`. For a `def`,
  named calls do fill defaults (`makeBooking "a" (duration := 30.0)`). So today the brace form
  is the only way to use a constructor field's default **[checked]** (`docs/syntax.md`, "Field
  defaults", "Parameter defaults": "Not yet: … a constructor application doesn't fill field
  defaults").
- **The guide spends a section on the mistake.** `docs/guide/03-data.md`, "A common mistake:
  braces after a constructor", exists only to explain the error.

## 3. How often each form is written

Counted on `main` at `cfa90ebf1` by a script over every `.sw` file in `aoc/`, `games/`,
`examples/`, `crates/elab/src/std`, `web/guide`, and `docs/guide` (its `.sw` examples and the
code blocks of its `.md` chapters), with line comments, block comments and string contents
removed first. An uppercase name followed by `{` is a brace-after-constructor use; it is a
pattern when it comes before `=>` on an arm line or its braces contain `..`, otherwise an
expression. An uppercase name followed by `({` is a bracketed record argument, classified by
its contents (a literal, an update `{ e | … }`, or a literal with `: T`). Hits were then read
by hand: uppercase *functions* (`WellFormed { … }`, `Rectangle { rows }`, `AtR { … }`, both
legal today) and `examples/reject/` files are taken out of the "real" columns below. The
counts are close, not exact.

| Form | aoc | games | std | examples (accept) | guide, tour | Total |
|---|---|---|---|---|---|---|
| Constructor applied to a bracketed record, `Some ({ … })` | 103 | 1 | 12 | 37 | 6 | **~160** |
| … of which a plain literal | 69 | 0 | 8 | 31 | 5 | ~113 |
| … an update, `Some ({ r \| … })` | 22 | 0 | 3 | 1 | 0 | ~26 |
| … an annotated literal, `Ok ({ … }: T)` | 12 | 1 | 1 | 3 | 0 | ~17 |
| … after a fieldless constructor in argument position, `f Filling ({ … })` | 9 | 0 | 0 | 1 | 0 | ~10 |
| Named construction, `Circle { … }` (a constructor) | **0** | **0** | **0** | ~20 | 8 | **~28** |
| … with a punned field (`{ id, ref = 2 }`) | 0 | 0 | 0 | 1 | 1 | 2 |
| … a field given a record by name, `Some { value = { … } }` | 0 | 0 | 0 | 3 | 0 | 3 |
| Named-field pattern, `\| Circle { … }` | **0** | **0** | **0** | ~35 | 4 | **~39** |
| … with `..` | 0 | 0 | 0 | ~33 | 4 | ~37 |
| … with a punned field | 0 | 0 | 0 | ~22 | 4 | ~26 |
| Named arguments on a constructor, `Circle (id := …)` | 0 | 0 | 0 | 3 | 0 | 3 |
| Record literals `{ f = … }` (any) | ~1280 | ~170 | ~250 | ~690 | ~120 | ~2500 |
| Record updates `{ e \| … }` (any) | ~90 | ~70 | ~20 | ~140 | ~6 | ~330 |

(The rows "of which" are from a second pass and add up to the first row only roughly; the
plain-literal row includes the multi-argument `Cons ({ … }) rest` and `Witness ({ … }) proof`
forms, and a handful of uppercase *functions* and propositions (`List.Mem`, `Represents`,
`Holds`, `OnMap`, `Outputs`), where the brackets are needed only for a `: T` annotation or
are already optional.) For scale, `aoc/` and `games/` declare about 85 constructors with explicit fields
(52 with one, 33 with two or more) and 152 record types; none of them is ever built or
matched by field names **[ran]** (same script).

What this says: the domain-records style (D2363, "records by default") puts records *inside*
`Option`, `Result`, `List` and small wrappers, so the bracketed form is the everyday one.
Named construction is two weeks old (built 23 Oct) and may grow, but its users so far are the
feature's tests and the guide pages that teach it.

## 4. Prior art

Sources and dates in §11. "Lit." is whether the language has a record literal that doesn't
name its type.

| Language | Lit. | Build a constructor by field names | `C { … }` for a constructor that holds a record | Update | Patterns by name |
|---|---|---|---|---|---|
| **Lean 4** | yes, `{ x := 1 }`, type from the expected type [1] | named arguments `C (x := e)`; for structures also `{ x := e }` [1, 2] | `C` applied to a structure instance (`addPoints { x := 1.5, y := 32 } { … }`) [3] | `{ s with x := 1 }` [1] | named arguments and `..` in patterns [2]; anonymous `⟨a, b⟩` when one constructor is expected [1] |
| **Haskell** | no | `C { x = 1 }`, for a constructor declared with labels; `C {}` for any constructor [4] | n/a (no literal); `f C { x = 1 }` is `f (C { x = 1 })`, since labelled construction is an `aexp` [4] | `r { x = 1 }` on any constructor having the labels [4] | `C { x = p }`; puns and `..` by extension [5, 6] |
| **OCaml** | yes, type from the labels and context [7, 8] | inline records: `Point { x = 0.; … }` for a constructor declared `of { … }` [9] | `Some { x = 1 }` is `Some` applied to a record [inferred from 7, 9] | `{ e with x = … }` [7] | `C { x; _ }`, `x` alone puns, `; _` for the rest [10] |
| **Rust** | no | struct-like variants `Shape::Circle { radius: 1.0 }`, declared with braces [11, 12] | n/a: tuple variants take brackets, `Some(Point { … })` | `S { x: 1, ..base }` [12] | `S { x, .. }`, shorthand, `..` [13] |
| **Scala 3** | named tuples `(name = "Bob")` [14] | named arguments `Circle(radius = 1)`, mixed with positional [15] | n/a; braces are a block | `c.copy(x = 1)` [16] | positional; named patterns `City(name = n)` arrived with named tuples [14] |
| **Kotlin** | no | named arguments `User(name = "Jack")` [17, 18] | n/a; braces are a trailing lambda | `copy(age = 2)` [17] | none (type tests and properties) [19] |
| **Swift** | no | labelled associated values, `case node(value: T, left: …)` [20] | n/a | none [unverified] | `case let .node(value, …)` [21] |
| **F#** | anonymous `{\| X = 1 \|}`, distinct delimiter [22] | union cases with named fields, `Rectangle(length = 1.3, width = 10.0)`, mixed with positional [23] | n/a; nominal `{ X = 1 }` takes its type from the labels [24] | `{ r with Y = 1 }`, `{\| r with … \|}` [22, 24] | `Rectangle(width = w)` [23] |
| **Elm** | yes, structural [25] | no; constructors are positional [26] | constructor applied to a record, `ReceivedMessage { user : User, … }` as a payload type [26] | `{ r \| x = 1 }` [25] | `{ x, y }` [unverified] |
| **PureScript** | yes, structural, `{ x: 1 }` [27] | no; positional | constructor applied to a record [inferred from 27] | `r { x = 1 }`, `_ { x = 1 }`: `=` marks an update, `:` a literal [27] | record puns `{ x, y }` [28] |
| **Roc** | yes, structural [29] | no; tags take payloads `Ok(first)` [29] | `Ok({ … })` [inferred from 29] | `{ ..r, name: "x" }` [29] | destructuring `{ name, … } = r` [29] |
| **Gleam** | no | labelled fields, `Teacher(name: …)`, labels optional, any order [30, 31] | n/a | `Teacher(..teacher1, subject: "PE", room: 6)` [32] | labels and shorthand `name:` [33] |
| **Koka** | no | the constructor is a function with named arguments, `Person(name = "Brian", age = 19)`: "just functions all the way down" [34] | n/a | `p(age = p.age + 1)`, a generated copy function [34] | [unverified] |
| **Idris 2** | no | positional `MkPerson "Fred" …` [35] | n/a | `{ x := 3 } r` [36] | positional; implicits by name `{n = 2}` [35] |
| **Agda** | `record { fst = 2; snd = 3 }`, type from the signature [37] | `record { … }`, or the declared constructor positionally [37] | n/a | `record old { a = 0 }` [37] | `record { fst = x; … }` as a pattern [37]; implicits by name `{y = e}` [38] |
| **Unison** | no | positional; "no special syntax for creating, pattern matching, or decomposing records" [39] | n/a | generated `Song.title.set` [39] | positional [39] |

What the table says:

- **Nobody gives `C { … }` two meanings decided by names or types.** Haskell, Rust and OCaml
  all have braces for named construction, and in all three **the declaration decides**: a
  constructor declared with named fields (Haskell's labels, Rust's `{ … }` variants, OCaml's
  `of { … }`) is built with braces; any other is applied positionally. OCaml is the closest to
  Stitchwort, since it also has type-directed record literals: there `Some { x = 1 }` is `Some`
  applied to a record, and `Point { x = 0.; … }` builds an inline record, and nothing about the
  field names is consulted to tell the two apart **[inferred from 7, 9]**.
- **Languages with record literals and no named construction** (Elm, PureScript, Roc, Lean)
  read `C { … }` as an argument. Lean builds constructors by name with `(x := e)`, which
  Stitchwort has too.
- **Named construction by named arguments is mainstream.** Scala, Kotlin, F#, Gleam, Koka and
  Lean spell it `C(x = e)` / `C (x := e)`. Gleam even has a pun for it, `name:` for `name:
  name` [33].
- **Printing.** Haskell's derived `Show` prints a labelled constructor with its labels [40];
  Rust's `Debug` prints `Point { x: 0, y: 0 }` [41]; Kotlin's `toString` prints
  `User(name=John, age=42)` [17]; Scala's prints positionally, `Person(Christina,niece)` [16].
  Stitchwort prints constructors positionally.
- **Brace ambiguity elsewhere** is settled syntactically, never by types: Rust forbids a struct
  literal at the head of `if`/`match` unless bracketed [12]; PureScript tells an update `r { x
  = 1 }` from a literal argument by `=` versus `:` [27]; F# gave anonymous records their own
  delimiter `{| |}` [22].

## 5. The alternatives

Each is shown on the same real call sites:

```
-- aoc/src/Aoc/Year2024/Day06/Day06.sw:71
| Up => if row == 0 then None else Some ({ row = row - 1, column })
-- aoc/src/Aoc/Year2020/Day08/Day08.sw:110
| Jmp => Some ({ instruction | operation = Nop })
-- aoc/src/Aoc/Year2020/Day14/Day14.sw:92
SetMask ({ bits })
-- aoc/src/Aoc/Year2021/Day16/Proofs/Complete.sw:160
readPackets Filling ({ unread = encodeAll packets }) = Some (packets, { unread = [] })
-- aoc/src/Aoc/Year2025/Day07/Spec/Spec.sw:54
(timelinesFrom (r + 1) b rest).map (Cons ({ row = r, column = c, turn = Left }))
-- aoc/src/Aoc/Year2020/Day13/Proofs/Part1.sw:26
Witness ({ id = other, offset = start }) (Both (Inl rfl) (Eq.cong idOf same))
-- docs/guide/examples/data.sw:80 and 84
type Event = | Meeting (title: Text) (minutes: Nat := 30) (room: Text) | Reminder (title: Text)
def standup: Event := Meeting { title = "Standup", room = "Blue" }
| Meeting { minutes, .. } => minutes
```

### A. Keep the rule; make the round trip cheaper

Braces after a constructor keep naming its fields (D1370 (a)). Two cheap additions:

- **A′: accept an update.** `Some { instruction | operation = Nop }` can never be a named
  construction (an update isn't one), so it can be read as `Some ({ … })` with no ambiguity.
  The same holds for a constructor with no explicit fields in argument position,
  `readPackets Filling { … }`, *as long as it has none*: if `Filling` later gains a field, the
  text becomes a construction, so that half is option B in miniature and I'd leave it out.
- **A″: a fix the CLI can apply** (`stitchwort check --fix`, and the editor's quick fix),
  inserting the brackets the note already names.

Before and after: only `Some { instruction | operation = Nop }` changes (about 26 sites).

Assessment: no new rule and no risk. But the ~113 plain literals keep their brackets, and an
agent still pays the check cycle unless it runs `--fix`, which none of the notes suggest they
would. The guide's "common mistake" section stays.

### B. Fall back by names (D1370 (b))

Braces name the constructor's fields; when a name isn't one of them and the constructor has one
explicit field, the braces are that field's record instead.

Before and after: `Some { row = row - 1, column }`, `SetMask { bits }` work; `Cons { … }`
(two fields) and `Witness { … } proof` don't; `Some { value = 3 }` with an `Item` having
`value` still picks `Some`'s own field.

Assessment: fixes the commonest case, but by exactly the mechanism §1.2 rules out. Which
reading applies depends on the names, so adding a field with the right name (and a default on
the other, or `..` in a pattern) changes working code silently. Patterns either differ from
expressions or reopen D593 (b). Not recommended, as in D1370.

### C. Lean's arrangement: braces are always a record

Braces after a constructor, as after a function, are always an argument. Building or matching
a constructor by field names uses named arguments: `Meeting (title := "Standup") (room :=
"Blue")`, and in patterns a new form `| Meeting (minutes := m) ..` (Lean's `..` fills the
other explicit arguments with `_` [2]).

```
Some { row = row - 1, column }                                   -- was Some ({ … })
Some { instruction | operation = Nop }
SetMask { bits }
readPackets Filling { unread = encodeAll packets }
(timelinesFrom (r + 1) b rest).map (Cons { row = r, column = c, turn = Left })
Witness { id = other, offset = start } (Both (Inl rfl) (Eq.cong idOf same))

def standup: Event := Meeting (title := "Standup") (room := "Blue")   -- was Meeting { … }
| Meeting (minutes := minutes) .. => minutes                          -- was Meeting { minutes, .. }
```

Assessment:

- **One rule for every callee**, and the simplest to state: `{` in an expression or pattern
  is always a record (or an ability row in a type). Nothing depends on the declaration, names
  or types. No silent change: a constructor gaining a field makes `C { … }` an arity or type
  error.
- **Costs.** Named construction loses its record look and its punning: `Dot { id, ref = 2 }`
  becomes `Dot (id := id) (ref := 2)`, and `| Circle { radius, .. }` becomes `| Circle
  (radius := radius) ..`, which D593 (b) rejected for being long (variant-fields.md §4.2). It
  needs named-argument patterns (unbuilt), and named arguments must fill constructor defaults
  (unbuilt, §2). The JS shape (`{ tag: "Circle", radius }`) no longer matches the pattern's
  look. Readers coming from Rust, Haskell or TypeScript expect `Circle { radius }` for this.

### D. The declaration decides (recommended)

A constructor can be declared in one of two styles, and its style fixes what braces after it
mean, in expressions and patterns alike:

- **Record-style**, explicit fields in braces: `| Meeting { title: Text, minutes: Nat := 30,
  room: Text }`. Braces after it name its fields, exactly as today (D593 (b), D605 (a), with
  all their rules: any order, punning, defaults, `..`, every field once). It can still be
  applied positionally and with `(f := e)`.
- **Bracket-style**, as every constructor is declared today: `| Some (value: a)`, `| Cons
  (head: a) (tail: List a)`, `| Filling`. Braces after it are an ordinary argument, as after a
  function: a record literal, an update, or a record pattern.

Implicit fields stay in square brackets in both styles (`| VCons [n: Nat] { x: a, xs: Vec a n
}: Vec a (Succ n)`). `| C { x: T }` is a parse error today, so the syntax is free **[ran]**.

```
type Event =
  | Meeting { title: Text, minutes: Nat := 30, room: Text }   -- the one change for this type
  | Reminder (title: Text)

def standup: Event := Meeting { title = "Standup", room = "Blue" }   -- unchanged
| Meeting { minutes, .. } => minutes                                  -- unchanged

Some { row = row - 1, column }                    -- Some is bracket-style: a record argument
Some { instruction | operation = Nop }
SetMask { bits }
readPackets Filling { unread = encodeAll packets }
(timelinesFrom (r + 1) b rest).map (Cons { row = r, column = c, turn = Left })
Witness { id = other, offset = start } (Both (Inl rfl) (Eq.cong idOf same))
| Some { name, .. } => name                       -- a record pattern on Some's argument
```

Checked against §1.2:

1. **Shared names** (`Some { value = 3 }`): `Some` is bracket-style, so it's always a record
   argument; there is nothing to pick. Written for an `Option Nat`, it is an error with a note:
   "`Some` is declared with its fields in brackets, so braces after it are its argument; to
   give `value` by name write `Some (value := 3)`, or just `Some 3`".
2. **Types.** The reading is fixed when the constructor's name is resolved, before any type
   is looked at. `Some { name = "tea" }` then waits for its type exactly as `Some ({ … })`
   does today (postponement), so type inference is unchanged.
3. **Silent change.** Adding a field to a bracket-style constructor turns `W { name, .. }`
   into `E-ARITY` (one argument for two fields) and `W { … }` in an expression into a partial
   application, a type error. Adding a field to a record-style constructor is today's D593 (b)
   case, already safe. The only edit that changes meaning is **switching a constructor's
   style**, and then only when the held record's field names are also the constructor's
   (otherwise it's an error). That is a deliberate edit to the declaration, and the existing
   `W-RECORD-ARGUMENT` warning (braces after a record-style one-field constructor whose field
   is a record having those names) still flags the risky shape.
4. **Patterns** follow the same rule, so a pattern and an expression never read `C { … }`
   differently (D605 (a)'s aim kept).

Costs:

- **Two ways to declare a constructor**, and the reader of `C { … }` needs to know which one
  `C` uses (hover shows it; the error explains it). Haskell, Rust and OCaml all ask the same of
  their readers.
- **Named construction becomes opt-in.** `Some { value = x }`, `VCons { x = 1, xs = VNil }` and
  `MkPos { n = 3, ok = omega }` (all in feature tests) need their types redeclared, or become
  `(f := e)` or positional. By §3, no application code is affected.
- **Defaults on a bracket-style constructor's fields** are reachable only by name, and today
  only braces fill them (§2). So named arguments on constructors should fill defaults as they
  do for `def`s (Q5), or defaults are allowed only on record-style constructors.
- **Implementation**: the declaration parser, a style flag on the constructor, the
  elaborator's choice in `records::ctor_fields` (it already falls back to a record argument
  for non-constructors, `not_a_ctor`). The parser can't know a constructor's style, so its two
  errors for `C { … } x` and `f C { … }` move to the elaborator, which gives them only for a
  record-style `C` (Q3). Then `show`, `fmt`, hover. Medium.
- **Unchanged**: terms and hashes (both styles elaborate to the positional application), the
  JS shape of a variant, shared fields and shared-field update, record literals and patterns.

### E. A different spelling for named construction

Keep braces as a record argument everywhere (as C), but give named construction a spelling of
its own that keeps the record look:

- `Meeting.{ title = "Standup", room = "Blue" }`, `| Meeting.{ minutes, .. }`. Zig uses `.{ }`
  for literals, which suggests the opposite meaning; nothing else uses it this way
  **[unverified]**.
- `Meeting { title := "Standup" }` versus `Some { name = "tea" }`: `:=` names constructor
  fields, `=` record fields. PureScript tells update from literal by `=` and `:` [27], but
  here a punned field (`{ id, .. }`) has neither, so the two readings collide again.
- `Meeting with { … }`, `new Meeting { … }`: a keyword, heavier than any of the others.

Assessment: every spelling either is new to every reader or brings the collision back for
puns. D gets the same separation without a new token, by putting the choice in the
declaration where it is made once.

### F. Unify constructors and records

Let every constructor's explicit fields be an inline record (OCaml's inline records, or
variant-fields.md §8's "record with a `kind` variant"), so `C { … }` is always `C` applied to
"its record". For `Some`, "its record" is `{ value: a }`, so `Some { name = "tea" }` is still
wrong; making a one-field constructor's record *be* its field is draft 1's rule, with its
silent change. OCaml also has to forbid an inline record from escaping as a value [9]. Not
pursued.

### Other ideas, briefly

- **Name the record type in its literal**, `Item { name = "tea" }` (Rust, Haskell), would
  replace the 17 annotated `({ … }: Item)` forms, but `Some Item { … }` still needs brackets.
  It could be added to any option later.
- **Whitespace**, `Circle{ … }` versus `Circle { … }`: rejected before (variant-fields.md
  §4.2), and still too easy to misread.
- **A different delimiter for literals** (F#'s `{| |}`): moves the cost onto the 2500 literals.

## 6. Side by side

| | A (keep, + update, + fix) | B (by names) | C (Lean) | D (declaration) | E (new spelling) |
|---|---|---|---|---|---|
| Bracketed records that go away (of ~160) | ~26 | ~85 | ~140 | ~140 | ~140 |
| Named construction as today | yes | yes | no: `(f := e)` | yes, for record-style | new token |
| Punned field patterns `C { id, .. }` | yes | yes | no | yes | yes |
| Meaning decided by | constructor or not | names, types | nothing | declaration | token |
| Silent change on adding a field | no | **yes** | no | no | no |
| Patterns and expressions agree | yes | needs D1371 | needs new patterns | yes | yes |
| `f Filling { … }` | error | error | works | works (Q3) | works |
| New syntax | none | none | named-argument patterns | record-style declarations | `.{` or `:=` |
| Prior art | none quite | none | Lean | Haskell, Rust, OCaml | none |
| Cost | small | small | medium | medium | medium |

## 7. Recommendation

**D: the constructor's declaration decides.** It removes about 140 of the 160 bracketed
records, including every form the AoC agents tripped on, and keeps named construction and
named-field patterns as they are for the types that want them. It keeps the property D593 (b)
was chosen for: no change to a type silently changes what working code means. It decides by
declaration, as the three languages with brace construction do, and never by field names or
types, which is D1370's objection to B.

Against C: C is simpler to state, but it gives up the record look and punning for named
patterns, which were the reasons D593 (b) chose braces, and it needs a new pattern form and
default-filling named arguments before it is even equal to today. If Matt prefers the
smallest rule over keeping those, C is the sound alternative.

Whatever is chosen, A′ (accept `Some { r | … }`) is safe on its own and could land first if D
waits.

What D should do, concretely:

- **Messages.** `Circle { id = "a", radius = 1 }` for a bracket-style `Circle`: an error at the
  braces, "braces after `Circle` are its first argument, a `Text`, not its fields", with notes
  "to build it by field names, declare it `| Circle { id: Text, radius: Nat }`" and "or write
  `Circle (id := "a") (radius := 1)`". `Some { name, .. }` against an `Option Int`: the record
  pattern's error, "an `Int` isn't a record", noting `Some`'s style.
- **The guide.** "A common mistake: braces after a constructor" goes; "Constructors with named
  fields" shows the record-style declaration, and the tour page `web/guide/04-variant-fields.sw`
  declares `Shape` with braces.
- **`show`** (Q4): a record-style constructor prints by name, `Meeting { title = "Standup",
  minutes = 30, room = "Blue" }`, as Haskell and Rust do; a record inside a bracket-style
  constructor prints without brackets, `Some { name = "tea", price = 3 }`. Both read back.

## 8. Staged plan

Each stage is a lane, in order; stage 0 is independent.

0. **(If D waits.) A′**: `C { e | … }` after any constructor is `C ({ e | … })`; and the bracket
   note for `E-UNKNOWN-FIELD` on a constructor with several fields, which is missing today
   (`Cons { row = 0, column = c }` gets only "`Cons`'s fields are `head`, `tail`" **[ran]**).
   Small, Sonnet or DeepSeek.
1. **Record-style constructors.** Parser and AST (`| C { f: T, … }`, implicits before it),
   a style flag on the constructor, the elaborator's choice in `records::ctor_fields` and
   `ctor_fields_pattern`, the argument-position rule (Q3), messages, `fmt`, hover. The
   feature's examples, the guide's `Event` and the tour's `Shape` are redeclared. Spec and
   tricky parts on Opus, the rest Sonnet.
2. **Named arguments fill constructor defaults** (Q5), matching `def`s. Small to medium.
3. **`show`** by field names for record-style constructors, and no brackets around a record
   argument (Q4). Moves the hashes of `Std.Show` and every derived `Show`, which doesn't count.
4. **Sweep** (Q6): drop the brackets from the ~140 `C ({ … })` sites by script; docs
   (`docs/syntax.md` bullets on named construction, named-field patterns, record patterns;
   `docs/guide/03-data.md`; the tour pages), and the reject examples rewritten. Mechanical,
   DeepSeek.

## 9. Evidence still to collect

- **How often a bracket-style constructor would be written with named braces by mistake**
  under D (the new error). §3 suggests rarely, since nobody builds constructors by name in
  application code; the first few AoC days after stage 1 would show it. A note in each day's
  friction list is enough.
- **Whether named construction grows** once it's taught: if new AoC days start declaring
  record-style constructors, D is confirmed; if they keep using records inside bracket-style
  wrappers, C's cost (losing brace patterns) would have been small.
- **A prototype of the elaborator choice** (stage 1's first step) to confirm that the
  argument-position case `f C { … }` can be decided after name resolution without the parser
  knowing the style (the parser would keep an "adjacent braces" node and the elaborator would
  pick; [inferred]).
- Not verified for this note: Swift's update story, Elm's record patterns, Koka's patterns,
  F#'s stated reason for `{| |}` (FS-1030 gives none I could find [22]).

## 10. Decisions

- **Q1. What decides the meaning of braces after a constructor?** [rec: D]
  (D) the constructor's declaration: record-style `| C { f: T, … }` takes its fields in
  braces, bracket-style `| C (f: T)` takes braces as an ordinary argument;
  (C) nothing: braces are always a record, named construction is `C (f := e)`;
  (A) keep today's rule, with A′ (updates) and a `--fix`.
  D removes the friction and keeps named construction and punned patterns as they are; C is
  simpler but loses those; A keeps the 160 brackets.
- **Q2. Do patterns follow the same rule?** [rec: yes] `| Some { name, .. }` is a record
  pattern on `Some`'s argument; `| Meeting { minutes, .. }` names `Meeting`'s fields. So a
  pattern and an expression never read `C { … }` differently (D605 (a)'s aim), and adding a
  field never changes a pattern silently (D593 (b)'s).
- **Q3. Braces after a constructor in argument position** (`f C { … }`). [rec: bracket-style
  takes them as `f`'s next argument (`readPackets Filling { unread = … }`); a record-style one
  stays an error asking for brackets (`Some (Dot { … })`)] Haskell's reading, `f (C { … })`,
  would also be consistent, but it is the one place where a reader would have to know the
  declaration to see which function gets the braces, so I'd keep the error until there is a
  reason not to.
- **Q4. `show`.** [rec: record-style constructors print by field name; a record inside a
  bracket-style constructor prints without brackets] Output stays valid source, and the named
  form is what the value was written as.
- **Q5. Should named arguments on a constructor fill its fields' defaults, as they do for a
  `def`?** [rec: yes] Otherwise a bracket-style constructor's defaults can't be used at all
  under D; and it removes the one place where constructors and functions differ today
  (`Circle (radius := 1)` is a function waiting for `id`).
- **Q6. Sweep the repository's `C ({ … })` to `C { … }` once D is built?** [rec: yes] The
  bracketed form stays valid, but one spelling in the code base is what agents copy.

## 11. Sources

Cited, read on 6 November 2026, 41:

1. Lean reference, Inductive Types (structure instances, `with`, anonymous constructor).
   <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>
2. Lean reference, Function Application (named arguments, mixing, `..`, patterns).
   <https://lean-lang.org/doc/reference/latest/Terms/Function-Application/>
3. Functional Programming in Lean, Structures (expected type; instances as arguments; `#eval`
   output). <https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Structures/>
4. Haskell 2010 Report, ch. 3 (§3.15 labelled construction and update, `C {}`, `aexp`).
   <https://www.haskell.org/onlinereport/haskell2010/haskellch3.html>
5. GHC User's Guide, NamedFieldPuns.
   <https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/record_puns.html>
6. GHC User's Guide, RecordWildCards.
   <https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/record_wildcards.html>
7. OCaml manual, Expressions. <https://ocaml.org/manual/latest/expr.html>
8. OCaml manual, tutorial (type-directed disambiguation of labels and constructors).
   <https://ocaml.org/manual/latest/coreexamples.html>
9. OCaml manual, Inline records. <https://ocaml.org/manual/latest/inlinerecords.html>
10. OCaml manual, Patterns. <https://ocaml.org/manual/latest/patterns.html>
11. The Rust Book, ch. 6.1 (enum variants with named fields).
    <https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html>
12. Rust Reference, Struct expressions (shorthand, `..base`, brace-restricted positions).
    <https://doc.rust-lang.org/reference/expressions/struct-expr.html>
13. Rust Reference, Patterns (struct patterns, shorthand, `..`).
    <https://doc.rust-lang.org/reference/patterns.html>
14. Scala 3 reference, Named tuples.
    <https://docs.scala-lang.org/scala3/reference/other-new-features/named-tuples.html>
15. Scala tour, Named arguments. <https://docs.scala-lang.org/tour/named-arguments.html>
16. Scala 3 book, Domain modelling tools (`copy`, `toString`).
    <https://docs.scala-lang.org/scala3/book/domain-modeling-tools.html>
17. Kotlin, Data classes. <https://kotlinlang.org/docs/data-classes.html>
18. Kotlin, Functions (named arguments). <https://kotlinlang.org/docs/functions.html>
19. Kotlin, Sealed classes. <https://kotlinlang.org/docs/sealed-classes.html>
20. The Swift Programming Language, Declarations.
    <https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/ReferenceManual/Declarations.md>
21. The Swift Programming Language, Enumerations.
    <https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/Enumerations.md>
22. F# language reference, Anonymous records; and FS-1030 (no stated reason for `{| |}`).
    <https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/anonymous-records>,
    <https://github.com/fsharp/fslang-design/blob/main/FSharp-4.6/FS-1030-anonymous-records.md>
23. F# language reference, Discriminated unions.
    <https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/discriminated-unions>
24. F# language reference, Records.
    <https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/records>
25. Elm guide, Core language. <https://guide.elm-lang.org/core_language.html>
26. Elm guide, Custom types. <https://guide.elm-lang.org/types/custom_types.html>
27. PureScript documentation, Records.
    <https://github.com/purescript/documentation/blob/master/language/Records.md>
28. PureScript by Example, ch. 4 (record puns). <https://book.purescript.org/chapter4.html>
29. Roc tutorial. <https://www.roc-lang.org/tutorial>
30. Gleam tour, Records. <https://tour.gleam.run/data-types/records/>
31. Gleam tour, Labelled arguments. <https://tour.gleam.run/functions/labelled-arguments/>
32. Gleam language tour source, record updates lesson.
    <https://github.com/gleam-lang/language-tour/blob/main/src/content/chapter3_data_types/lesson05_record_updates/code.gleam>
33. Gleam tour, Label shorthand syntax.
    <https://tour.gleam.run/functions/label-shorthand-syntax/>
34. The Koka book, §3.3 (structs, named-argument constructors, copy).
    <https://koka-lang.github.io/koka/doc/book.html>
35. Idris 2, Types and functions tutorial (records, implicits by name).
    <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>
36. Idris 2 reference, Records. <https://idris2.readthedocs.io/en/latest/reference/records.html>
37. Agda, Record types. <https://agda.readthedocs.io/en/latest/language/record-types.html>
38. Agda, Implicit arguments.
    <https://agda.readthedocs.io/en/latest/language/implicit-arguments.html>
39. Unison language reference, Record types.
    <https://www.unison-lang.org/docs/language-reference/record-type/>
40. Haskell 2010 Report, ch. 11 (derived `Show` and `Read` for labelled constructors).
    <https://www.haskell.org/onlinereport/haskell2010/haskellch11.html>
41. Rust standard library, `Debug`. <https://doc.rust-lang.org/std/fmt/trait.Debug.html>

Not cited, though read: the GHC DuplicateRecordFields and OverloadedRecordUpdate pages, OCaml's
warning list (40–42, ambiguous labels), Haskell mailing-list threads on record precedence.
