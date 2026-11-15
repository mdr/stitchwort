# Proposal: constructors found by the type they build or match

**Status:** draft 1, 15 November 2026 (SW-510). Decision for Matt: D3615
(at the end). Related: [namespaces.md](namespaces.md) §4.4 and §4.9, which
left this open ("can be added later", §8); SW-2716 (a constructor named like
its type, in type positions); [toy-formatter.md](toy-formatter.md) §6 item
3; `tools/toyfmt/NOTES.md` stage B friction 3 and 4; `games/rogue/NOTES.md`
§8.

## The problem

Two types in one program that each have a constructor called `Str` make
every bare `Str` an error, even where the type is plain to see:

```
type Token = | Str (text: Text) | Name (text: Text)
type Doc   = | Str (text: Text) | Line | Cat (a: Doc) (b: Doc)

def width (d: Doc): Nat := match d with
  | Str t => t.length        -- E-AMBIGUOUS: `Str` could mean `Doc.Str` or `Token.Str`
  ...
```

Probed today (release binary, 15 Nov 2026), every one of these is
`E-AMBIGUOUS`, though in each the type is known:

| Where | Written | Type known from |
|---|---|---|
| a `match` arm | `\| Str t =>` on `d: Doc` | the scrutinee |
| a definition's value | `def d: Doc := Str "x"` | the signature |
| an argument | `f (Str "x")`, `f: Doc → Nat` | the parameter |
| a list | `[Str "x", Line]: List Doc` | the element type |
| a record update | `{ x \| doc = Str "a" }` | the field |
| a comparison | `d == Str "a"` | the other side |

Only a name that is unique in scope works (`d == Line`). So programs pick
names to keep apart: the toy formatter's `Doc.Flatten` beside `Mode.Flat`,
its tree's `Var`, `NumberLiteral`, `StringLiteral` so the tokens can be
`Name`, `Number`, `Str`; the roguelike's `GaveUp` because `Command` has
`Quit`; std writes `Err (Args.Error.Unknown …)` because `Terminal.Key` has
an `Unknown` too. The same happens with the prelude: an AoC grid's
`type Cell = | Wall | None` hides `Option`'s `None`, and `| None => 0` in a
match on an `Option Nat` is then a type mismatch. The self-hosted formatter
holds a lexer, a 94-kind syntax tree and a layout document in one program,
so it would meet this on almost every page.

## Options

**(a) The expected type first.** Where the type a constructor builds or
matches is known and is a data type `T`, a bare `C` means `T.C` if `T` has a
constructor `C`, whatever else `C` means in scope and whether or not `T`'s
constructors are imported. Otherwise the scope decides, as today.

**(a′) The scope first, the type as a tie-break.** As (a), but only among
the constructors the scope already offers: `None` hidden by a file's own
`Cell.None` stays hidden, and a library type's constructors still need an
import.

**(b) Constructors only inside their type**, `Token.Str`, with a leading-dot
short form `.Str` resolved by the expected type (Swift's implicit members,
Lean's `.ctor`). Bare `Str` would no longer exist, prelude ones included
(`.Some x`, `.Cons`), unless they were made exceptions.

**(c) Both:** (a), plus `.Str` as an explicit form.

**(d) The status quo**, with a better message ("the scrutinee is a `Doc`:
write `Doc.Str`").

### What users write

| | lexer and printer | roguelike | std `Args` |
|---|---|---|---|
| today, (d) | `\| Doc.Str t => …`, `Token.Str`, or names chosen apart | `GaveUp` | `Err (Args.Error.Unknown n None)` |
| (a), (a′) | `\| Str t => Str "\"${t}\""` (a `Token.Str` in, a `Doc.Str` out) | `\| Quit => { state \| phase = Quit }` | `Err (Unknown n None)` |
| (b) | `\| .Str t => .Str "…"`, and `.Some`, `.Cons` everywhere | `\| .Quit => { … phase = .Quit }` | `Err (.Unknown n None)` |

Only (a) also makes `| None => 0` work beside a file's own `None`, and
`| Escape =>` on a `Terminal.Key` without importing its constructors.

### Where the type isn't known

`let k := Unknown`, or `Str "a" = mk "a"` read left to right, has no
expected type when the name is met. Under (a):

- A name that is unique in scope is used at once, exactly as today, so
  elaboration order doesn't change for any program that checks today.
- An ambiguous one **waits**, kept as syntax with its arguments, on the
  postponement queue ([postponement.md](postponement.md)), the way a method
  section waits for its receiver's type (`docs/syntax.md`, "Method
  sections"). It resumes when its expected type becomes a data type. An
  operator chain already retries a side it couldn't infer against the type
  the other side fixes (`numbers.rs`, `State::Failed`: "checked against `T`
  at the end"), so `d == Str "a"` and `Str "a" = mk "a"` resolve once the
  name is checked against a known type instead of failing.
- Still unknown at the end of the declaration, it is `E-AMBIGUOUS` as now,
  with a note saying why: "nothing here says whether this is a `Doc` or a
  `Token`: write `Doc.Str`, or give `k` a type".

A pattern whose scrutinee's type isn't known (rare: parameters and
annotated scrutinees give it) falls back to the scope; an ambiguous one is
`E-AMBIGUOUS` with the same note.

### Error messages under (a)

- Known type without that constructor: `E-UNKNOWN-NAME`, "`Doc` has no
  constructor `Name`", with "did you mean" over `Doc`'s constructors, and a
  note when `Name` is another type's constructor ("`Name` is `Token.Name`,
  a `Token`; this is a `Doc`"). Today the same mistake is a type mismatch
  between two types, or `E-AMBIGUOUS`.
- Hover and go-to-definition show the constructor chosen (`note_found`).

### Other interactions

- **Terms, proofs, goals.** The kernel sees data and constructor ids, so
  hashes, proofs and caches don't change. Goals print short names
  (`⊢ mk t = Cat (Str t) Line`), which today don't paste back when the name
  clashes; under (a) they do wherever the type is known, nearly everywhere
  in a statement. The missing-arms fix and case split (`ctor_written`,
  `missing.rs`) qualify clashing names today (`Doc.Str ‹text›`) and can
  write short ones.
- **Derived instances** (`==`, `Ord`, `Show`, `Finite`): `Doc`'s derived
  `==` already works with a clashing `Str` (probed: `d == Line`). Generated
  code names constructors by id or exact key (`EXACT_KEY` in `scope.rs`), so
  (a) changes nothing there.
- **Imports.** `import Lexer (..)` and `import Printer (..)` both bringing a
  `Str` are fine until a bare `Str` meets an unknown type. Under (a) a
  program needs fewer imports, not more: a value's type finds its
  constructors as it finds its functions for dot notation, which "need no
  import" already (`docs/syntax.md`, "Namespaces and imports").
- **The formatter** doesn't resolve names, so (a) costs it nothing; (b)
  and (c) need `.Name` in both lexers, the parser and the formatter's
  rules, and `.Name` sits next to method sections (`.name`, a function on a
  receiver), which differ from it only by case.
- **Not covered:** a constructor named like a type in a *type* position
  (`| Text (text: Text)`, NOTES friction 3; SW-2716). That's a separate,
  smaller rule (prefer the type where a type is expected) and should be
  done beside stage 1.

### Can (a) change what a working program means?

Only if a program checks today with `C` meaning `X.C` where a data type
`T ≠ X` with its own `C` is expected. That needs an implicit conversion
from `X` to `T`. The ones the elaborator has (a constructor against a test
fact, `Value::Eq`; a pure constructor where a computation's function is
expected, `Value::Pi`) are against types that aren't data heads, so (a)
doesn't apply to them; `Effect.Comp`'s constructors are proof-only and are
left out of the rule. Stage 1 checks the claim on the examples' hash
snapshots (the verifier): no hash may move.

### (a) against (a′)

(a′) is smaller but keeps two complaints: a file's own `None` still breaks
`| None` on an `Option`, and library constructors still need an import.
(a)'s one surprise, `None` meaning `Option.None` in a match on an `Option`
in a file with its own `Cell.None`, is what the scrutinee's type says, and
any other meaning there is a type error. Swift's and Lean's leading dot
behave like (a): they look only in the expected type.

### Against (b) and (c)

(b) turns every constructor in every program into `.C` or `T.C`, the
prelude's included, or else needs a second rule for exceptions; it reverses
namespaces.md decision 6 (constructors follow their type's visible
binding), and it only works where the type is known, which is where (a)
already works without the dot. (c) adds a second spelling whose only gain, a marker
that the type chose, hover already gives. (d) keeps the renames.

## Other languages (checked 15 Nov 2026)

- **Swift**: an implicit member expression `.member` is "an abbreviated way
  to access a member of a type, such as an enumeration case or a type
  method, in a context where type inference can determine the implied
  type"; enum case patterns take an optional type, `type-identifier? .
  enum-case-name`, so `case .left:` [SW1, SW2].
- **Lean 4**: identifiers with a leading `.` "are to be looked up in the
  expected type's namespace"; the current and open namespaces are not used.
  Separately, "if an identifier resolves to multiple names, then the
  elaborator attempts to use all of them"; exactly one success wins, and
  "when otherwise-ambiguous names have different types, the types are used
  to disambiguate" [L3]. (a) is the cheap half of this: it filters by the
  expected type's head rather than elaborating every candidate.
- **OCaml**: the manual's tour shows a constructor shared by two variant
  types resolved from an annotation, `let permute (x:first_variant) = match
  x with | A -> (B:first_variant) | …`: the pattern from `x`'s type, the
  result needing its own annotation, as its type wasn't known yet when met;
  "adding explicit type annotations to guide disambiguation is more robust"
  [O1]. Waiting, as in (a), avoids that annotation.
- **Agda**: constructors "can be overloaded and get disambiguated based on
  the type they are introducing" [A1]; 2.8.0 added a postponed
  `DisambiguateConstructor` problem (#7814), i.e. it waits while the type
  is unknown, as (a) does [research card C18, docs/research/inductives.md].
- **Rust**: variants "can be referenced by a path from the enumeration
  name, including in use declarations" (`Animal::Dog`, `use Examples::*`)
  [R1]; the Reference describes no resolution from the expected type. Two
  glob imports of one name are E0659 ("an item usage is ambiguous") where
  it is used [R2]. (So `games/rogue/NOTES.md` §8's "Rust … would resolve
  both from the expected type" isn't borne out.)
- **Haskell 2010**: an import clash is an error "only if y is actually
  mentioned"; `T(..)` brings a type's constructors [H1].
- Elm and Gleam: their official pages fetched didn't say how constructors
  of two types with one name are handled, so they're left out.

## Stages

1. **Patterns by the scrutinee's type.** In `pattern_ctor`
   (`crates/elab/src/lib.rs`), where `ty` is a data type, look the name up
   among its constructors first (record patterns already resolve by `ty`,
   `records.rs`); same for `C { f = p }` patterns and pattern `let`
   (`patlet.rs`). Errors as above. Examples: accept (the lexer/printer pair,
   `Cell.None` beside `Option`), reject (unknown constructor of the known
   type). Sonnet, 1.5 h. Plus SW-2716 alongside (Sonnet, 1 h).
2. **Expressions checked against a data type.** `ctor_head` and
   `ctor_fields_against` (`check.rs`) take the expected type's head; this
   covers values, arguments, lists, record fields and comparisons (through
   the chain's retry). Opus (name resolution in the checker), 2 h.
3. **Waiting when the type isn't known yet.** An ambiguous constructor in
   inference waits on the queue as a section does; at the end, the new
   `E-AMBIGUOUS` note. Opus, 2–3 h.
4. **Printers, editor, docs, uses.** `ctor_written` and case split write
   short names where the type picks them; `docs/syntax.md`, the guide (its
   examples checked) and a feature-tour page (this is one a newcomer
   enjoys); namespaces.md §4.9 updated; the toy's names (`Flat`, token
   `Str` beside `Doc.Str`), the roguelike's `Quit` and std's
   `Args.Error.Unknown` uses shortened as the first users. Sonnet, 1.5 h.

Total about 8–9 h of lanes, estimated. Stages 1 and 2 alone remove the
toy's and the roguelike's frictions; 3 handles `let` and left-hand sides.

## Findings worth tickets

- If D3615 is no, the goal printer should qualify clashing constructors as
  `ctor_written` does, so goals paste back.
- `games/rogue/NOTES.md` §8's Rust claim (above); namespaces.md §4.9's
  `Decidable`'s `Yes` example is stale (`Decidable` is a record, SW-2746).

## D3615

**The problem.** Two types with a constructor of the same name make every
bare use of it an error, even in a `match` on a known type or where a
signature gives the type. Programs rename (`GaveUp`, `Flatten`,
`StringLiteral`) or qualify (`Args.Error.Unknown`), and the self-hosted
formatter, with tokens, a 94-kind tree and a layout document in one
program, would do it constantly.

**The change.** Option (a): where the type being built or matched is known,
a bare constructor name means that type's constructor, ahead of whatever
else the name means in scope and without needing an import. Where the type
isn't known yet, an ambiguous name waits for it; only if nothing ever says
is it an error, which then says what to write. No new syntax; terms and
hashes don't change.

**What it should do.** All six probed cases above check (`| Str t` on a
`Doc`, `Err (Unknown n None)`, `| None` beside a file's own `None`); the
toy and roguelike renames can be undone; the missing-arms fix and pasted
goals use short names. Estimated 8–9 h of lanes in four stages, the first
two (about 3.5 h) covering the formatter's and roguelike's cases.

**D3615: adopt (a), the expected type first, for constructors in patterns
and expressions, in the four stages above? [rec: yes]**

## Sources

- [SW1] The Swift Programming Language, Expressions, "Implicit Member
  Expression".
  https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/ReferenceManual/Expressions.md
- [SW2] Same, Patterns, "Enumeration Case Pattern" and its grammar.
  https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/ReferenceManual/Patterns.md
- [L3] Lean Language Reference, "Identifiers".
  https://lean-lang.org/doc/reference/latest/Terms/Identifiers/
- [O1] OCaml manual, "The core language" (records and variants).
  https://ocaml.org/manual/latest/coreexamples.html
- [A1] Agda 2.5.2 release notes.
  https://hackage.haskell.org/package/Agda-2.7.0.1/docs/doc/release-notes/2.5.2.md
- [R1] The Rust Reference, "Enumerations".
  https://doc.rust-lang.org/reference/items/enumerations.html
- [R2] Rust error index, E0659. https://doc.rust-lang.org/error_codes/E0659.html
- [H1] Haskell 2010 Report, chapter 5 (§5.2, §5.5.2).
  https://www.haskell.org/onlinereport/haskell2010/haskellch5.html

## Decision (D3615, Matt, 15 Nov 2026)

Option (d), not (a): "I think it's probably not wise to support the same name
having different meanings within the same file ... it's really hard to look
and glance know what it is." Built as SW-3397: clearer E-AMBIGUOUS, a warning
where a file's constructor hides an imported one, goals printed qualified;
plus the habit of organising code so a file rarely imports two clashing
types. The `.C` shorthand may be revisited later (SW-3398).
