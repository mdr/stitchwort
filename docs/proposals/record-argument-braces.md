# A record literal as a constructor's argument (D1370)

**Status:** analysis, 26 October 2026, for SW-606. No code changed. The
readings conflict, so the choice is the user's: decisions D1370 and D1371
(§5).

## 1. The friction

A wrapper constructor holding a record has to bracket it:

```
type TextCardData = { id: Text, text: Text }
type Card =
  | TextCard (card: TextCardData)
  | Blank

def c: Card := TextCard ({ id = "a", text = "t" })   -- accepted
def c: Card := TextCard { id = "a", text = "t" }     -- refused
```

## 2. What happens today (run at `27b59c1c`)

Every line below was checked with `stitchwort check`, using the two types
above.

| Written | Result |
|---|---|
| `TextCard { id = "a", text = "t" }` | `E-UNKNOWN-FIELD` "`TextCard` has no field `id`"; note 1 "`TextCard`'s fields are `card`"; note 2 "braces right after a constructor name its own fields; to build the `TextCardData` it holds, write `TextCard ({ … })`" |
| the same inside a `match` arm | the same error |
| `TextCard ({ id = "a", text = "t" })` | accepted |
| `TextCard { card = { id = "a", text = "t" } }` | accepted (named construction) |
| `mk { id = "a", text = "t" }`, `mk` a function | accepted |
| `mk2 { … } 3` (record first, then more arguments) | accepted |
| `Mk { … }`, `Mk` an uppercase **function** | accepted |
| `d.wrap { … }` (dot call) | accepted |
| `d \|> wrap { … }` (pipe) | accepted |
| `MkTwo 1 { … }` (record as a constructor's *later* argument) | accepted |
| `MkTwo2 { … } 1` | `E-PARSE` "braces after `MkTwo2` name its fields, and take no further arguments" |
| `Some TextCard { … }` | `E-PARSE` "braces after `TextCard` as an argument need brackets" |
| `TextCard { d \| id = "b" }` | `E-PARSE` "braces after `TextCard` name its fields; an update isn't one of them" |
| `Some { id = "a", text = "t" }` | `E-UNKNOWN-FIELD` "`Some` has no field `id`", with the same bracket note |
| `theorem t: (s: Text) -> mk { id = s, … } = …` | accepted (the `{` follows `mk`, not the arrow) |
| `theorem t: (s: Text) -> { id = s, … } = …` | `E-PARSE` "expected `}`, but found `=`" (after `->`, `{` starts an ability row) |

So functions, dot calls and pipes already take `f { … }`. Only a
**constructor at the head of an application** is affected, and that is a
deliberate rule, not a parser gap.

### Where it lives

- `crates/syntax/src/parser.rs:3047` `atom`: an uppercase name followed by
  `{` goes to `ctor_fields_expr` (line 3053), whatever the name turns out to
  be. Its doc comment (3043–3046) gives the reason for refusing it as an
  argument: `f C { … }` could mean `f (C { … })` or `f C ({ … })`.
- `parser.rs:3130` `ctor_fields_expr`: refuses it as an argument (the
  `Some TextCard { … }` error) and refuses an update; otherwise builds
  `Expr::CtorFields`.
- `parser.rs:2923` `app`: after `CtorFields`, a further argument is
  `ctor_fields_then_argument` (2958).
- `parser.rs:3179` `record_body`: `{ x = …` or `{ x, …` or `{}` is a
  literal; anything else is an update `{ e | … }`.
- `parser.rs:1801` `row`: `{` in a type position (after `->`) is an ability
  row.
- `crates/elab/src/records.rs:447` `ctor_fields`: if the name is a
  constructor, the braces name its fields; if not (`not_a_ctor`, line 545),
  the braces become a record-literal argument again. That fallback is why
  `Mk { … }` works for an uppercase function.
- `records.rs:384` `unknown_ctor_field`: the second note, given when the
  constructor's one field holds a record that has every name written.

### Why it is this way

This was decided twice. **D593 (b)** made braces after a constructor name its
fields in patterns, and **D605 (a)**, built as D1085, extended it to
expressions so the two agree (`docs/proposals/variant-fields.md` §4.2, §4.5,
§11). §4.2 gives the reason: draft 1's exception (braces are the record
argument for a one-field constructor) let a working pattern silently change
meaning when the constructor gained a field.

## 3. Do the readings conflict?

Yes. For a constructor, `C { f = e, … }` already has a meaning: named
construction. Reading it as "`C` applied to a record literal" would be a
second meaning for the same text:

- **`TextCard { … }`**: named construction of `TextCard`'s fields (`card`),
  or `TextCard` applied to a `TextCardData`. Both parse. Only the field names
  tell them apart.
- **Names shared by both readings.** `Option`'s one field is `value`
  (`crates/elab/src/std/core/Data.sw:83`). If `Item = { value: Nat, … }`,
  then `Some { value = 3 }` could mean either reading. No rule based on names
  can settle it, so one reading has to win, and the other is silently
  unavailable.
- **Generic constructors.** For `Some { name = "tea", price = 3 }`, `Some`'s
  field has type `a`. Whether the names belong to "the record it holds" is
  only known from the expected type. The braces' meaning would then depend
  on type inference, not on syntax.
- **Defaults make a silent change possible.** Fields with defaults may be
  left out of a named construction. Suppose `TextCard { id = "a", text = "t" }`
  meant the record argument, and `TextCard` later becomes
  `TextCard (card: TextCardData := blank) (id: Text) (text: Text)`. The
  same text then means a named construction with `card` defaulted. It still
  checks, and it builds a different value. This is the §4.2 failure in
  expression form.
- **Patterns.** Braces after a constructor in a pattern name its fields
  (D593 (b)), and with `..` a pattern can leave fields out. A fallback in
  expressions only would bring back the pattern/expression asymmetry that
  D605 (a) removed. The same fallback in patterns would bring back the
  failure D593 (b) was chosen to prevent.

The other forms from the brief don't conflict: `f { … }`, `x.f { … }`,
`|> f { … }` and `match` arms already work for non-constructors (§2). A row
`{IO}` only starts after `->` or in a signature's type position, where a
record literal needs brackets today and still would.

## 4. Other languages

- **Lean 4.** Writing a structure instance directly as an argument is
  ordinary: `#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }`
  ([Functional Programming in Lean, Structures](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Structures/)).
  The structure's type comes from the expected type ("the structure's
  expected type must be known in order to use the curly-brace syntax",
  same page). Lean has no conflict because its named construction is spelt
  differently. A constructor's fields are given by name with named
  arguments, `(x := e)`, which "match parameters by name"
  ([Lean reference, Function Application](https://lean-lang.org/doc/reference/latest/Terms/Function-Application/)).
  So `C { … }` in Lean is always `C` applied to a structure instance.
  Structure instance notation "is elaborated to applications of structure
  constructors", and `{ point with x := 1 }` is its update form
  ([Lean reference, Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)).
- **Scala 3.** `f { … }` is valid: in the grammar, `SimpleExpr ::= SimpleExpr
  ArgumentExprs`, with `ArgumentExprs ::= ParArgumentExprs | BlockExpr`
  ([Scala 3 syntax](https://docs.scala-lang.org/scala3/reference/syntax.html)).
  But the braces are a *block*, not a record. Scala has no anonymous record
  literal, so a case class is built as `TextCard(TextCardData(...))` or with
  named arguments, `NamedExprInParens ::= id '=' ExprInParens` (same page).
  The question doesn't come up.
- **Kotlin.** Braces after a call are a *trailing lambda*: "If the lambda is
  the only argument in that call, the parentheses can be omitted entirely:
  `run { println("...") }`"
  ([Kotlin, Lambdas](https://kotlinlang.org/docs/lambdas.html)). Kotlin has
  no record literals either; data classes are built by constructor call.

**Summary:** Lean is the only one of the three with record literals as
arguments. It avoids this conflict by keeping braces for structure
instances and using `(f := e)` for named construction. Stitchwort already
has `(f := e)` for constructors (`docs/syntax.md`, "Named arguments":
`Circle (id := "a") (radius := 1)`). So the Lean arrangement is available to
Stitchwort if braces stopped meaning named construction.

## 5. Decisions

**D1370. What does `C { … }` mean after a constructor?**

- **(a) [rec] Keep it as it is.** Braces after a constructor always name its
  fields, and a record argument is `C ({ … })`. The error already says
  exactly that (§2). The rule is syntactic, so the meaning never depends on
  types or on later changes to the constructor, and patterns agree with
  expressions. The cost is the brackets in wrapper-of-record code. A type
  designed for this, with its fields on the constructor
  (`| TextCard (id: Text) (text: Text)`), gets `TextCard { id = …, text = … }`
  directly.
- **(b) Fall back by names.** Braces name the constructor's fields. When some
  name isn't one of them, and the constructor has one explicit field whose
  type (at the expected type) is a record having every name, the braces are
  that record. This fixes the friction case without breaking existing code.
  Costs (§3): a shared name like `value` goes to the constructor's own field;
  generic constructors need the expected type; defaults allow a silent change
  of meaning; patterns either differ or reopen D593 (b) (D1371).
- **(c) Lean's arrangement: reverse D605 (a).** After a constructor, as after
  a function, braces are always a record argument. Named construction is
  written with named arguments, `Circle (ref := 1) (id := "a") (text := "t")`,
  which already exist. No conflict and one rule for every callee. Costs:
  punning is lost (`Dot { id, ref = 2 }` becomes `Dot (id := id) (ref := 2)`);
  existing named constructions move to `(f := e)`; `show` can drop its
  brackets again; patterns differ unless they change too (D1371).

**D1371. Only if D1370 is (b) or (c): do patterns follow?**

- **(a) [rec] Yes, patterns follow,** so that a pattern and an expression
  never read `C { … }` differently. For (c) this needs `C (f := p)` patterns,
  which aren't built. For (b) it reopens D593 (b)'s silent-change case, made
  possible by `..`.
- **(b) No.** Patterns keep D593 (b), and expressions differ from them. That
  asymmetry was a known learning cost before D605 (a).
