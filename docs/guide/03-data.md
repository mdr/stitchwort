# 3. Data

Stitchwort has two ways to declare a type of your own: a **variant** type, which lists the shapes a value can have, and a **record**, which has named fields. Both are declared with `type`.

## Variants

A variant type is like a sealed trait with case classes in Scala, or a discriminated union in TypeScript. Each **constructor** is one case, with its own fields:

<!-- snippet: data.sw#variant -->
```stitchwort
type Shape =
  | Circle (radius: Nat)
  | Rect (width: Nat) (height: Nat)
  | Dot

def Shape.area: Shape → Nat
  | Circle radius => 3 * radius * radius
  | Rect width height => width * height
  | Dot => 0

test "area" := (Rect 3 4).area == 12
```

A function over a variant is written as a list of **arms**, one per case. Each arm starts with `|`, matches a pattern, and gives the result after `=>`. The arms replace the `:=` body.

`def Shape.area` puts `area` in the namespace of `Shape`, which is what lets you call it with dot notation: `(Rect 3 4).area` means `Shape.area (Rect 3 4)` ([chapter 4](04-functions.md)).

A constructor applied to its fields is a value: `Rect 3 4`. Constructors start with a capital letter, and so do type names. Types can be recursive:

<!-- snippet: data.sw#recursive -->
```stitchwort
type Expr =
  | Num (value: Int)
  | Add (left: Expr) (right: Expr)
  | Mul (left: Expr) (right: Expr)
  | Neg (inner: Expr)

def Expr.value: Expr → Int
  | Num n => n
  | Add a b => a.value + b.value
  | Mul a b => a.value * b.value
  | Neg e => -e.value

test "evaluate" := (Add (Num 2) (Mul (Num 3) (Neg (Num 4)))).value == -10
```

## Every case must be handled

The arms of a function, and the alternatives of a `match`, must cover every possible value. Leave one out and the program doesn't check:

<!-- snippet: errors/missing-case.sw -->
```stitchwort
type Shape =
  | Circle (radius: Nat)
  | Rect (width: Nat) (height: Nat)
  | Dot

def Shape.area: Shape → Nat
  | Circle radius => 3 * radius * radius
  | Rect width height => width * height
```

<!-- output: check errors/missing-case.sw -->
```text
[E-NONEXHAUSTIVE] Error: missing case: no arm matches `Dot`
| Dot => ?
   ╭─[ errors/missing-case.sw:7:3 ]
   │
 7 │ ╭─▶   | Circle radius => 3 * radius * radius
 8 │ ├─▶   | Rect width height => width * height
   │ │
   │ ╰───────────────────────────────────────────── missing case: no arm matches `Dot`
───╯
1 error: in `Shape.area`
```

This is what makes adding a constructor safe: the compiler lists every function that needs a new arm. A wildcard `_` matches anything, so a final `| _ => …` arm covers whatever is left, at the cost of that safety.

### Cases that can't happen

A case that can't happen needs no arm. Here `h` says the shape has an area, so it isn't a `Dot`:

<!-- snippet: data.sw#impossible -->
```stitchwort
def Shape.hasArea: Shape → Bool
  | Dot => False
  | _ => True

def Shape.width (shape: Shape) (h: shape.hasArea): Nat :=
  match shape with
    | Circle radius => 2 * radius
    | Rect width _ => width

test "width" := (Rect 3 4).width rfl == 3
```

For `Dot`, `h`'s type computes to `False = True`, an equation of two different constructors, which nothing can prove; so no one can call `width` with a `Dot`, and the compiler fills in that case itself. A caller passes the proof that its shape has an area: for `Rect 3 4` that is computing, `rfl`. The arm can also be written, with `()` in place of the pattern for the value that can't exist and no `=>`: `match shape, h with` and the alternative `| Dot, ()`. Leave out a case that can happen and it's still an error that names it. [Chapter 10](10-proofs.md) has more on statements like `h`, and [syntax.md](../syntax.md#impossible-cases) the details.

## Records

A record has named fields. Two record types with the same fields are still different types.

<!-- snippet: data.sw#record -->
```stitchwort
type Person = {
  name: Text,
  age: Nat
}

def ada: Person := { name = "Ada", age = 36 }

def Person.birthday (person: Person): Person := { person | age = person.age + 1 }

def newborn (name: Text): Person := { name, age = 0 }

test "read a field" := ada.name == "Ada"
test "update" := ada.birthday.age == 37
test "the original is unchanged" := ada.age == 36
test "field punning" := (newborn "Grace").age == 0
```

- `{ name = "Ada", age = 36 }` builds a record. Its type comes from where it's used: a signature, an argument's type, an annotation such as `({ … }: Person)`, or something later in the declaration, such as the other side of `==`. Only when nothing says it does the compiler look at the field names: the one record type in scope with exactly those fields. With none, or two, it asks for an annotation.
- `ada.name` reads a field.
- `{ person | age = … }` is a copy with some fields replaced. Values are never changed in place, so the original is untouched.
- A field name alone, as in `{ name, age = 0 }`, is short for `name = name`.

The house style for a declaration over several lines puts a comma at the end of each line, no comma after the last field, and the closing brace in column 0, as above.

Give the nouns of a problem types of their own, records by default, with the operations they support as methods. A `Pass` with a `seatId` method says more than a `List Bool` and a function on it, and a `Pass` can't be passed where a row number is wanted. Write a synonym ([below](#type-synonyms)) only where a type of its own would add nothing.

A record pattern takes the fields apart. `..` ignores the fields not named:

<!-- snippet: data.sw#record-patterns -->
```stitchwort
def Person.label: Person → Text
  | { name, age } => "${name} (${age})"

def isAdult: Person → Bool
  | { age, .. } => age ≥ 18

test "label" := ada.label == "Ada (36)"
```

### Default values

A field may have a default value, written after `:=` (so may a function's parameter, [chapter 4](04-functions.md#default-values)). A literal can then leave it out:

<!-- snippet: data.sw#defaults -->
```stitchwort
type Query = {
  text: Text,
  limit: Nat := 10,
  caseSensitive: Bool := False
}

def simple: Query := { text = "tea" }

test "defaults fill in" := simple.limit == 10 ∧ ¬simple.caseSensitive
test "or are given" := ({ text = "tea", limit = 3 }: Query).limit == 3
```

Defaults are for building values. They don't make a field optional: every `Query` has a `limit`. Leaving out a field without a default is an error that says which fields do have defaults:

<!-- snippet: errors/missing-field.sw -->
```stitchwort
type Query = {
  text: Text,
  limit: Nat := 10,
  caseSensitive: Bool := False
}

def everything: Query := { limit = 100 }
```

<!-- output: check errors/missing-field.sw -->
```text
[E-RECORD-FIELD] Error: this `Query` is missing `text`
   ╭─[ errors/missing-field.sw:7:26 ]
   │
 7 │ def everything: Query := { limit = 100 }
   │                          ───────┬───────
   │                                 ╰───────── every field without a default value must be given
   │
   │ Note: `limit` and `caseSensitive` have default values, so they may be left out
───╯
1 error: in `everything`
```

Use an `Option` field when a value can really be missing.

### Constructors with named fields

A constructor can be declared with its fields in braces instead of brackets, and then it is built and matched by field name. The fields can have defaults. `Meeting { … }` builds a `Meeting` from named fields, in any order, and the pattern `Meeting { minutes, .. }` reads them:

<!-- snippet: data.sw#named-construction -->
```stitchwort
type Event =
  | Meeting { title: Text, minutes: Nat := 30, room: Text }
  | Reminder (title: Text)

def standup: Event := Meeting { title = "Standup", room = "Blue" }
def review: Event := Meeting { title = "Review", minutes = 60, room = "Red" }

def Event.length: Event → Nat
  | Meeting { minutes, .. } => minutes
  | Reminder _ => 0

test "default minutes" := standup.length == 30
```

When every constructor of a type has a field with the same name and type, it is a **shared field**: you can read it and update it without matching first. `title` is shared by both kinds of `Event`, `minutes` isn't:

<!-- snippet: data.sw#shared-fields -->
```stitchwort
test "every Event has a title" := review.title == "Review"

def retitled: Event := { standup | title = "Daily" }

test "shared-field update" := retitled.title == "Daily" ∧ retitled.length == 30
```

### Braces after a constructor

The way a constructor is declared decides what braces after it mean. A constructor declared with brackets, like `Some (value: a)` and most of your own, takes braces as an ordinary record argument, as a function does, in expressions and in patterns:

<!-- snippet: data.sw#braces-argument -->
```stitchwort
def found: Option Person := Some { name = "Ada", age = 36 }

def nameOr (fallback: Text): Option Person → Text
  | Some { name, .. } => name
  | None => fallback

test "braces are a record argument" := nameOr "nobody" found == "Ada"
```

One declared with braces, like `Meeting` above, takes braces as its own fields. So a record that you want to give such a constructor goes in brackets, `Guest ({ name = "Ada", age = 36 })`, or is given by its field, `Guest { person = { name = "Ada", age = 36 } }`; the error says so:

<!-- snippet: errors/constructor-braces.sw -->
```stitchwort
type Person = { name: Text, age: Nat }

type Booking = | Guest { person: Person }

def ada: Booking := Guest { name = "Ada", age = 36 }
```

<!-- output: check errors/constructor-braces.sw -->
```text
[E-UNKNOWN-FIELD] Error: `Guest` has no field `name`
   ╭─[ errors/constructor-braces.sw:5:29 ]
   │
 5 │ def ada: Booking := Guest { name = "Ada", age = 36 }
   │                             ──┬─
   │                               ╰─── `Guest` has no field `name`
   │
   │ Note 1: `Guest`'s fields are `person`
   │
   │ Note 2: `Guest` is declared with its fields in braces, so braces after it name its own fields; to build the `Person` it holds, write `Guest ({ … })`
───╯
1 error: in `ada`
```

Naming a bracket-declared constructor's fields works with named arguments instead, `Rect (height := 4) (width := 3)`, which also fill the defaults of fields left out.

## Patterns

Patterns nest, and lists have their own syntax: `[]` is the empty list, `[x]` a list of one, and `[x, y, ..rest]` a list of at least two, with the rest in `rest`. Numbers and characters are patterns too (text isn't: compare with `==`). The arms are tried from top to bottom, so a general arm goes after the specific ones:

<!-- snippet: data.sw#nested-patterns -->
```stitchwort
def firstTwo: List Nat → Text
  | [] => "nothing"
  | [x] => "just ${x}"
  | [x, y, ..rest] => "${x} and ${y}, then ${rest.length} more"

test "list patterns" := firstTwo [1, 2, 3, 4] == "1 and 2, then 2 more"

def simplify: Expr → Expr
  | Add (Num 0) e => simplify e
  | Mul (Num 1) e => simplify e
  | Neg (Neg e) => simplify e
  | e => e

test "nested patterns" := simplify (Add (Num 0) (Neg (Neg (Num 5)))) == Num 5
```

Several patterns that give the same result are written in one arm with `|`. The alternatives can't bind variables (`_` is fine); for those, write arms of their own:

<!-- snippet: data.sw#or-patterns -->
```stitchwort
type Colour = | Red | Yellow | Green | Blue

def Colour.isWarm: Colour → Bool
  | Red | Yellow => True
  | Green | Blue => False

def keyMove (key: Char): Option Text :=
  match key with
    | 'k' | 'w' => Some "north"
    | 'j' | 's' => Some "south"
    | _ => None

test "or-patterns" := Colour.isWarm Yellow ∧ ¬Colour.isWarm Blue ∧ keyMove 'w' == Some "north" ∧ keyMove 'x' == None
```

`match` takes values apart in the middle of an expression. It can match several values at once, separated by commas:

<!-- snippet: data.sw#match -->
```stitchwort
def compareAges (a: Person) (b: Person): Text :=
  match Ord.compare a.age b.age with
    | Less => "${a.name} is younger"
    | Equal => "the same age"
    | Greater => "${a.name} is older"

def both (x: Option Nat) (y: Option Nat): Option Nat :=
  match x, y with
    | Some a, Some b => Some (a + b)
    | _, _ => None
```

`Ord.compare` gives `Less`, `Equal` or `Greater`, a variant type of the library.

A `let` and a lambda's parameter can be patterns, as long as the pattern can't fail: a tuple or a record, not `Some x`:

<!-- snippet: data.sw#let-patterns -->
```stitchwort
def divide (n: Nat): Text :=
  let (quotient, remainder) := (n / 7, n % 7)
  "${n} = 7 * ${quotient} + ${remainder}"

def total (pairs: List (Text, Nat)): Nat := pairs.foldLeft 0 (sum (_, n) => sum + n)

test "let pattern" := divide 23 == "23 = 7 * 3 + 2"
test "lambda pattern" := total [("a", 1), ("b", 2)] == 3
```

`(a, b)` is a pair; `(a, b, c)` is a pair whose second part is a pair. A tuple type is written the same way: `(Text, Nat)`.

## Conditions on cases

An arm can carry a condition: `if` after the patterns and before `=>`. The arm is used only when its patterns match and the condition holds; when the condition is false, the arms below it are tried. It works in every kind of `match`: `match … with`, a function written as arms, and the forms in [chapter 4](04-functions.md#taking-a-value-apart-in-a-lambda).

<!-- snippet: data.sw#guards -->
```stitchwort
def grade: Nat → Text
  | score if score >= 90 => "distinction"
  | score if score >= 50 => "pass"
  | _ => "fail"

test "conditions on cases" := grade 95 == "distinction" ∧ grade 60 == "pass" ∧ grade 10 == "fail"

def share (total: Nat) (parts: Nat): Nat :=
  match total, parts with
    | amount, count if count != 0 => amount / count
    | amount, _ => amount

test "a condition picks the arm" := share 12 4 == 3 ∧ share 12 0 == 12
```

The condition is also a fact in its arm, as in an `if` ([chapter 2](02-values-and-definitions.md#dividing-by-zero)): in `share`'s first arm `count != 0` is known, so a proof or an `auto` argument there can use it. One condition covers the whole arm. With several patterns (`| a, b if a < b =>`) it comes once, after the last, and with alternatives (`| 'a' | 'e' if strict =>`) it is tested for whichever alternative matched.

The compiler doesn't reason about conditions, so an arm with one covers nothing when it checks that every case is handled. Two conditions that between them cover every number still leave the case missing, and the message points at the guarded arms:

<!-- snippet: errors/guard-missing-case.sw -->
```stitchwort
def grade: Nat → Text
  | score if score >= 90 => "distinction"
  | score if score < 90 => "pass"
```

<!-- output: check errors/guard-missing-case.sw -->
```text
[E-NONEXHAUSTIVE] Error: missing case: no arm matches `_`
| _ => ?
   ╭─[ errors/guard-missing-case.sw:2:3 ]
   │
 2 │ ╭─▶   | score if score >= 90 => "distinction"
 3 │ ├─▶   | score if score < 90 => "pass"
   │ │             ──────┬──────
   │ │                   ╰─────────────────── this arm has a condition, so it covers nothing
   │ │
   │ ╰─────────────────────────────────────── missing case: no arm matches `_`
   │
   │     Note: an arm with `if` covers no case for sure: add an arm without `if` for these values
───╯
1 error: in `grade`
```

End with an arm that has no condition, as `grade` does. Conditions can't perform abilities.

## Option instead of null

A value that may be missing has the type `Option a`, which is `Some value` or `None`. The type tells the caller to handle both, and the compiler checks that they do. The library has the usual helpers, so a `match` is often unnecessary:

<!-- snippet: data.sw#option -->
```stitchwort
def findAdult (people: List Person): Option Person := people.find isAdult

def adultName (people: List Person): Text :=
  match findAdult people with
    | Some person => person.name
    | None => "nobody"

test "found" := adultName [newborn "Bo", ada] == "Ada"
test "with helpers" := (findAdult []).map .name |> .getOrElse "nobody" == "nobody"
```

`Result a e` is the same idea for operations that can fail with a reason: `Ok value` or `Err error`. [Chapter 6](06-namespaces-and-library.md) has more of both, and [chapter 8](08-abilities.md) shows `Fail`, which is often more convenient than returning a `Result` by hand.

## Type synonyms

`type Name = SomeType` gives an existing type another name. Unlike a record, a synonym is interchangeable with what it stands for. It has a namespace of its own, so it can have dot-callable functions:

<!-- snippet: data.sw#synonyms -->
```stitchwort
type Grid = List (List Nat)

def Grid.width (grid: Grid): Nat := grid.map .length |> .maximum |> .getOrElse 0

test "a synonym is the type it names" := ([[1, 2, 3], [4]]: Grid).width == 3
```

A synonym's functions are found by dot notation where the value's type mentions the synonym: a `grid: Grid` parameter, a value annotated as `Grid`, a function's `Grid` result, and anything worked out from those, such as each element in `grids.map (grid => grid.width)` with `grids: List Grid`. A value whose type never mentions `Grid` looks only in the namespace of what `Grid` stands for: `[[1, 2, 3]].width` and `rows.width` with a hand-written `rows: List (List Nat)` look in `List`, and the error says so. There, write `Grid.width rows`, or annotate the value as `Grid` where it's made, as the test above does. Where it does find `Grid`, `List`'s functions still work too (`grid.length`): the synonym's namespace is tried first, then what it stands for.

To make a new type that can't be mixed up with the old one (a `UserId` that isn't any `Text`), use a one-field record instead. At run time a one-field record costs nothing; it is stored as its field.

More: [syntax.md, Records](../syntax.md#records), [Field defaults](../syntax.md#field-defaults), [`match`](../syntax.md#match), and the design notes [records.md](../proposals/records.md) and [variant-fields.md](../proposals/variant-fields.md).
