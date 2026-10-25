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
   ╭─[ errors/missing-case.sw:7:3 ]
   │
 7 │ ╭─▶   | Circle radius => 3 * radius * radius
 8 │ ├─▶   | Rect width height => width * height
   │ │
   │ ╰───────────────────────────────────────────── missing case: no arm matches `Dot`
───╯
```

This is what makes adding a constructor safe: the compiler lists every function that needs a new arm. A wildcard `_` matches anything, so a final `| _ => …` arm covers whatever is left, at the cost of that safety.

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

- `{ name = "Ada", age = 36 }` builds a record. It needs to know which record type it is, from a signature, an argument's type or an annotation such as `({ … }: Person)`. Nothing is guessed from the field names.
- `ada.name` reads a field.
- `{ person | age = … }` is a copy with some fields replaced. Values are never changed in place, so the original is untouched.
- A field name alone, as in `{ name, age = 0 }`, is short for `name = name`.

The house style for a declaration over several lines puts a comma at the end of each line, no comma after the last field, and the closing brace in column 0, as above.

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

A field may have a default value, written after `:=`. A literal can then leave it out:

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
```

Use an `Option` field when a value can really be missing.

### Constructors with named fields

A constructor's fields can be given by name too, and can have defaults. `Meeting { … }` builds a `Meeting` from named fields, and the pattern `Meeting { minutes, .. }` reads them:

<!-- snippet: data.sw#named-construction -->
```stitchwort
type Event =
  | Meeting (title: Text) (minutes: Nat := 30) (room: Text)
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

### A common mistake: braces after a constructor

Braces right after a constructor always name *that constructor's* fields. To put a record inside a constructor, bracket it:

<!-- snippet: errors/constructor-braces.sw -->
```stitchwort
type Person = { name: Text, age: Nat }

def found: Option Person := Some { name = "Ada", age = 36 }
```

<!-- output: check errors/constructor-braces.sw -->
```text
[E-UNKNOWN-FIELD] Error: `Some` has no field `name`
   ╭─[ errors/constructor-braces.sw:3:36 ]
   │
 3 │ def found: Option Person := Some { name = "Ada", age = 36 }
   │                                    ──┬─
   │                                      ╰─── `Some` has no field `name`
   │
   │ Note 1: `Some`'s fields are `value`
   │
   │ Note 2: braces right after a constructor name its own fields; to build the `Person` it holds, write `Some ({ … })`
───╯
```

The second note says what to write: `Some ({ name = "Ada", age = 36 })`.

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
test "with helpers" := ((findAdult []).map (.name)).getOrElse "nobody" == "nobody"
```

`Result a e` is the same idea for operations that can fail with a reason: `Ok value` or `Err error`. [Chapter 6](06-namespaces-and-library.md) has more of both, and [chapter 8](08-abilities.md) shows `Fail`, which is often more convenient than returning a `Result` by hand.

## Type synonyms

`type Name = SomeType` gives an existing type another name. Unlike a record, a synonym is interchangeable with what it stands for. It has a namespace of its own, so it can have dot-callable functions:

<!-- snippet: data.sw#synonyms -->
```stitchwort
type Grid = List (List Nat)

def Grid.width (grid: Grid): Nat := grid.map (.length) |> .maximum |> .getOrElse 0

test "a synonym is the type it names" := ([[1, 2, 3], [4]]: Grid).width == 3
```

To make a new type that can't be mixed up with the old one (a `UserId` that isn't any `Text`), use a one-field record instead. At run time a one-field record costs nothing; it is stored as its field.

More: [syntax.md, Records](../syntax.md#records), [Field defaults](../syntax.md#field-defaults), [`match`](../syntax.md#match), and the design notes [records.md](../proposals/records.md) and [variant-fields.md](../proposals/variant-fields.md).
