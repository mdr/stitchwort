# 2. Values and definitions

## Definitions

Everything at the top level of a file is a declaration, and the most common one is `def`. A definition has a name, parameters in brackets, a type after the colon, and a body after `:=`:

<!-- snippet: values.sw#definitions -->
```stitchwort
def answer: Nat := 42

def double (n: Nat): Nat := n + n

def greeting (name: Text): Text := "Hello, " ++ name ++ "!"

def area (width: Nat) (height: Nat): Nat := width * height
```

The house style is `name: Type`, with no space before the colon, as in Scala and TypeScript. A declaration starts in column 0, and every line that continues it is indented. `--` starts a comment that runs to the end of the line.

There are no statements and no mutation. A definition is a value, and calling a function computes a new value from its arguments. `=` is only equality (a proposition, used in theorems), and `:=` gives a definition or a `let` its value.

## Documentation

A comment line that starts `--|` documents the declaration below it. The compiler ignores it, and tools show it: the language server on hover, `stitchwort search` as a one-line summary (the first sentence), and `stitchwort doc NAME`, which also prints the declaration's header, the tests named after it as examples, and the theorems about it:

<!-- snippet: values.sw#docs -->
```stitchwort
--| How many shelves `width` wide fit along a wall, rounded down. A width of 0
--| fits none. For the floor see [`area`].
def shelves (wall: Nat) (width: Nat): Nat := wall / width

test "shelves" := shelves 250 60 == 4 ∧ shelves 250 0 == 0
```

<!-- output: doc shelves values.sw --theorems 0 -->
```text
Main.shelves  definition
  def shelves (wall: Nat) (width: Nat): Nat
  values.sw:17  (import Main (shelves))

  How many shelves `width` wide fit along a wall, rounded down. A width of 0
  fits none. For the floor see `area`.

Examples:
  test "shelves" := shelves 250 60 == 4 ∧ shelves 250 0 == 0     values.sw:19
```

A doc says what the name and the type can't: an edge case, a unit, what a `None` means, why. ``[`area`]`` links to another declaration, and the compiler warns (`W-DOC-LINK`) if it names nothing. A plain `--` comment is a note for whoever edits the code, and no tool shows it. Most declarations in application code need no doc, while the standard library documents all of its API, so `stitchwort doc List.filterMap` is often quicker than reading the source ([chapter 6](06-namespaces-and-library.md#the-standard-library)). The rules are in [syntax.md](../syntax.md#doc-comments).

## Blocks

A body that starts on a new line is a **block**. Each line at the block's indentation is one step: `let x := e` names a value for the lines after it, and the last line is the result:

<!-- snippet: values.sw#blocks -->
```stitchwort
def describe (n: Nat): Text :=
  let half := n / 2
  let parity := if n % 2 == 0 then "even" else "odd"
  "${n} is ${parity}, and half of it is ${half}"
```

`if` is an expression with both branches required, like Scala's `if` or TypeScript's `?:`. A chain of `else if`s can be laid out one per line:

<!-- snippet: values.sw#if-chain -->
```stitchwort
def grade (score: Nat): Text :=
  if score ≥ 90 then "A"
  else if score ≥ 75 then "B"
  else if score ≥ 50 then "C"
  else "D"
```

A long condition can be split before an operator instead of after it: a line that starts with an infix operator (`&&` or `∧`, `||` or `∨`, `->`, `<->`, `=`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `+`, `++`, `*`, `/`, `%`, `!in`) continues the line above, whether it is indented further or lines up with the block. `-` and `!` can start an expression, so a line starting with either, at the block's column, is a new step:

<!-- snippet: values.sw#leading-operator -->
```stitchwort
def validScore (score: Nat): Bool :=
  0 <= score
  && score <= 100
  && score != 13
```

`if` takes a `Bool`, or a statement the compiler can decide, such as `score >= 90`. The difference matters for proofs and is explained in [chapter 10](10-proofs.md); in ordinary code you can use comparisons as conditions without thinking about it.

Comparisons chain, as in mathematics: `if 90 <= score <= 100` is `90 <= score && score <= 100`, and `0 <= i < n` says that `i` is a valid index. `<` and `<=` chain together, as do `>` and `>=` (`hi >= x > lo`), for any number of links. A middle that is a call, as in `1 <= digits.length <= 3`, is computed once, and the later links are only tested if the earlier ones hold. Chains that mix directions (`a < b > c`), or use `=`, `==`, `!=` or `in`, are an error (`E-COMPARISON-CHAIN`) that says what to write instead.

## Text

`Text` is a sequence of Unicode characters, written in double quotes. `++` joins two texts (and two lists). Inside a text literal, `${e}` inserts the value of any expression whose type has a `Show` instance, which every type you declare gets automatically ([chapter 5](05-interfaces.md)):

<!-- snippet: values.sw#interpolation -->
```stitchwort
def summary (name: Text) (items: List Nat): Text :=
  "${name} bought ${items.length} items: ${items}, costing ${items.sum}"

test "summary" := summary "Ada" [3, 4] == "Ada bought 2 items: [3, 4], costing 7"
```

A text over several lines is written between `"""` and `"""`. The text starts on the line after the opening quotes, and the indentation common to all lines is removed, so the literal can be indented with the code around it. This is how puzzle inputs and test data are usually written:

<!-- snippet: values.sw#text-block -->
```stitchwort
def example: Text := """
  L68
  L30
    R48
  """

test "a text block" := example == "L68\nL30\n  R48\n"
test "its lines" := example.lines == ["L68", "L30", "  R48"]
```

A closing `"""` on its own line leaves a newline after the last line. `Text.lines` ignores a final newline, so `example.lines` has three lines.

A `Char` is one Unicode character, written in single quotes: `'A'`, `'\n'`. `Text.uncons` splits a text into its first character and the rest, if there is one:

<!-- snippet: values.sw#chars -->
```stitchwort
def initial (name: Text): Char := match name.uncons with
  | Some (first, _) => first
  | None => '?'

test "initial" := initial "Ada" == 'A' ∧ initial "" == '?'

test "digit tests" := '7'.isAsciiDigit ∧ ¬'x'.isAsciiDigit ∧ 'x'.isAsciiLetter ∧ 'Q'.isAsciiUppercase
```

To classify a character, use the tests `isAsciiDigit`, `isAsciiLetter`, `isAsciiLowercase`, `isAsciiUppercase`, `isAsciiAlphanumeric` and `isAsciiSpace`, which look only at the character's code. `Char.digitValue` is the one to use when you want a digit's number (`'7'.digitValue` is `Some 7`).

`Some` and `None` are the two cases of `Option`, Stitchwort's way of saying a value may be missing ([chapter 3](03-data.md)). There is no `null`.

## Numbers

`Nat` is the natural numbers: 0, 1, 2 and so on, with no upper limit. Arithmetic never overflows. Subtraction stops at zero, and `/` and `%` round down:

<!-- snippet: values.sw#nat -->
```stitchwort
test "no overflow" := 2 * 1000000000000 * 1000000000000 == 2000000000000000000000000
test "subtraction stops at zero" := 3 - 5 == 0
test "division rounds down" := 7 / 2 == 3 ∧ 7 % 2 == 1
```

`Int` is the integers, also unbounded. A literal is a `Nat` unless something says otherwise: the expected type, an `Int` operand, or a minus sign. There is no implicit conversion between the two:

<!-- snippet: values.sw#int -->
```stitchwort
def balance: Int := 3 - 5

test "Int subtraction" := balance == -2
test "a negative literal is an Int" := -5 + 2 == -3
test "converting" := balance.toNat == 0 ∧ (7: Nat).toInt == 7
test "absolute value" := Int.natAbs balance == 2
```

`n.toInt` converts a `Nat` to an `Int`, `i.toNat` the other way (negative numbers become 0), and `Int.natAbs` gives the absolute value as a `Nat`.

### Dividing by zero

`/` and `%` always give an answer. Dividing by 0 gives 0, and the remainder is then the number itself: `7 / 0` is 0 and `7 % 0` is 7, as in Lean, Rocq and Isabelle. With those values `n = (n / d) * d + n % d` holds for every `d`, 0 included. `Int`'s divisions do the same.

<!-- snippet: values.sw#division-by-zero -->
```stitchwort
test "dividing by 0" := 7 / 0 == 0 ∧ 7 % 0 == 7

def averageOf (total: Nat) (count: Nat): Nat := total / count

test "the average of nothing" := averageOf 10 0 == 0
```

Where 0 should mean something else, say so with an `if` or a guard, as `share` does in [chapter 3](03-data.md#conditions-on-cases). A claim about the result is a different matter: `x % d < d` holds only when `d` isn't 0, so the lemma that says it, `Nat.modLt`, asks for that fact, and a proof using it has to have the fact at hand ([chapter 10](10-proofs.md)). The usual way is a condition written as a statement, `if d != 0` or `if d = 0` (one `=`: equality as a statement): each branch then knows which way it went. A `Bool` test, `if d == 0`, computes `True` or `False` but tells the compiler nothing about `d`.

### Other number types

`Float` is a 64-bit IEEE 754 double, the same as a JavaScript `number`. A literal with a decimal point is a `Float`, and `Float` never mixes with `Nat` or `Int`:

<!-- snippet: values.sw#float -->
```stitchwort
def celsius (fahrenheit: Float): Float := (fahrenheit - 32.0) * 5.0 / 9.0

test "boiling" := celsius 212.0 == 100.0
test "doubles round" := 0.1 + 0.2 == 0.30000000000000004
```

`SafeNat` and `SafeInt` are whole numbers that fit a JavaScript `number` exactly (up to 2^53 - 1 in size). They exist for the JavaScript boundary ([chapter 11](11-running-and-shipping.md)); compute with `Nat` and `Int`, and convert when a value crosses:

<!-- snippet: values.sw#safe -->
```stitchwort
def small: Option SafeNat := SafeNat.ofNat 42

test "fits a JS number" := small.isSome
test "too big for a JS number" := (SafeNat.ofNat 9007199254740992).isNone
```

Two more number types appear later: `Fin n`, the numbers below `n`, used as positions in a vector of length `n`, and `Mod n`, the numbers below `n` where `+` and `*` wrap around, as on a clock. Both are in [syntax.md](../syntax.md#numbers).
