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
  if score >= 90 then "A"
  else if score >= 75 then "B"
  else if score >= 50 then "C"
  else "D"
```

`if` takes a `Bool`, or a statement the compiler can decide, such as `score >= 90`. The difference matters for proofs and is explained in [chapter 10](10-proofs.md); in ordinary code you can use comparisons as conditions without thinking about it.

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
def initial (name: Text): Char :=
  match name.uncons with
    | Some (first, _) => first
    | None => '?'

test "initial" := initial "Ada" == 'A' && initial "" == '?'
```

`Some` and `None` are the two cases of `Option`, Stitchwort's way of saying a value may be missing ([chapter 3](03-data.md)). There is no `null`.

## Numbers

`Nat` is the natural numbers: 0, 1, 2 and so on, with no upper limit. Arithmetic never overflows. Subtraction stops at zero, and `/` and `%` round down:

<!-- snippet: values.sw#nat -->
```stitchwort
test "no overflow" := 2 * 1000000000000 * 1000000000000 == 2000000000000000000000000
test "subtraction stops at zero" := 3 - 5 == 0
test "division rounds down" := 7 / 2 == 3 && 7 % 2 == 1
```

`Int` is the integers, also unbounded. A literal is a `Nat` unless something says otherwise: the expected type, an `Int` operand, or a minus sign. There is no implicit conversion between the two:

<!-- snippet: values.sw#int -->
```stitchwort
def balance: Int := 3 - 5

test "Int subtraction" := balance == -2
test "a negative literal is an Int" := -5 + 2 == -3
test "converting" := balance.toNat == 0 && (7: Nat).toInt == 7
test "absolute value" := Int.natAbs balance == 2
```

`n.toInt` converts a `Nat` to an `Int`, `i.toNat` the other way (negative numbers become 0), and `Int.natAbs` gives the absolute value as a `Nat`.

### Division needs a reason

`total / count` needs to know that `count` isn't zero, because division by zero has no answer. The compiler looks for that fact among the conditions that hold where the division is written. A `Bool` test doesn't give it one:

<!-- snippet: errors/divide.sw -->
```stitchwort
def average (total: Nat) (count: Nat): Nat :=
  if count == 0 then 0 else total / count
```

<!-- output: check errors/divide.sw -->
```text
[E-AUTO-STUCK] Error: can't decide `count != 0` here
   ╭─[ errors/divide.sw:2:29 ]
   │
 2 │   if count == 0 then 0 else total / count
   │                             ──────┬──────
   │                                   ╰──────── it depends on values that aren't known until the program runs
   │
   │ Note: establish it first, with `if h: … then … else …`
───╯
```

`count == 0` is a `Bool`: it computes `True` or `False`, but says nothing to the compiler about `count`. Write the condition as a statement instead, `count != 0` or `count = 0` (one `=`: equality as a statement), and each branch knows which way it went:

<!-- snippet: values.sw#division-proof -->
```stitchwort
def averageOf (total: Nat) (count: Nat): Nat :=
  if count != 0 then total / count else 0

def meanOf (total: Nat) (count: Nat): Nat :=
  if count = 0 then 0 else total / count
```

In `averageOf`'s `then` branch, `count != 0` is a fact in scope, and `/` finds it; in `meanOf`'s `else` branch the fact is `Not (count = 0)`, which is the same thing. For a literal divisor (`n / 2`) the compiler checks the fact by computing it, so nothing needs to be written. [Chapter 10](10-proofs.md) explains these facts in general: they are proofs, and `[auto …]` parameters ask for them.

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
