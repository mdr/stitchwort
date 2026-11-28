# 8. Abilities

A function's type says what it may do besides returning a value. `Nat -> Nat` is pure: it computes a number and nothing else. `Nat -> {IO} Nat` may also read input and print. The things in braces are **abilities**: sets of operations, such as printing, failing, logging or choosing. A function can only perform what its type lists:

<!-- snippet: errors/ability.sw -->
```stitchwort
import Std (IO)

def total (prices: List Nat): Nat :=
  IO.print "adding up ${prices.length} prices"
  prices.sum
```

<!-- output: check errors/ability.sw -->
```text
[E-ABILITY] Error: this may perform `IO`, which isn't allowed here
   ╭─[ errors/ability.sw:4:3 ]
   │
 4 │ ╭─▶   IO.print "adding up ${prices.length} prices"
 5 │ ├─▶   prices.sum
   │ │
   │ ╰────────────────── `IO` isn't in the abilities of the enclosing function or handler
   │
   │     Note: add `IO` to the function's type (`-> {IO …} …`), or handle it
───╯
1 error: in `total`
```

Abilities are Stitchwort's version of algebraic effects, the design behind Unison's abilities and Koka's effects. The code that performs operations is plain, direct-style code: no monads, no `await`. What the operations *mean* is decided separately, by a **handler**. The same code can print its log in one place and collect it into a list in a test.

## Declaring an ability

An ability lists its operations. Each takes one argument (use `()` for none) and has a result:

<!-- snippet: abilities.sw#declare -->
```stitchwort
ability Log where
  say: Text → {Log} ()

def checkout (items: Nat): {Log} Nat :=
  say "checking out ${items} items"
  let price := items * 5
  say "the price is ${price}"
  price
```

`checkout` performs `say` twice. Each line of the block runs in order, and `let` lines run when they're reached.

## Handling it

A handler runs a computation and says what each operation does. `handle prog() with` takes a `return` clause, for when the computation finishes with a value, and a clause per operation. In `| say message, resume =>`, `message` is the operation's argument and `resume` is the rest of the computation from that point: call it with the operation's result to carry on.

This handler collects the messages in a list. Each clause returns a function that takes the messages said so far, which is how a handler keeps state:

<!-- snippet: abilities.sw#handle -->
```stitchwort
def collectLog (prog: () → {Log | e} a): {e} (a, List Text) :=
  let run: List Text → {e} (a, List Text) :=
    handle prog() with
      | return result => said => (result, said)
      | say message, resume => said => resume () (said ++ [message])
  run []

test "collected" := collectLog (() => checkout 3) == (15, ["checking out 3 items", "the price is 15"])
```

A few things to notice:

- **The computation is a thunk.** `collectLog` takes `prog: () -> {Log | e} a`, a function of no arguments, and the caller writes `() => checkout 3`. Passing `checkout 3` itself would run it at the call, before the handler is in place.
- **`{Log | e}` is "`Log`, plus whatever `e` stands for".** `e` is a row variable: the handler removes `Log` and passes every other ability through to its own type, `{e}`. So `collectLog` works around code that also prints, or fails.
- **The handler stays in place.** `resume` continues under the same handler, so later `say`s are caught too.

A handler that ignores the operation just resumes:

<!-- snippet: abilities.sw#ignore -->
```stitchwort
def quietly (prog: () → {Log | e} a): {e} a :=
  handle prog() with
    | return result => result
    | say _, resume => resume ()

test "ignored" := quietly (() => checkout 2) == 10
```

And one that prints performs `IO` in its clause, so its own type says `{IO | e}`:

<!-- snippet: abilities.sw#print -->
```stitchwort
def printLog (prog: () → {Log, IO | e} a): {IO | e} a :=
  handle prog() with
    | return result => result
    | say message, resume =>
      IO.print "log: ${message}"
      resume ()

def main(): {IO} () :=
  let price := printLog (() => checkout 4)
  IO.print "total: ${price}"
```

<!-- output: run abilities.sw -->
```text
log: checking out 4 items
log: the price is 20
total: 20
```

An operation's result can be anything the handler chooses. Here `next()` asks the handler for a number, and the handler threads a counter through, as a mutable variable would in another language:

<!-- snippet: abilities.sw#state -->
```stitchwort
ability Counter where
  next: () → {Counter} Nat

def label (names: List Text): {Counter} List Text := names.map (name => "${next()}. ${name}")

def counting (start: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => count => resume count (count + 1)
  run start

test "numbered" := counting 1 (() => label ["tea", "milk"]) == ["1. tea", "2. milk"]
```

## Effect polymorphism: `{e}`

A function that takes a callback can be polymorphic in the callback's abilities. `applyTwice` says its result performs whatever `f` performs, so it works for pure functions and effectful ones alike:

<!-- snippet: abilities.sw#polymorphic -->
```stitchwort
def applyTwice (f: a → {e} a) (x: a): {e} a := f (f x)

test "pure" := applyTwice (n => n + 1) 0 == 2
def loggedStep (n: Nat): {Log} Nat :=
  say "at ${n}"
  n + 1

test "with an ability" := collectLog (() => applyTwice loggedStep 0) == (2, ["at 0", "at 1"])
```

With a pure callback, `e` is empty and `applyTwice` is an ordinary pure function. This is how `List.map`, `List.filter`, the folds and the other list functions work: `xs.map f` takes an `f` that may perform abilities, such as reading or failing, and with a pure `f` it is the ordinary pure `map`. The effects run in list order, each element's once, and `any`, `all`, `find` and `takeWhile` stop calling `f` once the answer is decided.

A data type can carry callbacks with abilities too. Give it a parameter of type `Effects` (from `Std.Effect`), and use it as the row of its fields:

<!-- snippet: abilities.sw#effects-parameter -->
```stitchwort
type Hooks (e: Effects) = { before: Nat → {e} (), after: Nat → {e} () }

def withHooks (hooks: Hooks e) (step: Nat → Nat) (n: Nat): {e} Nat :=
  hooks.before n
  let result := step n
  hooks.after result
  result

def doubled (n: Nat): {Log} Nat :=
  withHooks { before = m => say "before ${m}", after = m => say "after ${m}" } (m => m * 2) n

test "hooks" := collectLog (() => doubled 5) == (10, ["before 5", "after 10"])
```

The row is worked out where the value is used; there's no syntax yet for writing a particular row, such as `Hooks {Log}`, as a type argument.

### Finding a function when you don't know its abilities

`stitchwort search` finds functions by the shape of their type, and abilities are part of a type. When you don't know which abilities a function performs, write `_` for its row: `{_}` is any abilities, none included.

```text
$ stitchwort search --in Std '() → {_} Int'
1 match for  () → {_} Int

int : () → {Parse Char} Int  Std.Parse  std/Parse/Chars.sw:59
    A whole number with an optional '+' or '-' in front, else "expected a number".
```

`{Parse _ | _}` is `Parse` and maybe more, as `{Log | e}` is in a type; `{Parse _}` is exactly `Parse`. A pattern may be just a computation type, `{Parse _ | _} Int`, which finds a value of that type of any shape. The results whose rows have fewer abilities you didn't write come first. A pattern without braces, `() → Int`, means a pure function, as the type does; when nothing pure matches, the search tries again with the abilities left open and says so. The details are in [syntax.md](../syntax.md#lemma-search-stitchwort-search).

## Failing: `Fail` and `Abort`

`Fail` is the library's ability for operations that can fail with a message, like exceptions, but visible in the type. `need` takes the value out of an `Option` or fails with a message, `ensure` fails when a condition is false, and `fail` fails wherever a value of any type is expected. `toResult` handles it, turning the computation into a `Result`:

<!-- snippet: abilities.sw#fail -->
```stitchwort
type Turn = { left: Bool, distance: Nat }

def Turn.parse (text: Text): {Fail} Turn :=
  let (direction, rest) := need text.uncons "expected a turn, got nothing"
  ensure (direction == 'L' ∨ direction == 'R') "expected L or R, got '${text}'"
  { left = direction == 'L', distance = rest.toNatOrFail }

def parseTurns (lines: List Text): {Fail} List Turn := lines.map Turn.parse

test "a turn" := toResult (() => Turn.parse "L68") == Ok { left = True, distance = 68 }
test "a bad turn" := toResult (() => parseTurns ["L1", "X2"]) == Err "expected L or R, got 'X2'"
test "context" :=
  toResult (() => Fail.context "line 2" (() => Turn.parse "R")) == Err "line 2: expected a whole number, got ''"
```

`Fail.context` puts a label in front of a failure's message. Other handlers: `Fail.toOption`, `Fail.orElse` (a default) and `Fail.recover` (a function of the message). `Option.orFail` and `Text.toNatOrFail` are dot-notation forms.

`Abort` is the same without a message, for code where the reason doesn't matter:

<!-- snippet: abilities.sw#abort -->
```stitchwort
def halfOf (n: Nat): {Abort} Nat :=
  Abort.ensure (n % 2 == 0)
  n / 2

test "abort" := Abort.toOption (() => halfOf 6) == Some 3 ∧ Abort.toOption (() => halfOf 7) == None
```

## Searching: `Each`

`Each` runs the rest of a computation once for each element of a list, and collects every result, like nested loops with a filter, or a Scala `for`/`yield`:

<!-- snippet: abilities.sw#each -->
```stitchwort
def triples (n: Nat): List (Nat, Nat, Nat) := Each.collect (() =>
  let a := Each.each (1 ..= n)
  let b := Each.each (a ..= n)
  let c := Each.each (b ..= n)
  Each.require (a * a + b * b == c * c)
  (a, b, c))

test "pythagorean triples" := triples 13 == [(3, 4, 5), (5, 12, 13), (6, 8, 10)]
```

## Parsing: `Parse`

A parser from `Std.Parse` is direct-style code with the `Parse` ability. The ability takes the type of what it reads: a parser of text is `{Parse Char}`, and the combinators work over any `Parse t` (a list of tokens, say). It reads with `nat()`, `char ','` and `text "p="`, and chooses with `oneOf`, `optional` and `many`. A runner gives it the input: `Parse.eachLine` parses each line on its own, `Parse.all` the whole input. Either turns a failure into a `Fail` that names the line and column:

<!-- snippet: abilities.sw#parse -->
```stitchwort
type Box = { x: Nat, y: Nat, z: Nat }

def box(): {Parse Char} Box :=
  let x := nat()
  char ','
  let y := nat()
  char ','
  let z := nat()
  { x, y, z }

def parseBoxes (input: Text): {Fail} List Box := Parse.eachLine input box

test "boxes" :=
  toResult (() => parseBoxes "162,817,812\n57,618,57\n")
    == Ok [{ x = 162, y = 817, z = 812 }, { x = 57, y = 618, z = 57 }]
test "a bad box" :=
  toResult (() => parseBoxes "162,817,812\n57,6x8,57\n") == Err "line 2, column 5: expected ',', got 'x'"
```

A line such as `char ','` is run for what it reads, and its value is dropped. A line that performs nothing can't do anything, so the compiler warns about it (`W-NO-EFFECT`): `char` without its argument, or a parser named without its `()`, as in `box` for `box()`.

A choice always backs up: when one alternative fails, the next starts from the same place, and an error names the furthest point any alternative reached and what was expected there. Input in sections goes through `sections` and `section`. The parsers that read at least one value (`many1`, `sepBy1`, `lines`, `sections`, `section`, `grid`) give a `NonEmptyList`; `.toList` makes it a plain list. A recursive grammar uses `recursive (self => …)`, and a rule must not call `self` before reading something: left recursion can hide behind an earlier alternative and quietly accept less than you meant, so read a repeated part with a loop such as `sepBy1` instead. For operators that group from the left, `Parse.chainLeft operand operator` reads `operand (operator operand)*` and folds it: `operator` is a parser that gives the function joining its two sides, so with `-` giving `(left right => left - right)`, `8-3-2` reads as `(8 - 3) - 2`. Several levels of operators are one `Parse.operators "an operator" levels operand`, where `levels` lists them from the loosest, each with its `associativity` (`LeftAssociative` or `RightAssociative`) and an `operator` that says, for an item, whether it is one of that level's and what it joins: it gives the results and messages of a `chainLeft` per level, but looks at the next item once per operand instead of trying every level.

### Lex, then parse

A grammar with operators and brackets is easier in two passes: a lexer reads the characters into tokens, and a parser reads the tokens. Both are written with the same combinators. A lexer is a `{Parse Char}` parser whose value is a token wrapped in `Parse.located`, which keeps where the token was read (`offset` and `length`, in characters); a token parser is a `{Parse (Parse.Located Token)}` parser, and `Parse.tokens` runs the two one after the other:

<!-- snippet: abilities.sw#lex-parse -->
```stitchwort
type Token =
  | Num (value: Nat)
  | Name (text: Text)
  | Plus
  | Times
  | Open
  | Close

type Expr =
  | Lit (value: Nat)
  | Var (name: Text)
  | Add (left: Expr) (right: Expr)
  | Mul (left: Expr) (right: Expr)

def lexToken(): {Parse Char} Parse.Located Token :=
  Parse.spaces()
  Parse.located (() =>
    Parse.oneOf [
      () => Num nat(),
      () => Name (Parse.takeWhile1 "a name" Char.isAsciiLetter),
      () =>
        char '+'
        Plus,
      () =>
        char '*'
        Times,
      () =>
        char '('
        Open,
      () =>
        char ')'
        Close
    ])

def operandOf (token: Parse.Located Token): Option Expr := match token with
  | { value = Num value, .. } => Some (Lit value)
  | { value = Name name, .. } => Some (Var name)
  | _ => None

def symbolIs (wanted: Token) (token: Parse.Located Token): Option () := if token.value == wanted then Some () else None

def symbol (what: Text) (wanted: Token): {Parse (Parse.Located Token)} () := Parse.one what (symbolIs wanted)

def expression(): {Parse (Parse.Located Token)} Expr := Parse.recursive (self =>
  let atom := () =>
    Parse.oneOf [
      () => Parse.one "an operand" operandOf,
      () =>
        symbol "'('" Open
        let inner := self()
        symbol "')'" Close
        inner
    ]
  let product := () =>
    Parse.chainLeft atom (() =>
      symbol "'*'" Times
      (left right => Mul left right))
  Parse.chainLeft product (() =>
    symbol "'+'" Plus
    (left right => Add left right)))

def parseExpression (input: Text): {Fail} Expr := Parse.tokens input (() => Parse.many lexToken) expression

test "lex, then parse" :=
  toResult (() => parseExpression "1 + 2 * (x + 3)") == Ok (Add (Lit 1) (Mul (Lit 2) (Add (Var "x") (Lit 3))))
test "a bad token" :=
  toResult (() => parseExpression "1 + * 2") == Err "line 1, column 5: expected an operand or '(', got '*'"
test "the end of the input" :=
  toResult (() => parseExpression "(1 + 2")
    == Err "line 1, column 7: expected '*', '+' or ')', got the end of the input"
test "a character no token starts with" :=
  toResult (() => parseExpression "1 + ?")
    == Err "line 1, column 5: expected a number, a name, '+', '*', '(' or ')', got '?'"
```

`Parse.one what select` reads the next token if `select` gives a value for it and fails with "expected `what`" if not, so `operandOf` says which tokens are operands and what an operand means. `Parse.span1` is the same for a run of tokens that pass a test (`takeWhile1` for any items). A selector is a named function, with the token's type written, because a record pattern in a lambda (`match some | { value = Num value, .. } => …`) needs to know the type it matches where the lambda is checked, and that type is only known from the parser's signature once the call is done. The rest is as for characters: `oneOf`, `many`, `chainLeft` and `recursive` work on tokens, and so do the `Parse.Reads` and `Parse.Runs` lemmas. A recursive rule that passes something down, such as the layout a nested part is read at, is `Parse.recursiveWith (self argument => …) first`, with `self` taking the argument. A lexer in which every character belongs to some token (spaces and comments included) is `Parse.locatedToEnd lexeme`, where `lexeme` reads one token from the characters left: it keeps no handler per token, so it is about a third faster than `many` of `located` (a lexeme that fails then fails the whole lex). A lexer with something to give besides its tokens, such as the comments after the last one, returns a pair and goes through `Parse.tokensWith`, whose parser takes the second part. `Parse.lastRead start Parse.mark()` is the last item read since `start`.

Errors are in the source's terms. A failure in the lexer reads as it does for `Parse.all`. A failure in the token parser names the line and column of the token it stopped at, what it expected, and the token as it was written (`got '*'`), or "got the end of the input" when it ran out; `Parse.tokens` works these out from each token's `offset` and `length`, so a token needs no `Show`. To keep the failure itself and map it your own way, run `Parse.run tokens parser`: its `offset` counts tokens.

The rest of the library (`findAll`, `grid`, `Parse.token` (spaces around a parser), `Parse.ensure`, the `Parse.Reads` lemmas for proving what a parser accepts, and the `Parse.Follows` lemmas for proving that two runs on related inputs, such as a source and the same source without its comments, give related results, for a parser that never backs up) is described by `stitchwort doc` (for instance `stitchwort doc Parse.findAll`), the [parser library note](../proposals/parser-combinators.md) and `examples/accept/parse-basics.sw`.

## `IO` and `main`

`IO`'s main operations are `IO.print` (writes a line), `IO.readLine()` (the next line, or `None` at the end of the input) and `IO.readAll()` (the rest of the input). `IO.readAllLines()` is the input as a list of lines. `IO.args()` gives the program's arguments (those after `--` in `stitchwort run Main.main -- a b`), `IO.randomSeed()` a fresh number each run, `IO.printError` writes a line on standard error (for a warning that shouldn't mix with the output; `IO.simulate` drops it), and a few lower-level operations (`write`, `console`, `keysMode`, `readBytes`) are for programs that drive a terminal ([syntax.md, IO](../syntax.md#io)).

`main` has the type `{IO} ()`, and may also be `{IO, Fail} ()`: a failure that reaches the top is printed to standard error as `error: …`, after whatever was printed before it, and the exit status is 1. The shop from [chapter 6](06-namespaces-and-library.md), on an order it can't parse:

<!-- output: run --project project Shop.Report.main < project/bad-orders.txt -->
```text
error: expected a quantity, got 'two'
```

`main` can also be `Partial` ([chapter 7](07-recursion.md)), and it can be both `Fail` and `Partial`. This loop reads numbers until the end of its input and fails on a line that isn't one:

<!-- snippet: sum-lines.sw@sumLines,main -->
```stitchwort
def sumLines (total: Nat): {IO, Fail, Partial} Nat := match IO.readLine() with
  | None => total
  | Some line =>
    let number := line.toNatOrFail
    IO.print "total so far ${total + number}"
    sumLines (total + number)

def main(): {IO, Fail, Partial} () := IO.print "sum ${sumLines 0}"
```

<!-- output: run sum-lines.sw < sum-lines.input -->
```text
total so far 1
total so far 3
error: expected a whole number, got 'x'
```

A handler still can't go around partial code, so `Fail.toResult` can't catch a failure from inside `sumLines`: only `main` can leave it unhandled.

To test code that performs `IO`, handle it: `IO.simulate` runs a computation against a list of input lines and returns what it printed ([chapter 9](09-testing.md)).

## Files

`Files` is the ability for the disk, separate from `IO`: a function whose row says `{IO}` can't touch a file, and one that says `{Files}` can't print. It has four operations, each on a whole file or one folder, and each returns a `Result`, so a missing file is a value to handle rather than a crash:

- `Files.read path` gives the file's text (`NotText` if its bytes aren't UTF-8);
- `Files.write (path, text)` replaces the file whole, or creates it, but never creates a folder. The text goes to a temporary file that is then renamed over the old one, so a program stopped halfway never leaves a half-written file;
- `Files.list path` gives a folder's entries (`Entry`: a `name` and a `kind`, `File`, `Folder` or `Other`), sorted by name;
- `Files.info path` gives a `FileInfo`: the `kind` and the `size` in bytes.

A `Path` is a small record of its parts, not a bare `Text`: `"notes/today.txt".toPath` (or `Path.parse`) makes one, `folder.child "today.txt"` puts a name inside a folder (and `folder.childPath other` a relative path), and `path.name`, `path.parent`, `path.extension` and `path.show` take it apart. `/` separates parts on every system, and a path that doesn't start with `/` is relative to the folder the program was started in. A failure is a `FileError`: `NotFound`, `NotPermitted`, `NotAFile` (a folder where a file was wanted), `NotAFolder` (a file where a folder was wanted), `NotText`, or `OtherError` with the system's own message. Each holds its path, and `${error}` says what went wrong for people.

`main` may have `Files` in its row beside `IO` (and `Fail` and `Partial`), and then `stitchwort run` and a built executable perform it on the real disk, with your permissions, as a program in any other language would. Under `--js` it isn't supported yet. This one counts the lines of the files it's given:

<!-- snippet: files.sw#count -->
```stitchwort
def lineCount (path: Path): {Files} Result Nat FileError := Files.read path |> .map (text => text.lines.length)

def main(): {Files, IO} () := IO.args().forEach (name =>
  match lineCount name.toPath with
    | Ok count => IO.print "${name}: ${count} lines"
    | Err error => IO.printError "${error}")
```

<!-- output: run files.sw -- hello.input missing.txt -->
```text
hello.input: 2 lines
missing.txt: no such file or folder
```

Checking, testing and the editor never touch the disk: they treat `Files` as data, as they do `IO`, so checking someone else's project is safe whatever it says. To test file code, run it on a pretend disk: `Files.simulate disk prog` runs `prog` against a `Disk` held in memory (`Disk.fromList` of paths and texts, with the folders they're in; `Disk.empty`), and gives the disk afterwards with the result. Here a tool tidies a file in place, and the tests check what it did to the disk:

<!-- snippet: files.sw#tidy -->
```stitchwort
-- Each line without the spaces at its ends; written back only if that
-- changes anything. `Ok True` if it did.
def tidy (path: Path): {Files} Result Bool FileError := match Files.read path with
  | Err error => Err error
  | Ok text =>
    let tidied := text.lines.map (line => line.trim) |> .joinWith "\n"
    if tidied == text then Ok False else Files.write (path, tidied) |> .map (done => True)

def notes: Path := "docs".toPath.child "notes.txt"

test "tidy rewrites an untidy file" :=
  let (disk, changed) := Files.simulate (Disk.fromList [(notes, " a \nb")]) (() => tidy notes)
  changed == Ok True ∧ disk.read notes == Ok "a\nb"

test "tidy leaves a tidy file alone" :=
  let tidyDisk := Disk.fromList [(notes, "a\nb")]
  Files.simulate tidyDisk (() => tidy notes) == (tidyDisk, Ok False)

test "tidy of a missing file" := (Files.simulate Disk.empty (() => tidy notes)).snd == Err (NotFound notes)
```

The pretend disk is ordinary data, so proofs are about it too: the library's laws (`Files.simulateRead`, `Files.simulateWriteOk` and the rest) say what each operation does to a `Disk`, by computing. To see which operations a program made, wrap it in `Files.tracing`, which passes each one on and gives the list of them (`Reads path`, `Writes path`, `Lists path`, `Infos path`) with the result: `Files.simulate disk (() => Files.tracing prog)`. A test of a program that uses both abilities nests the handlers: `IO.simulate input (() => Files.simulate disk prog)`.

## How it runs

Before the kernel sees a program, a computation with abilities is translated into ordinary data: a tree of operations, each with the rest of the computation as a function ([core.md, Abilities](../core.md#abilities)). A handler is a fold over that tree, so the kernel's usual termination check is what shows that handlers finish. A use of an effect-polymorphic function with a pure callback is plain pure code. A pure function stays pure: a handler used inside it doesn't show in its type, so `collectLog` can be called from a test.

More: [syntax.md, Abilities](../syntax.md#abilities), [`Abort`](../syntax.md#abort), [`Fail` and `Result`](../syntax.md#fail-and-result), [`Each`](../syntax.md#each), [`Files`](../syntax.md#files), and the design notes [file-io-and-text.md](../proposals/file-io-and-text.md), [abilities.md](../proposals/abilities.md), [effect-polymorphism.md](../proposals/effect-polymorphism.md), [errors.md](../proposals/errors.md) and [parser-combinators.md](../proposals/parser-combinators.md).
