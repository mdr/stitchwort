# 9. Testing

## Tests

A test is a name and a condition that must hold:

<!-- snippet: testing.sw#basics -->
```stitchwort
def wordCount (line: Text): Nat := line.words.length

test "counts words" := wordCount "the quick brown fox" == 4
test "an empty line has none" := wordCount "" == 0
test "a proposition, decided" := wordCount "a b" < 3
test "several at once" := wordCount "a" == 1 ∧ wordCount "a b" == 2
```

The condition is a `Bool`, or a statement the compiler can decide, such as `wordCount "a b" < 3`. Tests live beside the code, are checked like any declaration, and run with `stitchwort test`. They can't take parameters or perform abilities: a test is a closed computation, so its result never changes unless the code does. A test may call `Partial` code ([chapter 7](07-recursion.md)); a test that never finishes is a bug, which you stop as you'd stop a program that hangs. Only `stitchwort test` and the playground's Tests tab run tests: checking, the editor and the playground's checks never do.

That's also why test results are cached by content. Each test's result is stored under a hash of the test and everything it depends on, so `stitchwort test` reruns a test only when something it uses has changed. Formatting, comments and renaming local variables change no hash.

A test can be a block, with `let`s before the condition:

<!-- snippet: testing.sw#block -->
```stitchwort
test "longest word" :=
  let words := "a tea pot of milk".words
  let longest := words.maxBy (.length)
  longest == Some "milk"
```

## When a test fails

When a test's condition is a comparison (`==`, `!=`, `<`, `<=`, `>`, `>=` or `=`), a failure shows its two sides. For two lists or two texts that differ, it also shows where they first differ:

<!-- snippet: failing/tests.sw -->
```stitchwort
-- Tests that fail on purpose, to show what `stitchwort test` says.
import Std (List, Nat, Text)

def parse (line: Text): List Nat := (line.split ',').filterMap Text.toNat

def isSorted: List Nat → Bool
  | Cons a (Cons b rest) => a ≤ b ∧ isSorted (Cons b rest)
  | _ => True

test "parses the example" := parse "1,2,4" == [1, 2, 3]
test "both parts" := parse "7" == [7] ∧ List.length (parse "1,x") == 2
test "sorted" := isSorted (parse "3,1,2")
test "all small" := List.all (parse "1,2,3") (n => n < 3)
```

<!-- output: test failing/tests.sw -->
```text
  ✗ parses the example  ran  (`==` is False)
      left:  [1, 2, 4]
      right: [1, 2, 3]
      first difference at [2]: 4 vs 3
  ✗ both parts          ran  (`==` is False)
      left:  1
      right: 2
      in: List.length (parse "1,x") == 2  (failing/tests.sw:11:41)
  ✗ sorted              ran  (evaluated to False)
  ✗ all small           ran  (evaluated to False)
4 test(s): 0 passed, 4 failed (0 from the cache)
```

- **"parses the example"** shows both lists and the path to the first difference (`[2]`; for nested values something like `[0].tags[2]`, with the two parts found there, or the two constructors if they differ).
- **"both parts"** is an `&&` of comparisons: the failure names the first one that was false, with its text and position (`in:`).
- **"sorted"** and **"all small"** are neither, so all the test can say is that the condition was `False`. When a test like that fails, rewrite it as a comparison to see the values: `parse "3,1,2" == [1, 2, 3]` would show what `parse` gave.

The sides are computed again only when a test fails, so passing tests don't pay for the explanation.

## Testing effectful code

A test is pure, so effectful code is tested through a handler, which turns the computation into a value. For `Fail`, `toResult` gives a `Result` to compare:

<!-- snippet: testing.sw#fail -->
```stitchwort
def parsePair (line: Text): {Fail} (Nat, Nat) :=
  match line.split ',' with
    | [a, b] => (a.toNatOrFail, b.toNatOrFail)
    | _ => Fail.fail "expected two numbers, got '${line}'"

test "a pair" := Fail.toResult (() => parsePair "3,4") == Ok (3, 4)
test "not a pair" := Fail.toResult (() => parsePair "3") == Err "expected two numbers, got '3'"
```

For `IO`, `IO.simulate` runs a computation against a list of input lines, and gives the lines it printed and its result:

<!-- snippet: testing.sw#io -->
```stitchwort
def greetAll(): {IO} () :=
  let names := IO.readAllLines()
  names.map (name => IO.print "Hello, ${name}!")
  IO.print "Greeted ${names.length}"

test "greets everyone" := (IO.simulate ["Ada", "Grace"] greetAll).fst == ["Hello, Ada!", "Hello, Grace!", "Greeted 2"]
```

For your own abilities, the handler you'd write anyway is usually the test's handler too, like `collectLog` in [chapter 8](08-abilities.md). This is one of the main reasons for abilities: the code under test is the real code, and what changes in a test is only what its operations mean.

## Organising tests

In a single file, tests sit beside the code. In a project, put them in a namespace of their own, as the shop project does (`Shop.Tests`) and as `aoc/` does (`Aoc.Day01.Tests`). `stitchwort test Shop` runs the tests of `Shop`, every namespace under it, and every namespace those use; `stitchwort run` doesn't check them.

A test with a puzzle input can read the file at check time with `include "path"`, which is a `Text` literal with the file's contents. Editing the file reruns exactly the tests that include it:

<!-- snippet: ../../../aoc/src/Aoc/Day01/Tests/Input.sw -->
```stitchwort
-- The real puzzle input (aoc/inputs/day01.txt, committed, D119), through
-- `include`: the answers are checked on it when the tests run, and editing
-- the input reruns exactly these tests.
namespace Aoc.Day01.Tests
import Aoc.Day01 (..)
import Std (Fail)

test "real input, part 1" := solvePart1 (Fail.orElse [] (() => parseTurns (include "../../../../inputs/day01.txt").lines)) == 1076
test "real input, part 2" := solvePart2 (Fail.orElse [] (() => parseTurns (include "../../../../inputs/day01.txt").lines)) == 6379
```

## Tests and proofs

A test is a runtime check of one case, like a unit test in other languages; a theorem ([chapter 10](10-proofs.md)) covers all of them, and the checker checks its proof. Keep tests of edge cases beside a theorem that covers them anyway: they document the cases and fail with a clearer message.

## Two runtimes

Tests run on the fast runtime, the same one `stitchwort run` uses. `stitchwort test --reference` runs them on the type checker's own evaluator, the reference that defines what programs mean; it's slower, and the repository's own tests check that the two always agree.

## Property tests

There are no property tests yet. A theorem's statement is searched for counterexamples, small inputs first and then random ones, when its proof fails, and `stitchwort check --counterexamples` searches every theorem's ([syntax.md, Counterexamples to a theorem](../syntax.md#counterexamples-to-a-theorem)); property tests, `test` with parameters, are designed and come later ([counterexample-search.md](../proposals/counterexample-search.md)).

More: [syntax.md, Declarations](../syntax.md#declarations) (test failures), and [testing.md](../testing.md) (how the compiler itself is tested).
