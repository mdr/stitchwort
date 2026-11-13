# 6. Namespaces, projects and the library

## Namespaces and imports

Names live in namespaces. The standard library's root is `Std`, and each type has a namespace of its own holding its constructors and the functions about it: `List.map`, `Text.split`, `Shape.area`.

A small set of names is always in scope (the **prelude**): the basic types (`Nat`, `Int`, `Bool`, `Char`, `Text`, `List`, `Option`, `Result`, `Ordering`, tuples and `()`), their constructors, the interfaces behind the operators, `IO` and its operations, and `not`. The rest of a library namespace needs an import, and the error says which:

<!-- snippet: errors/import.sw -->
```stitchwort
def numbers (line: Text): List Nat := line.split ',' |> .filterMap Text.toNat
```

<!-- output: check errors/import.sw -->
```text
[E-UNKNOWN-NAME] Error: unknown name `Text.toNat`
   ╭─[ errors/import.sw:1:68 ]
   │
 1 │ def numbers (line: Text): List Nat := line.split ',' |> .filterMap Text.toNat
   │                                                                    ─────┬────
   │                                                                         ╰────── not in scope
   │
   │ Note 1: `Text.toNat` needs `import Std (Text)`, or write it in full: `Std.Text.toNat`
   │
   │ Note 2: the prelude's `Text` comes with its own constructors, fields and operations; the functions and theorems in its namespace need the import
───╯
1 error: in `numbers`
```

`import Std (List, Text)` at the top of a file makes `List.…` and `Text.…` usable. Some things need no import:

- **Dot notation and pipes.** In `line.split ','` the value's type picks the namespace, so `Text.split` is found without an import. Most code is written this way.
- **Full names.** `Std.Text.toNat` always works.
- **Syntax.** `+`, `==`, `++`, `if`, literals and `${…}` always mean the library's.

`import N (a, b)` brings particular names into scope: `import Std.Fail (fail, need)` lets you write `fail` for `Fail.fail`. A constructor may be named too: beside its type, `import Turns (Move, Clockwise)`, it adds nothing, since importing the type already brings its constructors; alone, `import Turns (Counterclockwise)`, it imports just that constructor, and neither the type nor the type's other constructors. `import N (..)` brings every name declared directly in `N`, at a lower priority than the file's own names and named imports. Types outside the prelude, such as `Map`, `Set`, `Vec`, `Array` and `Float`, need an import even for the type's name.

A short name means, first found: a local variable, the file's own declaration, a name imported by name, a name from an `(..)` import, the prelude. So a file can declare its own `length` or `Option` without a clash.

## A project

The example project in [examples/project/](examples/project/) is a small shop: it reads orders and prints a bill. Its `stitchwort.yaml` is one line:

<!-- snippet: project/stitchwort.yaml -->
```yaml
sources: [src]
```

`sources` lists the folders to read; every `.sw` file under them belongs to the project. An empty file means `sources: [src]`.

The namespace `Shop` is spread over two files. The first declares the model:

<!-- snippet: project/src/Shop/Shop.sw -->
```stitchwort
-- The shop's model: products, prices and orders.
namespace Shop
import Std (List, Map, Nat, Text)

type Product = { name: Text, pence: Nat }

type Order = { product: Text, quantity: Nat }

def catalogue: Map Text Product := Map.fromList [
  ("tea", { name = "tea", pence = 250 }),
  ("milk", { name = "milk", pence = 90 }),
  ("biscuits", { name = "biscuits", pence = 120 })
]

-- The price of an order, or `None` for a product the shop doesn't sell.
def Order.price (order: Order): Option Nat := catalogue.get order.product |> .map (product => product.pence * order.quantity)

-- Orders of the same product, added up, in the product's name order.
def combine (orders: List Order): Map Text Nat :=
  orders.foldLeft Map.empty (totals order => totals.insertWith order.product order.quantity (a b => a + b))
```

The second adds a function to read an order from a line of text. It sees `Order` without an import, because it is in the same namespace, but it has its own imports:

<!-- snippet: project/src/Shop/Parse.sw -->
```stitchwort
-- Reading orders: a second file of the namespace `Shop`. It sees `Order`
-- without an import, but has its own imports.
namespace Shop
import Std (Fail, List, Text)
import Std.Fail (fail, need)

-- "tea 3" is three teas.
def Order.read (line: Text): {Fail} Order := match line.words with
  | [product, quantity] => { product, quantity = need quantity.toNat "expected a quantity, got '${quantity}'" }
  | _ => fail "expected a product and a quantity, got '${line}'"
```

The program is a namespace of its own, `Shop.Report`. A dotted namespace doesn't see its parent's names: it imports what it uses.

<!-- snippet: project/src/Shop/Report.sw -->
```stitchwort
-- The program: read orders, one per line, and print a bill.
namespace Shop.Report
import Shop (Order, combine)
import Std (Fail, IO, List, Map)

def main(): {IO, Fail} () :=
  let orders := IO.readAllLines().map Order.read
  let totals := combine orders
  totals.toList.map printTotal
  IO.print "Total: ${bill orders} pence"

def printTotal (item: (Text, Nat)): {IO} () :=
  let (product, quantity) := item
  IO.print "${quantity} x ${product}"

def bill (orders: List Order): Nat := orders.filterMap .price |> .sum
```

<!-- output: run --project project Shop.Report.main < project/orders.txt -->
```text
4 x biscuits
2 x milk
4 x tea
Total: 1660 pence
```

The tests are in `Shop.Tests`, so running the program never checks them, and `stitchwort test` runs them:

<!-- snippet: project/src/Shop/Tests/Tests.sw -->
```stitchwort
-- The shop's tests, in a namespace of their own so that running the program
-- doesn't check them.
namespace Shop.Tests
import Shop (..)
import Shop.Report (bill)
import Std (Fail, Map)

def read (line: Text): Result Order Text := Fail.toResult (() => Order.read line)

test "reads an order" := read "tea 3" == Ok { product = "tea", quantity = 3 }
test "refuses a bad quantity" := read "tea lots" == Err "expected a quantity, got 'lots'"
test "prices an order" := ({ product = "milk", quantity = 2 }: Order).price == Some 180
test "an unknown product has no price" := ({ product = "cake", quantity = 1 }: Order).price == None
test "combines orders" := (combine [{ product = "tea", quantity = 1 }, { product = "tea", quantity = 2 }]).get "tea" == Some 3
test "bills only what it sells" := bill [{ product = "tea", quantity = 2 }, { product = "cake", quantity = 9 }] == 500
```

<!-- output: test --project project -->
```text
Shop.Tests
  ✓ reads an order                   ran
  ✓ refuses a bad quantity           ran
  ✓ prices an order                  ran
  ✓ an unknown product has no price  ran
  ✓ combines orders                  ran
  ✓ bills only what it sells         ran
6 test(s): 6 passed, 0 failed (0 from the cache)
```

The rules, in brief (the full set is in [projects.md](../projects.md)):

- Every file starts with `namespace N`; only comments may come before it.
- All files of a namespace see each other's declarations, in any order. Imports are per file.
- A namespace uses another by importing from it or writing a full name. Namespaces can't depend on each other in a cycle; definitions within one namespace can.
- `Std`, the library's namespaces (`List`, `Text`, …) and `Main` are reserved as namespace names.
- There is no `private`: anything can be named from anywhere.
- A namespace may add functions to another namespace's type: in `Shop.Tests`, `def Order.isLarge (order: Order): Bool := order.quantity > 10` is `Shop.Tests.Order.isLarge`. `order.isLarge` finds it in `Shop.Tests` and in files that `import Shop.Tests (..)`, nowhere else. The library's types can't be added to.
- Files and folders mean nothing to the compiler. The convention, followed by `aoc/`, is a folder per namespace: `Aoc.Year2025.Day01` in `src/Aoc/Year2025/Day01/`, with `Aoc.Year2025.Day01.Tests` and `Aoc.Year2025.Day01.Proofs` in subfolders.

## The standard library

The library's source is in `crates/elab/src/std/`, and `stitchwort std-source List/Toolkit.sw` prints a file; in the editor, go to definition opens it. To find out what a function does without reading its file, `stitchwort doc List.filterMap` prints its header, the comment above it, the tests and theorems named after it as examples, and the theorems about it; `stitchwort doc List` lists what a namespace declares, with a line on each (`--theorems 0` skips the check, for an instant answer). A few conventions run through it:

- The main argument comes first, then the other arguments, then any function arguments: `List.map xs f`, `Text.split line ','`, `Map.get map key`, `xs.foldLeft 0 (total n => total + n)`. Dot notation and pipes put the value there (`xs.map f`, `xs |> .map f`), and a function ending in a lambda suits a lambda that spans lines. A function with two arguments of the same type is named so that the dot reads as a sentence: `t.startsWith p`, `a.sub b`, `xs.append ys`.
- Functions are total. Where an answer may not exist, the result is an `Option` (`List.maximum`, `Text.toNat`, `Map.get`), or the function takes a default (`getOrElse`, `List.headOr`).
- Most functions come with theorems about them, named after what they say (`List.lengthMap`, `Nat.addComm`), for use in proofs.

### Lists

<!-- snippet: library.sw#lists -->
```stitchwort
def scores: List Nat := [7, 3, 9, 3, 5]

test "map and filter" := (scores.filter (n => n > 4)).map (n => n * 10) == [70, 90, 50]
test "folds" := scores.foldLeft 0 (total n => total + n) == scores.sum
test "searching" := scores.find (n => n > 7) == Some 9 ∧ scores.findIndex (n => n == 9) == Some 2
test "sorting and dedup" := scores.sort.dedup == [3, 5, 7, 9]
test "slicing" := scores.take 2 == [7, 3] ∧ scores.drop 3 == [3, 5]
test "zipping" := List.zipWith [1, 2, 3] [4, 5, 6] (a b => a * b) == [4, 10, 18]
test "ranges" := 0 ..< 4 == [0, 1, 2, 3] ∧ 2 ..= 5 == [2, 3, 4, 5]
test "with an index" := ["a", "b"].withIndex == [(0, "a"), (1, "b")]
test "maximum of an empty list" := ([]: List Nat).maximum == None
```

Others worth knowing: `count`, `all`, `any`, `flatMap`, `concatMap`, `scanLeft`, `partition`, `span`, `takeWhile`, `dropWhile`, `chunksOf`, `windows` (sliding windows), `transpose`, `reverse`, `sortOn`, `sortBy`, `maxBy`, `minBy`, `occurrences`, `getOr`, `replicate`, `maximumOf` and `minimumOf` (the largest and smallest value of a function over the list), `findMap` (the first `Some` a function gives) and `somes` (the values inside the `Some`s). `Option.flatten` joins two layers of `Option`, and `uncurry` turns a function of two arguments into one of a pair. `map`'s function may also perform abilities ([chapter 8](08-abilities.md)).

### Ranges

`a ..< b` is the numbers from `a` up to, not including, `b`, and `a ..= b` is the numbers from `a` through `b`. Both are written with spaces. A range is an ordinary list of `Nat`s (the call `List.range a b`), so everything above works on it, and an end below the start gives `[]`.

<!-- snippet: library.sw#ranges -->
```stitchwort
def squares (n: Nat): List Nat := 0 ..< n |> .map (i => i * i)

test "up to, not including" := 0 ..< 3 == [0, 1, 2]
test "through" := 1 ..= 3 == [1, 2, 3]
test "nothing when the end is below the start" := 5 ..< 2 == []
test "mapping over a range" := squares 4 == [0, 1, 4, 9]
test "range membership" := 3 in 0 ..< 5 ∧ 5 !in 0 ..< 5
test "in a spread" := [0, ..2 ..< 5, 9] == [0, 2, 3, 4, 9]
test "each number of a range" := Each.collect (() => each (1 ..= 3) * 10) == [10, 20, 30]

theorem inRange (x n: Nat) (h: x < n): x ∈ 0 ..< n := omega

theorem upTo (x n: Nat) (h: x ∈ 0 ..< n): x < n := omega
```

`0 ..< n` is the usual way to count `n` things from zero, and `1 ..= n` the way to say "1 to n". The end can be any expression (`0 ..< xs.length`), but a range binds more loosely than `++` and `+`, and more tightly than `==`, `in` and `|>`: `x in 0 ..< n` is `x in (0 ..< n)`, and `0 ..< n |> .map f` is `(0 ..< n) |> .map f`. A method on a range needs brackets, `(0 ..< n).length`, since a dot binds tighter; the pipe reads better. In a spread a range needs no brackets, `[0, ..2 ..< 5, 9]`.

In a proof, `omega` and `auto` read `x ∈ a ..< b` (and `..=`) as the two bounds `a ≤ x` and `x < b`, and prove such a membership from them, as the two theorems above do. `List.memRange` says the same as a lemma, `x ∈ a ..< b ↔ a ≤ x < b`, and `List.lengthRange` gives the length. As a `Bool`, `x in a ..< b` is two comparisons, however long the range (`List.inRange`; `List.inRangeIff` and `List.containsRange` tie it to the membership and to `contains`). A range is never written in brackets: `[0 ..< n]` is a list holding one list, which is almost never meant, so it gets the warning `W-RANGE-IN-BRACKETS` (write `[(0 ..< n)]` if the nesting is). `[2..n]`, as in Haskell, is a syntax error that says to write `2 ..= n` for a range or `[2, ..n]` for a spread. Only `Nat` ranges exist so far.

### Option and Result

<!-- snippet: library.sw#option -->
```stitchwort
def lookupAge (name: Text): Option Nat :=
  if name == "Ada" then Some 36 else None

test "map" := (lookupAge "Ada").map (age => age + 1) == Some 37
test "getOrElse" := (lookupAge "Bob").getOrElse 0 == 0
test "flatMap" := (lookupAge "Ada").flatMap (age => if age > 18 then Some "adult" else None) == Some "adult"
test "filterMap" := ["1", "x", "3"].filterMap Text.toNat == [1, 3]
```

<!-- snippet: library.sw#result -->
```stitchwort
def parseAge (text: Text): Result Nat Text := match text.toNat with
  | Some age => Ok age
  | None => Err "not a number: '${text}'"

test "ok" := parseAge "36" == Ok 36
test "err" := parseAge "old" == Err "not a number: 'old'"
test "map over Ok" := (parseAge "36").map (age => age * 2) == Ok 72
test "traverse stops at the first Err" := Result.traverse ["1", "x", "y"] parseAge == Err "not a number: 'x'"
```

### Text

`Text` functions count Unicode characters, not bytes or UTF-16 units:

<!-- snippet: library.sw#text -->
```stitchwort
test "split and join" := Text.join ("a,b,c".split ',') '-' == "a-b-c"
test "words and lines" := "two  words".words == ["two", "words"] ∧ "a\nb\n".lines == ["a", "b"]
test "numbers" := "42".toNat == Some 42 ∧ "-7".toInt == Some (-7)
test "toNat does not trim" := " 42 ".toNat == None ∧ " 42 ".trim.toNat == Some 42
test "trim and slices" := "  tea ".trim == "tea" ∧ "teapot".take 3 == "tea"
test "prefixes" := "L68".stripPrefix "L" == Some "68"
test "length counts characters" := "héllo".length == 5
```

Note that `Text.toNat` and `Text.toInt` don't trim spaces, while `Text.toNatOrFail` and `Text.toIntOrFail` do ([chapter 8](08-abilities.md)).

### Map and Set

`Map k v` is a map ordered by its keys, which need an `Ord` instance (every declared type has one). `Set k` is the same without values. Both print, compare and convert to lists in key order, and two maps with the same entries are equal, however they were built. `pairs.toMap` and `xs.toSet` build a map or set from a list, and `sets.unionAll` unions a list of sets:

<!-- snippet: library.sw#map -->
```stitchwort
def wordCounts (words: List Text): Map Text Nat :=
  words.foldLeft Map.empty (counts word => counts.insertWith word 1 (a b => a + b))

test "counts" := (wordCounts ["a", "b", "a"]).get "a" == Some 2
test "missing key" := (wordCounts ["a"]).get "z" == None
test "in key order" := (wordCounts ["b", "a", "b"]).toList == [("a", 1), ("b", 2)]
test "group by" := (["tea", "milk", "pot"].groupBy (word => word.length)).get 3 |> .map (group => group.toList) == Some ["tea", "pot"]
test "from pairs" := [(2, "b"), (1, "a")].toMap == Map.fromList [(1, "a"), (2, "b")]
test "equal however built" := Map.fromList [(1, "a"), (2, "b")] == Map.fromList [(2, "b"), (1, "a")]
```

<!-- snippet: library.sw#set -->
```stitchwort
def seen: Set Nat := [3, 1, 3, 2].toSet
def sets: List (Set Nat) := [[1, 2].toSet, [2, 3].toSet]

test "duplicates go" := seen.size == 3 ∧ seen.toList == [1, 2, 3]
test "membership" := seen.contains 2 ∧ ¬(seen.contains 5)
test "set algebra" := Set.union seen [9].toSet == [1, 2, 3, 9].toSet
test "union a list of sets" := sets.unionAll == [1, 2, 3].toSet
```

### Array

Reach for an `Array a` when a program keeps **indexed state and updates it in a loop**: a table of counters, a board of cells, the numbers a game has said so far. A list reads and changes position `i` in `i` steps, so a loop over a million positions is quadratic; an array does either in one step. When you only walk a collection from one end to the other, or build it once and read it, a `List` is simpler and as fast.

An array is not in the prelude: write `import Std (Array)`. Building one from a list with `.toArray` (a dot call, as ever) needs no import.

<!-- snippet: library.sw#array -->
```stitchwort
def tally (digits: List Nat): Array Nat :=
  digits.foldLeft (Array.replicate (count := 10) 0) (counts digit => counts.modify digit (n => n + 1))

test "an array of counts" := (tally [3, 1, 3, 3]).toList == [0, 1, 0, 3, 0, 0, 0, 0, 0, 0]
test "get gives an Option" := (tally [3]).get 3 == Some 1 ∧ (tally [3]).get 10 == None
test "getOr gives a fallback" := (tally [3]).getOr 12 0 == 0
test "set out of range changes nothing" := ([5, 6].toArray).set 2 9 == [5, 6].toArray

test "getLt needs no Option when the index is in range" := ([7, 8, 9].toArray).getLt 1 == 8
```

Nothing panics. `get array i` is an `Option`, `None` past the end; `getOr array i fallback` takes the answer for that case; and `getLt array i` takes a proof that `i < array.size`, found by `auto` where the compiler can see it (as for a literal array above, or after a check such as `if i < array.size`), so the result needs no `Option` at all. `set array i x` past the end leaves the array unchanged, as `List.set` does, and so do `modify` and `swap`. The rest: `size`, `push`, `pop`, `replicate`, `tabulate`, `map`, `foldLeft`, `withIndex`, `toList` and `toVec`. Two arrays are equal when their lists are, and `toList` is what a proof sees: an array *is* its list, so every list lemma applies, and the proofs about a program that uses arrays are the proofs about the lists it would have used.

**In place.** `set`, `push`, `pop` and `modify` take the array and give back a new one, but when nothing else holds the old one, `stitchwort run` (and `--native`, and the playground) changes the same buffer instead of copying it. That is what makes the loop above linear. It only works while you pass the new array on and don't use the old one again. If you do (the old array is kept in a variable you read later, a `Map`, a closure), the first change must copy it first: the answer is still right, but that step takes time in proportion to the array's size, which brings back the cost you used an array to avoid. Under `--js` every operation runs as written, on the list, so it is correct but slow.

A run that makes many large copies says so when it ends:

```
note: an array was copied 4000 times because something else still held it (the largest had 5000 elements); `set`, `push` and `pop` change an array in place only when nothing else holds it, so keep one version in use and pass it on (docs/proposals/arrays.md §6.1)
```

It appears after ten copies of a thousand elements or more. It means some loop is holding on to an old version of the array: look for a place that uses the array both before and after a `set`, such as comparing the new array with the old one, or a step that returns a pair containing both. The note never appears for an array that is changed in place, and a short array never triggers it.

### NonEmptyList

Many lists can't be empty: the people in a group, the numbers on a line. A `NonEmptyList a` is a record of a first element and the rest, `{ head = 3, tail = [9, 4] }`, written `[3, 9, 4]` where the type says it is a `NonEmptyList`, so the functions that need a first element can't fail. `maximum`, `minimum`, `maxBy`, `minBy`, `last` and `reduce` (a fold that starts from the first element) return the value itself where `List`'s return an `Option`, and `map`, `zip`, `sort`, `reverse` and `append` return a `NonEmptyList` again. `xs.toList` goes back to a `List`. To go forward, `xs.toNonEmpty` takes a list the compiler can see isn't empty (a proof `xs ≠ []`, found by `auto`), and `xs.nonEmpty` gives an `Option (NonEmptyList a)`. In a pattern, `[first, ..rest]` takes one apart (`rest` is a `List`) and covers every value, so a match needs no `[]` arm; `[]` itself is an error where a `NonEmptyList` is expected. Where nothing says the type, brackets make a `List`. `++` is for `List` and `Text`, so the joins are `append`, `appendList` and `prependList`. The library returns one wherever a list can't be empty: the parsers `Parse.many1`, `sepBy1`, `lines`, `sections`, `section` and `grid`, each group of `List.splitBy` and of `Map.groupBy`, and `Nat.digits`. Write `.toList` where a plain list is wanted.


<!-- snippet: library.sw#nonempty -->
```stitchwort
def groupAnswers: NonEmptyList (Set Char) := [['a', 'b', 'c'].toSet, ['b', 'c'].toSet, ['c', 'd'].toSet]
def numbers: NonEmptyList Nat := [3, 9, 4]

def describe: NonEmptyList Nat → Text
  | [only] => "just ${only}"
  | [first, ..rest] => "${first} and ${rest.length} more"

test "no Option" := groupAnswers.intersectAll == ['c'].toSet
test "reduce and maximum" := numbers.maximum == 9 ∧ numbers.reduce Nat.add == 16
test "map keeps it non-empty" := (numbers.map (n => n * 10)).head == 30
test "no [] arm" := describe [7] == "just 7" ∧ describe numbers == "3 and 2 more"
test "from a list" := [4, 5, 6].toNonEmpty.maximum == 6 ∧ ([]: List Nat).nonEmpty == None
```

### Vec

`Vec a n` is a list whose length `n` is part of its type. Functions that need a non-empty vector, or two of the same length, say so in their types, so `head` needs no `Option`:

<!-- snippet: library.sw#vec -->
```stitchwort
def row: Vec Nat 3 := VCons 4 (VCons 5 (VCons 6 VNil))

test "a Vec knows its length" := row.toList == [4, 5, 6]
test "head needs no Option" := row.head == 4
test "zipWith needs equal lengths" := (Vec.zipWith row row (a b => a + b)).toList == [8, 10, 12]
```

[Chapter 10](10-proofs.md) has more on types that mention values. The library also has `Fin n` (positions below `n`), `Mod n` (wrap-around arithmetic), `Float`, `Each` (search, [chapter 8](08-abilities.md)), `Parse` (parsing text into your own types, also chapter 8), `Graph` (shortest paths: Dijkstra's `Graph.distances` and breadth-first `Graph.breadthFirst`, both proved; `Graph.fromEdges` builds a graph with nothing to prove, and `Graph.reachable` gives the set of states reachable from some sources; for states that can be numbered densely, such as a grid's positions row by row, `graph.distances (index := …) sources` keeps the search's costs in arrays rather than maps, about twice as fast, with a `Graph.Index` that numbers them and proves two facts about its numbers) and `Nat.partitionPoint` (binary search for where a test starts failing, as Rust's `partition_point`).
