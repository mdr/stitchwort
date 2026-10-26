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
```

`import Std (List, Text)` at the top of a file makes `List.…` and `Text.…` usable. Some things need no import:

- **Dot notation and pipes.** In `line.split ','` the value's type picks the namespace, so `Text.split` is found without an import. Most code is written this way.
- **Full names.** `Std.Text.toNat` always works.
- **Syntax.** `+`, `==`, `++`, `if`, literals and `${…}` always mean the library's.

`import N (a, b)` brings particular names into scope: `import Std.Fail (fail, need)` lets you write `fail` for `Fail.fail`. `import N (..)` brings every name declared directly in `N`, at a lower priority than the file's own names and named imports. Types outside the prelude, such as `Map`, `Set`, `Vec` and `Float`, need an import even for the type's name.

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
def Order.read (line: Text): {Fail} Order :=
  match line.words with
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

def bill (orders: List Order): Nat := orders.filterMap (.price) |> .sum
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

test "reads an order" := read "tea 3" == Ok ({ product = "tea", quantity = 3 })
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
- Files and folders mean nothing to the compiler. The convention, followed by `aoc/`, is a folder per namespace: `Aoc.Day01` in `src/Aoc/Day01/`, with `Aoc.Day01.Tests` and `Aoc.Day01.Proofs` in subfolders.

## The standard library

The library's source is in `crates/elab/src/std/`, and `stitchwort std-source List/Toolkit.sw` prints a file; in the editor, go to definition opens it. A few conventions run through it:

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
test "ranges" := List.range 4 == [0, 1, 2, 3] ∧ List.between 2 5 == [2, 3, 4, 5]
test "with an index" := ["a", "b"].withIndex == [(0, "a"), (1, "b")]
test "maximum of an empty list" := ([]: List Nat).maximum == None
```

Others worth knowing: `count`, `all`, `any`, `flatMap`, `concatMap`, `scanLeft`, `partition`, `span`, `takeWhile`, `dropWhile`, `chunksOf`, `transpose`, `reverse`, `sortOn`, `sortBy`, `maxBy`, `minBy`, `occurrences`, `getOr` and `replicate`. `map`'s function may also perform abilities ([chapter 8](08-abilities.md)).

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
def parseAge (text: Text): Result Nat Text :=
  match text.toNat with
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

`Map k v` is a map ordered by its keys, which need an `Ord` instance (every declared type has one). `Set k` is the same without values. Both print, compare and convert to lists in key order, and two maps with the same entries are equal, however they were built:

<!-- snippet: library.sw#map -->
```stitchwort
def wordCounts (words: List Text): Map Text Nat :=
  words.foldLeft Map.empty (counts word => counts.insertWith word 1 (a b => a + b))

test "counts" := (wordCounts ["a", "b", "a"]).get "a" == Some 2
test "missing key" := (wordCounts ["a"]).get "z" == None
test "in key order" := (wordCounts ["b", "a", "b"]).toList == [("a", 1), ("b", 2)]
test "group by" := (Map.groupBy ["tea", "milk", "pot"] (word => word.length)).get 3 == Some ["tea", "pot"]
test "equal however built" := Map.fromList [(1, "a"), (2, "b")] == Map.fromList [(2, "b"), (1, "a")]
```

<!-- snippet: library.sw#set -->
```stitchwort
def seen: Set Nat := Set.fromList [3, 1, 3, 2]

test "duplicates go" := seen.size == 3 ∧ seen.toList == [1, 2, 3]
test "membership" := seen.contains 2 ∧ ¬(seen.contains 5)
test "set algebra" := Set.union seen (Set.fromList [9]) == Set.fromList [1, 2, 3, 9]
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

[Chapter 10](10-proofs.md) has more on types that mention values. The library also has `Fin n` (positions below `n`), `Mod n` (wrap-around arithmetic), `Float`, `Each` (search, [chapter 8](08-abilities.md)) and `PrefixSums`.
