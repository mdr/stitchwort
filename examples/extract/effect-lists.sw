-- The effect-polymorphic list functions with effectful callbacks
-- (docs/proposals/effect-polymorphic-list.md, D1239–D1241). Each callback
-- reports the element it is called on with `visit`, and `traced` collects
-- them, so each test pins down the order of the calls and where they stop:
-- - effects run in list order, first element first (`foldRight`'s run last
--   to first, as its definition reads);
-- - the callback is called at most once per element;
-- - `any`, `all`, `find`, `findMap`, `takeWhile` and `span` stop once the
--   answer is decided.
-- A `Fail` callback reports the first bad element. The `run:` lines compare
-- the backends with the reference evaluator.
--
-- run: filterOrder [1, 5, 2, 7]
-- run: filterOrder []
-- run: foldLeftOrder [1, 5, 2, 7]
-- run: foldRightOrder [1, 5, 2, 7]
-- run: sumByOrder [1, 5, 2, 7]
-- run: countOrder [1, 5, 2, 7]
-- run: anyOrder [1, 5, 2, 7]
-- run: anyOrder [1, 2]
-- run: allOrder [5, 6, 1, 7]
-- run: allOrder [5, 6]
-- run: findOrder [1, 5, 2, 7]
-- run: filterMapOrder [1, 5, 2, 7]
-- run: findMapOrder [1, 5, 2, 7]
-- run: findMapOrder [1, 2]
-- run: takeWhileOrder [7, 5, 1, 9]
-- run: flatMapOrder [1, 5, 2]
-- run: partitionOrder [1, 5, 2, 7]
-- run: spanOrder [7, 5, 1, 9]
-- run: filterFirstBad ["1", "x", "y"]
-- run: filterFirstBad ["1", "12", "3"]
-- run: partitionFirstBad ["1", "x", "y"]
-- run: countFirstBad ["1", "x", "y"]
-- run: allFirstBad ["1", "x", "y"]
import Std (List, Nat, Fail, Option, Result, Text)

ability Trace where
  visit: Nat → {Trace} ()

-- The callback's result, with the elements it was called on, in order.
def traced (prog: () → {Trace | e} a): {e} (a, List Nat) :=
  let run: List Nat → {e} (a, List Nat) :=
    handle prog() with
      | return result => seen => (result, seen)
      | visit x, resume => seen => resume () (seen ++ [x])
  run []

def big (x: Nat): {Trace} Bool :=
  visit x
  Nat.leq 5 x

def seen (x: Nat): {Trace} Nat :=
  visit x
  x

def addSeen (total: Nat) (x: Nat): {Trace} Nat :=
  visit x
  total + x

def pushSeen (x: Nat) (rest: List Nat): {Trace} (List Nat) :=
  visit x
  Cons x rest

def tenfoldIfBig (x: Nat): {Trace} (Option Nat) :=
  visit x
  if Nat.leq 5 x then Some (x * 10) else None

def twiceSeen (x: Nat): {Trace} (List Nat) :=
  visit x
  [x, x]

export def filterOrder (xs: List Nat): (List Nat, List Nat) := traced (() => List.filter xs big)

export def foldLeftOrder (xs: List Nat): (Nat, List Nat) := traced (() => List.foldLeft xs 0 addSeen)

export def foldRightOrder (xs: List Nat): (List Nat, List Nat) := traced (() => List.foldRight xs Nil pushSeen)

export def sumByOrder (xs: List Nat): (Nat, List Nat) := traced (() => List.sumBy xs seen)

export def countOrder (xs: List Nat): (Nat, List Nat) := traced (() => List.count xs big)

export def anyOrder (xs: List Nat): (Bool, List Nat) := traced (() => List.any xs big)

export def allOrder (xs: List Nat): (Bool, List Nat) := traced (() => List.all xs big)

export def findOrder (xs: List Nat): (Option Nat, List Nat) := traced (() => List.find xs big)

export def filterMapOrder (xs: List Nat): (List Nat, List Nat) := traced (() => List.filterMap xs tenfoldIfBig)

export def findMapOrder (xs: List Nat): (Option Nat, List Nat) := traced (() => List.findMap xs tenfoldIfBig)

export def takeWhileOrder (xs: List Nat): (List Nat, List Nat) := traced (() => List.takeWhile xs big)

export def flatMapOrder (xs: List Nat): (List Nat, List Nat) := traced (() => List.flatMap xs twiceSeen)

export def partitionOrder (xs: List Nat): ((List Nat, List Nat), List Nat) := traced (() => List.partition xs big)

export def spanOrder (xs: List Nat): ((List Nat, List Nat), List Nat) := traced (() => List.span xs big)

test "filter: in order, once each" := filterOrder [1, 5, 2, 7] == ([5, 7], [1, 5, 2, 7])
test "foldLeft: in order" := foldLeftOrder [1, 5, 2, 7] == (15, [1, 5, 2, 7])
test "foldRight: last to first" := foldRightOrder [1, 5, 2, 7] == ([1, 5, 2, 7], [7, 2, 5, 1])
test "sumBy: in order" := sumByOrder [1, 5, 2, 7] == (15, [1, 5, 2, 7])
test "count: in order" := countOrder [1, 5, 2, 7] == (2, [1, 5, 2, 7])
test "any: stops at the first yes" := anyOrder [1, 5, 2, 7] == (True, [1, 5])
test "any: all of them for no" := anyOrder [1, 2] == (False, [1, 2])
test "all: stops at the first no" := allOrder [5, 6, 1, 7] == (False, [5, 6, 1])
test "all: all of them for yes" := allOrder [5, 6] == (True, [5, 6])
test "find: stops at the element found" := findOrder [1, 5, 2, 7] == (Some 5, [1, 5])
test "filterMap: in order" := filterMapOrder [1, 5, 2, 7] == ([50, 70], [1, 5, 2, 7])
test "findMap: stops at the first Some" := findMapOrder [1, 5, 2, 7] == (Some 50, [1, 5])
test "findMap: all of them for None" := findMapOrder [1, 2] == (None, [1, 2])
test "takeWhile: stops at the first no" := takeWhileOrder [7, 5, 1, 9] == ([7, 5], [7, 5, 1])
test "flatMap: in order" := flatMapOrder [1, 5, 2] == ([1, 1, 5, 5, 2, 2], [1, 5, 2])
test "partition: one pass, in order" := partitionOrder [1, 5, 2, 7] == (([5, 7], [1, 2]), [1, 5, 2, 7])
test "span: one pass, stops at the first no" := spanOrder [7, 5, 1, 9] == (([7, 5], [1, 9]), [7, 5, 1])

-- A `Fail` callback: the first element that isn't a number is reported.
def isSmall (text: Text): {Fail} Bool :=
  let n := Fail.need text.toNat "not a number: ${text}"
  Nat.leq n 9

export def filterFirstBad (texts: List Text): Result (List Text) Text := Fail.toResult (() => List.filter texts isSmall)

export def partitionFirstBad (texts: List Text): Result (List Text, List Text) Text := Fail.toResult (() => List.partition texts isSmall)

export def countFirstBad (texts: List Text): Result Nat Text := Fail.toResult (() => List.count texts isSmall)

export def allFirstBad (texts: List Text): Result Bool Text := Fail.toResult (() => List.all texts isSmall)

test "filter: the first bad element" := filterFirstBad ["1", "x", "y"] == Err "not a number: x"
test "filter: all good" := filterFirstBad ["1", "12", "3"] == Ok ["1", "3"]
test "partition: the first bad element" := partitionFirstBad ["1", "x", "y"] == Err "not a number: x"
test "count: the first bad element" := countFirstBad ["1", "x", "y"] == Err "not a number: x"
test "all: the first bad element" := allFirstBad ["1", "x", "y"] == Err "not a number: x"

-- Pure copies of the functions as they were before their callbacks took
-- effects. Each function's empty-row variant compiles to the same loop as
-- its copy (`list_functions_at_the_empty_row_are_their_pure_loops` in
-- crates/cli/tests/extract.rs).
def pureFilter: List a → (p: a → Bool) → List a
  | Nil, p => Nil
  | Cons x xs, p => List.filterStep x (pureFilter xs p) (p x)

def pureFoldLeft: List a → (initial: b) → (f: b → a → b) → b
  | Nil, initial, f => initial
  | Cons x xs, initial, f => pureFoldLeft xs (f initial x) f

def pureAny: List a → (p: a → Bool) → Bool
  | Nil, p => False
  | Cons x xs, p => if p x then True else pureAny xs p

def pureAll: List a → (p: a → Bool) → Bool
  | Nil, p => True
  | Cons x xs, p => if p x then pureAll xs p else False

def pureFind: List a → (p: a → Bool) → Option a
  | Nil, p => None
  | Cons x xs, p => if p x then Some x else pureFind xs p

def pureFilterMap: List a → (f: a → Option b) → List b
  | Nil, f => Nil
  | Cons x xs, f => List.consSome (f x) (pureFilterMap xs f)

def pureFindMap (xs: List a) (f: a → Option b): Option b :=
  match xs with
    | Nil => None
    | Cons x ys => Option.orElse (f x) (pureFindMap ys f)

def pureTakeWhile (xs: List a) (p: a → Bool): List a :=
  match xs with
    | Nil => Nil
    | Cons x ys => if p x then Cons x (pureTakeWhile ys p) else Nil

def isBig (x: Nat): Bool := Nat.leq 5 x

def tenfold (x: Nat): Option Nat := if Nat.leq 5 x then Some (x * 10) else None

def add (total: Nat) (x: Nat): Nat := total + x

-- Each function and its copy, used purely: the two must agree.
export def filtered (xs: List Nat): (List Nat, List Nat) := (List.filter xs isBig, pureFilter xs isBig)

export def folded (xs: List Nat): (Nat, Nat) := (List.foldLeft xs 0 add, pureFoldLeft xs 0 add)

export def anyAll (xs: List Nat): (Bool, Bool, Bool, Bool) := (List.any xs isBig, pureAny xs isBig, List.all xs isBig, pureAll xs isBig)

export def found (xs: List Nat): (Option Nat, Option Nat) := (List.find xs isBig, pureFind xs isBig)

export def filterMapped (xs: List Nat): (List Nat, List Nat) := (List.filterMap xs tenfold, pureFilterMap xs tenfold)

export def foundMap (xs: List Nat): (Option Nat, Option Nat) := (List.findMap xs tenfold, pureFindMap xs tenfold)

export def prefix (xs: List Nat): (List Nat, List Nat) := (List.takeWhile xs isBig, pureTakeWhile xs isBig)
