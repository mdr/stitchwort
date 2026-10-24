-- Inferring a row variable's row (design C of
-- docs/proposals/effect-polymorphism.md, §5.C.1). `{e} b` is the plain `b`
-- when `e` is the empty row, so a pure use of an effect-polymorphic function
-- is pure code: its equations hold by `rfl` and its lemmas are the pure ones.
-- The row is the empty one only when the callback's type can never be a
-- computation; one that may yet become one waits, and a row nothing decides
-- is the empty one. One definition per row of the worked-examples table.
import Std (List, Eq, Vec, Text)

ability Log where
  say: Nat -> {Log} ()

-- Runs a computation that logs, collecting what it said.
def Log.collect (program: () -> {Log} a): Pair a (List Nat) :=
  handle program() with
    | return result => MkPair result []
    | Log.say n, k =>
      let rest := k ()
      MkPair rest.fst (Cons n rest.snd)

-- The pure use is `List.map`, by the same proofs as `List.map`'s own lemmas.
theorem mapInIsMap [a b: Type] (f: a -> b): (xs: List a) -> List.mapIn f xs = List.map f xs
  | Nil => rfl
  | Cons x xs => Eq.cong (Cons (f x)) (mapInIsMap f xs)

theorem lengthMapIn [a b: Type] (f: a -> b): (xs: List a) -> List.length (List.mapIn f xs) = List.length xs
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (lengthMapIn f xs)

theorem mapInCons [a b: Type] (f: a -> b) (x: a) (xs: List a):
    List.mapIn f (Cons x xs) = Cons (f x) (List.mapIn f xs) := rfl

-- A data type: `Nat`.
def lengths (words: List Text): List Nat := List.mapIn Text.length words

test "a callback returning a number" := lengths ["ab", "", "xyz"] == [2, 0, 3]

-- A type with a parameter: `List a`.
def singletons [a: Type] (xs: List a): List (List a) := List.mapIn (x => [x]) xs

test "a callback returning a list" := singletons [1, 2] == [[1], [2]]

-- A function type.
def adders (numbers: List Nat): List (Nat -> Nat) := List.mapIn (n => (m => n + m)) numbers

test "a callback returning functions" := List.map (add => add 1) (adders [1, 2]) == [2, 3]

-- A record.
type Point: Type = { x: Nat, y: Nat }

def onDiagonal (numbers: List Nat): List Point := List.mapIn (n => { x = n, y = n }) numbers

test "a callback returning records" := List.map (p => p.x + p.y) (onDiagonal [1, 2]) == [2, 4]

-- A result type not known yet where the callback is checked: settled later,
-- or defaulted.
def unannotated (numbers: List Nat): Nat :=
  let doubled := List.mapIn (n => n + n) numbers
  List.sum doubled

test "a callback whose result type is found later" := unannotated [1, 2] == 6

def unconstrained: Nat :=
  let unused := List.mapIn (x => x + 1)
  0

def sayAndDouble (n: Nat): {Log} Nat :=
  say n
  n + n

-- A type that computes to a computation only once an unknown is solved: the
-- row waits for it, and `map` becomes effectful in `Log`.
-- (`{Log} Nat` can't be written as a value of type `Type`: it's the result
-- type of `sayAndDouble`, below.)
def ResultOf [r: Type] (f: Nat -> r): Type := r

def Answer: Bool -> Type
  | True => ResultOf sayAndDouble
  | False => Nat

-- A number tagged with a flag, so that the flag is known from the list.
type Tagged (flag: Bool): Type =
  | Tag (n: Nat)

def answerOf: (flag: Bool) -> Nat -> Answer flag
  | True, n => sayAndDouble n
  | False, n => n

def Tagged.number [flag: Bool]: Tagged flag -> Nat
  | Tag n => n

def answer [flag: Bool] (tagged: Tagged flag): Answer flag := answerOf flag tagged.number

-- `answer`'s type is `Tagged ?flag -> Answer ?flag` when the callback is
-- checked; `?flag` is solved by the list, after it.
def logged (numbers: List (Tagged True)): {Log} (List Nat) := List.mapIn answer numbers

test "a callback whose type becomes a computation later" :=
  Log.collect (() => logged [Tag 3, Tag 4]) == MkPair [6, 8] [3, 4]

def notLogged (numbers: List (Tagged False)): List Nat := List.mapIn answer numbers

test "a callback whose type computes to a plain type later" := notLogged [Tag 3, Tag 4] == [3, 4]

-- The same callbacks eta-expanded: the body's type goes through the same
-- rule, so the row waits for `?flag` as it does for `answer` itself.
def loggedLambda (numbers: List (Tagged True)): {Log} (List Nat) := List.mapIn (tagged => answer tagged) numbers

test "an eta-expanded callback whose type becomes a computation later" :=
  Log.collect (() => loggedLambda [Tag 3, Tag 4]) == MkPair [6, 8] [3, 4]

def notLoggedLambda (numbers: List (Tagged False)): List Nat := List.mapIn (tagged => answer tagged) numbers

test "an eta-expanded callback whose type computes to a plain type later" :=
  notLoggedLambda [Tag 3, Tag 4] == [3, 4]

-- An effectful callback: the row is its row.
def sayAll (numbers: List Nat): {Log} (List Nat) := List.mapIn sayAndDouble numbers

test "an effectful callback" := Log.collect (() => sayAll [1, 2]) == MkPair [2, 4] [1, 2]

-- A dependent result type.
def applyIn (f: a -> {e} b) (x: a): {e} b := f x

def threeZeros: Vec Nat 3 := applyIn (n => Vec.replicate 3 n) 0

test "a dependent result type" := Vec.toList threeZeros == [0, 0, 0]

-- A type family stuck on a variable: nothing decides it, so it's pure.
def Cell: Bool -> Type
  | True => Nat
  | False => Text

def cellOf: (flag: Bool) -> Cell flag
  | True => 1
  | False => "one"

def cells (flags: List Bool): List Nat := List.mapIn (flag => if flag then 1 else 0) flags

def applyDep [p: a -> Type] (f: (x: a) -> {e} p x) (x: a): {e} p x := f x

def cellAt (flag: Bool): Cell flag := applyDep cellOf flag

test "a type family stuck on a variable" := cellAt True == 1

-- A callback that is itself effect-polymorphic: the rows are the same.
def mapTwice (f: Nat -> {e} Nat) (numbers: List Nat): {e} (List Nat) :=
  List.mapIn f (List.mapIn f numbers)

test "a row-polymorphic callback, pure" := mapTwice (n => n + 1) [1] == [3]

test "a row-polymorphic callback, effectful" :=
  Log.collect (() => mapTwice sayAndDouble [1]) == MkPair [4] [1, 2]
