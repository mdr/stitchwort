-- Chapter 8: abilities and handlers.
import Std (Abort, Each, Fail, IO, List, Nat, Option, Parse, Result, Text)
import Std.Effect (Effects)
import Std.Fail (fail, need, ensure, toResult)
import Std.Parse (char, nat)

-- begin declare
ability Log where
  say: Text → {Log} ()

def checkout (items: Nat): {Log} Nat :=
  say "checking out ${items} items"
  let price := items * 5
  say "the price is ${price}"
  price
-- end declare

-- begin handle
def collectLog (prog: () → {Log | e} a): {e} (a, List Text) :=
  let run: List Text → {e} (a, List Text) :=
    handle prog() with
      | return result => said => (result, said)
      | say message, resume => said => resume () (said ++ [message])
  run []

test "collected" := collectLog (() => checkout 3) == (15, ["checking out 3 items", "the price is 15"])
-- end handle

-- begin ignore
def quietly (prog: () → {Log | e} a): {e} a :=
  handle prog() with
    | return result => result
    | say _, resume => resume ()

test "ignored" := quietly (() => checkout 2) == 10
-- end ignore

-- begin print
def printLog (prog: () → {Log, IO | e} a): {IO | e} a :=
  handle prog() with
    | return result => result
    | say message, resume =>
      IO.print "log: ${message}"
      resume ()

def main(): {IO} () :=
  let price := printLog (() => checkout 4)
  IO.print "total: ${price}"
-- end print

-- begin state
ability Counter where
  next: () → {Counter} Nat

def label (names: List Text): {Counter} (List Text) := names.map (name => "${next()}. ${name}")

def counting (start: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => count => resume count (count + 1)
  run start

test "numbered" := counting 1 (() => label ["tea", "milk"]) == ["1. tea", "2. milk"]
-- end state

-- begin polymorphic
def applyTwice (f: a → {e} a) (x: a): {e} a := f (f x)

test "pure" := applyTwice (n => n + 1) 0 == 2
def loggedStep (n: Nat): {Log} Nat :=
  say "at ${n}"
  n + 1

test "with an ability" := collectLog (() => applyTwice loggedStep 0) == (2, ["at 0", "at 1"])
-- end polymorphic

-- begin fail
type Turn = { left: Bool, distance: Nat }

def Turn.parse (text: Text): {Fail} Turn :=
  let (direction, rest) := need text.uncons "expected a turn, got nothing"
  ensure (direction == 'L' ∨ direction == 'R') "expected L or R, got '${text}'"
  { left = direction == 'L', distance = rest.toNatOrFail }

def parseTurns (lines: List Text): {Fail} (List Turn) := lines.map Turn.parse

test "a turn" := toResult (() => Turn.parse "L68") == Ok ({ left = True, distance = 68 })
test "a bad turn" := toResult (() => parseTurns ["L1", "X2"]) == Err "expected L or R, got 'X2'"
test "context" := toResult (() => Fail.context "line 2" (() => Turn.parse "R")) == Err "line 2: expected a whole number, got ''"
-- end fail

-- begin abort
def halfOf (n: Nat): {Abort} Nat :=
  Abort.ensure (n % 2 == 0)
  n / 2

test "abort" := Abort.toOption (() => halfOf 6) == Some 3 ∧ Abort.toOption (() => halfOf 7) == None
-- end abort

-- begin each
def triples (n: Nat): List (Nat, Nat, Nat) := Each.collect (() =>
  let a := Each.each (List.between 1 n)
  let b := Each.each (List.between a n)
  let c := Each.each (List.between b n)
  Each.require (a * a + b * b == c * c)
  (a, b, c))

test "pythagorean triples" := triples 13 == [(3, 4, 5), (5, 12, 13), (6, 8, 10)]
-- end each

-- begin parse
type Box = { x: Nat, y: Nat, z: Nat }

def box(): {Parse} Box :=
  let x := nat()
  char ','
  let y := nat()
  char ','
  let z := nat()
  { x, y, z }

def parseBoxes (input: Text): {Fail} (List Box) := Parse.eachLine input box

test "boxes" := toResult (() => parseBoxes "162,817,812\n57,618,57\n") == Ok [{ x = 162, y = 817, z = 812 }, { x = 57, y = 618, z = 57 }]
test "a bad box" := toResult (() => parseBoxes "162,817,812\n57,6x8,57\n") == Err "line 2, column 5: expected ','"
-- end parse

-- begin effects-parameter
type Hooks (e: Effects) = {
  before: Nat → {e} (),
  after: Nat → {e} ()
}

def withHooks (hooks: Hooks e) (step: Nat → Nat) (n: Nat): {e} Nat :=
  hooks.before n
  let result := step n
  hooks.after result
  result

def doubled (n: Nat): {Log} Nat :=
  withHooks { before = m => say "before ${m}", after = m => say "after ${m}" } (m => m * 2) n

test "hooks" := collectLog (() => doubled 5) == (10, ["before 5", "after 10"])
-- end effects-parameter
