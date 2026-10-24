-- Chapter 9: testing.
import Std (Fail, IO, List, Nat, Text)

-- begin basics
def wordCount (line: Text): Nat := line.words.length

test "counts words" := wordCount "the quick brown fox" == 4
test "an empty line has none" := wordCount "" == 0
test "a proposition, decided" := wordCount "a b" < 3
test "several at once" := wordCount "a" == 1 && wordCount "a b" == 2
-- end basics

-- begin block
test "longest word" :=
  let words := "a tea pot of milk".words
  let longest := words.maxBy (.length)
  longest == Some "milk"
-- end block

-- begin io
def greetAll(): {IO} () :=
  let names := IO.readAllLines()
  names.map (name => IO.print "Hello, ${name}!")
  IO.print "Greeted ${names.length}"

test "greets everyone" := (IO.simulate ["Ada", "Grace"] greetAll).fst == ["Hello, Ada!", "Hello, Grace!", "Greeted 2"]
-- end io

-- begin fail
def parsePair (line: Text): {Fail} (Nat, Nat) :=
  match line.split ',' with
    | [a, b] => (a.toNatOrFail, b.toNatOrFail)
    | _ => Fail.fail "expected two numbers, got '${line}'"

test "a pair" := Fail.toResult (() => parsePair "3,4") == Ok (3, 4)
test "not a pair" := Fail.toResult (() => parsePair "3") == Err "expected two numbers, got '3'"
-- end fail
