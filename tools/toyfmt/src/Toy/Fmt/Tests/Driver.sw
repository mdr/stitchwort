--| The file loop and the command line, on a pretend disk: what is rewritten,
--| what is left alone and not even written, what is reported as a value.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Std (Disk, Fail, Files, IO, List, Nat, Option, Path, Result, Text)

def tidy: Text := "fn add(a, b) = a + b\n"

def untidy: Text := "fn add(a,b) = a+b\n"

def broken: Text := "let x ="

--| A project's folder: a file to rewrite, one already formatted, one that
--| doesn't parse, a nested one, and a file the walk must skip.
def project: Disk := Disk.fromList [
  ("src/a.sprig".toPath, untidy),
  ("src/b.sprig".toPath, tidy),
  ("src/bad.sprig".toPath, broken),
  ("src/deep/c.sprig".toPath, untidy),
  ("src/notes.txt".toPath, untidy)
]

def options (check: Bool) (paths: List Text): Options := { check, width = 80, paths = paths.map Text.toPath }

--| The disk afterwards, whose `writes` say which files were written, and
--| the outcomes of formatting `paths`.
def runOn (disk: Disk) (check: Bool) (paths: List Text): (Disk, List Outcome) :=
  Files.simulate disk (() => formatPaths (options check paths) (options check paths).paths)

--| The paths, as the disk records the writes to them.
def written (paths: List Text): List Path := paths.map Text.toPath

def formatted (path: Text) (change: Change): Outcome := Formatted path.toPath change 0

test "a folder is walked: files are rewritten, formatted ones aren't written, the broken one is reported" :=
  let (after, outcomes) := runOn project False ["src"]
  outcomes
    == [
      formatted "src/a.sprig" Rewritten,
      formatted "src/b.sprig" Unchanged,
      Problem "src/bad.sprig:1:8: expected an expression, got the end of the input",
      formatted "src/deep/c.sprig" Rewritten
    ]
    && after
      == { Disk.fromList [
        ("src/a.sprig".toPath, tidy),
        ("src/b.sprig".toPath, tidy),
        ("src/bad.sprig".toPath, broken),
        ("src/deep/c.sprig".toPath, tidy),
        ("src/notes.txt".toPath, untidy)
      ] |
        writes = written ["src/a.sprig", "src/deep/c.sprig"]
      }

test "a second run changes nothing and writes nothing" :=
  let (after, outcomes) := runOn project False ["src"]
  let (again, moreOutcomes) := runOn after False ["src"]
  again == after
    && moreOutcomes.all (match
      | Formatted _ Unchanged _ => True
      | Problem _ => True
      | _ => False)

test "--check writes nothing and says which files would change" :=
  let (after, outcomes) := runOn project True ["src"]
  after == project
    && outcomes.filter (match
      | Formatted _ WouldChange _ => True
      | _ => False)
      == [formatted "src/a.sprig" WouldChange, formatted "src/deep/c.sprig" WouldChange]

test "a missing path is a problem, and the other paths are still done" :=
  let (after, outcomes) := runOn project False ["nowhere", "src/a.sprig"]
  outcomes == [Problem "nowhere: no such file or folder", formatted "src/a.sprig" Rewritten]
    && after.writes == written ["src/a.sprig"]

test "a file named on the command line is formatted whatever its extension" :=
  let (after, outcomes) := runOn project False ["src/notes.txt"]
  outcomes == [formatted "src/notes.txt" Rewritten] && after.read "src/notes.txt".toPath == Ok tidy

test "a parse error leaves the disk as it was and names the line and column" :=
  let (after, outcomes) := runOn project False ["src/bad.sprig"]
  after == project && outcomes == [Problem "src/bad.sprig:1:8: expected an expression, got the end of the input"]

test "a folder holding a file where a folder was wanted is reported" :=
  let (after, outcomes) := runOn project False ["src/a.sprig/inside"]
  outcomes == [Problem "src/a.sprig/inside: is a file, not a folder"] && after == project

test "a folder nested past the bound is reported, not entered" :=
  let deepPath := List.range 0 40 |> .map (n => "d") |> .joinWith "/"
  let disk := Disk.fromList [("${deepPath}/x.sprig".toPath, untidy)]
  let (after, outcomes) := runOn disk False ["d"]
  after == disk && outcomes.length == 1

test "the arguments: flags, a width, paths" :=
  parseArguments ["--check", "--width", "40", "a", "b/c"] Options.start
    == Ok { check = True, width = 40, paths = ["a".toPath, "b/c".toPath] }

test "bad arguments are refused with the usage line" :=
  parseArguments [] Options.start == Err "${usage}: no paths given"
    && parseArguments ["--wide", "a"] Options.start == Err "${usage}: unknown flag --wide"
    && parseArguments ["--width"] Options.start == Err "${usage}: --width needs a number"
    && parseArguments ["--width", "x", "a"] Options.start == Err "${usage}: --width wants a whole number, got 'x'"

test "a parse error's line and column lead the message" :=
  locate "a.sprig".toPath "line 3, column 9: expected ',' or ')', got 'b'"
    == "a.sprig:3:9: expected ',' or ')', got 'b'"
    && locate "a.sprig".toPath "something else" == "a.sprig: something else"

--| The lines `run` printed, the disk afterwards and whether it failed.
def runCli (disk: Disk) (arguments: List Text): (List Text, (Disk, Result () Text)) :=
  let pair := IO.simulate [] (() => Files.simulate disk (() => Fail.toResult (() => run arguments)))
  (pair.fst, pair.snd)

test "run rewrites the disk, prints the changed paths, and fails when a problem was found" :=
  let (printed, (after, result)) := runCli project ["src"]
  after.read "src/a.sprig".toPath == Ok tidy
    && printed == ["src/a.sprig", "src/deep/c.sprig"]
    && result == Err "toyfmt: problems"

test "run --check fails on a file it would change and succeeds on a formatted folder" :=
  let (printed, (unchanged, checked)) := runCli project ["--check", "src/b.sprig", "src/a.sprig"]
  let (nothing, (also, clean)) := runCli project ["--check", "src/b.sprig"]
  unchanged == project
    && printed == ["src/a.sprig"]
    && checked == Err "toyfmt: not formatted"
    && also == project
    && nothing == []
    && clean == Ok ()
