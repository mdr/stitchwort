-- Files: count the lines of the files named on the command line, and tidy
-- a file in place, tested on a pretend disk.
--
--   $ stitchwort run files.sw -- hello.input missing.txt

import Std (Disk, FileError, Files, IO, List, Nat, Pair, Path, Result, Text)
import Std.FileError (NotFound)

-- begin count
def lineCount (path: Path): {Files} Result Nat FileError := Files.read path |> .map (text => text.lines.length)

def main(): {Files, IO} () := IO.args().forEach (name =>
  match lineCount name.toPath with
    | Ok count => IO.print "${name}: ${count} lines"
    | Err error => IO.printError "${error}")
-- end count

-- begin tidy
-- Each line without the spaces at its ends; written back only if that
-- changes anything. `Ok True` if it did.
def tidy (path: Path): {Files} Result Bool FileError := match Files.read path with
  | Err error => Err error
  | Ok text =>
    let tidied := text.lines.map (line => line.trim) |> .joinWith "\n"
    if tidied == text then Ok False else Files.write (path, tidied) |> .map (done => True)

def notes: Path := "notes.txt".toPath

test "tidy rewrites an untidy file" :=
  let (disk, changed) := Files.simulate (Disk.fromList [(notes, " a \nb")]) (() => tidy notes)
  changed == Ok True ∧ disk.read notes == Ok "a\nb"

test "tidy leaves a tidy file alone" :=
  let tidyDisk := Disk.fromList [(notes, "a\nb")]
  Files.simulate tidyDisk (() => tidy notes) == (tidyDisk, Ok False)

test "tidy of a missing file" := (Files.simulate Disk.empty (() => tidy notes)).snd == Err (NotFound notes)
-- end tidy
