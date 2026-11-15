-- `Files` is the ability for the disk, apart from `IO`: a function that
-- says `{Files}` can read and write files but can't print, and one that
-- says `{IO}` can't touch a file. Every operation gives a `Result`.
import Std (Disk, FileError, Files, Path)
import Std.FileError (NotFound)

-- Add a line to a log file, starting it if it's missing.
def append (path: Path) (line: Text): {Files} Result () FileError :=
  let before := Files.read path |> .getOrElse ""
  Files.write (path, before ++ line ++ "\n")

def log: Path := "notes/log.txt".toPath

-- A test runs the same code on a pretend disk held in memory, and looks at
-- the disk afterwards. The real disk is never touched by checking or tests.
test "a new log" :=
  let (disk, result) := Files.simulate (Disk.fromList [("notes/old.txt".toPath, "")]) (() => append log "hi")
  result == Ok () ∧ disk.read log == Ok "hi\n"

test "no folder, no log" := (Files.simulate Disk.empty (() => append log "hi")).snd == Err (NotFound log)
