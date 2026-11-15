-- `Files` is the ability for the disk, apart from `IO`: a function that
-- says `{Files}` can read and write files but can't print, and one that
-- says `{IO}` can't touch a file. Every operation gives a `Result`.
import Std (Disk, FileError, Files, Path)
import Std.FileError (NotFound)

-- Add a line to a log file, starting it if it's missing. Only a missing file
-- counts as empty: any other error is passed on, so a file that can't be
-- read is never overwritten.
def append (path: Path) (line: Text): {Files} Result () FileError := match Files.read path with
  | Ok before => Files.write (path, before ++ line ++ "\n")
  | Err (NotFound p) => Files.write (path, line ++ "\n")
  | Err error => Err error

def notes: Path := "notes".toPath

-- `child` puts a name inside a folder.
def log: Path := notes.child "log.txt"

-- A test runs the same code on a pretend disk held in memory, and looks at
-- the disk afterwards. The real disk is never touched by checking or tests.
test "a new log" :=
  let (disk, result) := Files.simulate (Disk.fromList [(notes.child "old.txt", "")]) (() => append log "hi")
  result == Ok () ∧ disk.read log == Ok "hi\n"

test "no folder, no log" := (Files.simulate Disk.empty (() => append log "hi")).snd == Err (NotFound log)
