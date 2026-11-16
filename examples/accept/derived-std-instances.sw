-- The library's types outside the core get `==`, `<` and `${…}` like a
-- program's own: `Terminal.Size` has no hand-written instance, and `Files`'
-- and `Key`'s are the derived ones.

import Std (Terminal, Key, FileError, FileKind, FileInfo, Entry, Disk, Path, Files)
import Std.Key (Up, Down, Printable, Ctrl)

test "a record of the library compares" := ({ columns = 80, rows = 24 }: Terminal.Size) == { columns = 80, rows = 24 }

test "records differing in a field are unequal" :=
  ({ columns = 80, rows = 24 }: Terminal.Size) != { columns = 80, rows = 25 }

test "a record of the library orders by its fields in turn" :=
  ({ columns = 80, rows = 24 }: Terminal.Size) < { columns = 80, rows = 25 }
    && ({ columns = 80, rows = 99 }: Terminal.Size) < { columns = 81, rows = 0 }

test "its text lists the fields" := "${({ columns = 1, rows = 2 }: Terminal.Size)}" == "{ columns = 1, rows = 2 }"

test "keys compare and keep their declaration order" :=
  Ctrl 'a' == Ctrl 'a' && Ctrl 'a' != Printable 'a' && Up != Down && Up < Down && Printable 'z' < Up

test "the kinds of a path" := FileKind.File != FileKind.Folder && FileKind.File < FileKind.Folder

test "file errors compare by constructor, then by what they carry" :=
  FileError.NotFound "a".toPath == FileError.NotFound "a".toPath
    && FileError.NotFound "a".toPath != FileError.NotFound "b".toPath
    && FileError.NotFound "z".toPath != FileError.NotText "a".toPath
    && FileError.OtherError "a".toPath "x" == FileError.OtherError "a".toPath "x"
    && FileError.OtherError "a".toPath "x" != FileError.OtherError "a".toPath "y"

test "entries and file information compare" :=
  ({ name = "a", kind = FileKind.File }: Entry) == { name = "a", kind = FileKind.File }
    && ({ kind = FileKind.File, size = 3 }: FileInfo) != { kind = FileKind.Folder, size = 3 }

test "paths order by parts, then relative before absolute" :=
  "a/b".toPath < "a/c".toPath && "a".toPath < "a/b".toPath && "a".toPath < "/a".toPath && "a/b".toPath == "a//b".toPath

test "disks compare" := Disk.empty == Disk.empty && Disk.empty != Disk.fromList [("a.txt".toPath, "x")]
