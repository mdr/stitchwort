--| `Files`: read and write whole text files, list folders and ask what a
--| path is. Every operation returns a `Result`, so a missing file is a value
--| the program handles, not a crash. Code that touches the disk says
--| `{Files}` in its row; code that says only `{IO}` can't. `main` may have
--| `Files` beside `IO` (`def main(): {Files, IO} ()`), and then `stitchwort
--| run` and built executables perform it on the real disk, with the program's
--| own permissions. Checking and testing never do: in a test,
--| [`Files.simulate`] runs the same code against a [`Disk`] held in memory.
--|
--|   def shout (path: Path): {Files} (Result () FileError) := match Files.read path with
--|     | Err error => Err error
--|     | Ok text => Files.write (path, text.toUpper)
--|
--|   test "shout a missing file" :=
--|     (Files.simulate Disk.empty (() => shout "a.txt".toPath)).snd == Err (NotFound "a.txt".toPath)
-- (docs/proposals/file-io-and-text.md §2, §3; D3585, D3586, D3595)

-- Paths

--| Where a file or folder is: its parts in order, and whether it starts at
--| the root (`/srv/notes.txt`) or at the folder the program was started in
--| (`notes.txt`). The separator is `/` on every host. The operations read a
--| path as [`Path.normal`] gives it, so a part holding `/`, or one that is
--| `""` or `.`, means what it would in text. A part may be `..`, which the
--| host takes as the folder above; [`Files.simulate`]'s disk refuses it.
--|
--| `Path` has `==` and is `Ord`, so `<`, `.sort`, `Set Path` and `Map Path` work on
--| it. Paths compare by their parts, as lists of texts, then relative before
--| absolute. Since a list sorts just before the lists it starts, a folder
--| sorts just before what is in it.
type Path = { parts: List Text, absolute: Bool }

--| The place a path names, as the operations read it: each part split again
--| at `/`, then empty parts and `.` dropped, so `{ parts = ["a/b", "", "."],
--| absolute = False }` is `a/b`. `..` is kept. A path from [`Path.parse`] is
--| already normal.
def Path.normal (path: Path): Path := {
  parts = path.parts.concatMap (part => part.split '/') |> .filter (part => part != "" && part != "."),
  absolute = path.absolute
}

--| The path a text names: split at each `/`, with empty parts and `.`
--| dropped, so `"a//b/./c"` is `a/b/c`. A leading `/` makes it absolute;
--| `""` and `"."` are the starting folder itself.
def Path.parse (text: Text): Path := Path.normal { parts = [text], absolute = text.startsWith "/" }

--| [`Path.parse`] for dot notation: `"notes/today.txt".toPath`.
def Text.toPath (text: Text): Path := Path.parse text

--| The path as text, with `/` between parts: `/` for the root and `.` for
--| the starting folder. [`Path.parse`] reads it back.
def Path.show (path: Path): Text := match path.parts, path.absolute with
  | [], True => "/"
  | [], False => "."
  | parts, True => "/" ++ parts.joinWith "/"
  | parts, False => parts.joinWith "/"

--| `${path}` prints [`Path.show`]: `notes/today.txt`.
instance Path.instShow: Show Path := Show.fromText Path.show

--| Two paths are equal when their parts and their absoluteness are.
theorem Path.ext ∀ (p q: Path) (sameParts: p.parts = q.parts) (sameAbsolute: p.absolute = q.absolute): p = q :=
  match p, q with | { parts = a, absolute = x }, { parts = b, absolute = y } => rewrite sameParts, sameAbsolute in rfl

--| `name` inside the folder `path`: `notes.child "today.txt"` is
--| `notes/today.txt`. The name is added as one part, as written
--| ([`Path.childParts`]); the operations read it through [`Path.normal`], so
--| a name holding `/` names a place further in (`"a/b"`), `""` and `.` name
--| `path` itself, and `..` the folder above (which [`Files.simulate`]'s disk
--| refuses). Compare paths built so with `.normal` if they may differ that
--| way.
def Path.child (path: Path) (name: Text): Path := { parts = path.parts ++ [name], absolute = path.absolute }

--| A child's parts are the folder's with the name after them.
theorem Path.childParts ∀ (path: Path) (name: Text): (path.child name).parts = path.parts ++ [name] := rfl

--| `other` inside the folder `path`, if `other` is relative: `src.childPath
--| "Day05/Main.sw".toPath` is `src/Day05/Main.sw`. An absolute `other`
--| names its own place, so it is the result, as in most languages' path
--| joins.
def Path.childPath (path other: Path): Path :=
  if other.absolute then other else { parts = path.parts ++ other.parts, absolute = path.absolute }

--| Under a relative path, the parts are appended.
theorem Path.childPathParts ∀ (path other: Path)
    (relative: other.absolute = False):
    (path.childPath other).parts = path.parts ++ other.parts :=
  rewrite relative in rfl

--| An absolute path is its own place, whatever folder it is put under.
theorem Path.childPathAbsolute ∀ (path other: Path) (absolute: other.absolute = True): path.childPath other = other :=
  rewrite absolute in rfl

--| The last part, if there is one: `today.txt` for `notes/today.txt`.
def Path.name (path: Path): Option Text := path.parts.last

--| The folder the path is in, if it has a part to drop: `notes` for
--| `notes/today.txt`, the starting folder (`.`) for `today.txt`, and `None`
--| for the starting folder or the root.
def Path.parent (path: Path): Option Path := match path.parts with
  | [] => None
  | parts => Some { parts = parts.init, absolute = path.absolute }

--| What follows the last `.` of the name, if the name has one that isn't its
--| first character and something follows it: `txt` for `today.txt` and for
--| `a.b.txt`, `None` for `README`, `.profile`, `notes.` and `..`.
def Path.extension (path: Path): Option Text := match path.name with
  | None => None
  | Some name =>
    match name.split '.' with
      | [] => None
      | [whole] => None
      | ["", rest] => None
      | pieces =>
        match pieces.last with
          | Some "" => None
          | last => last

-- What the operations give

--| What a path is on the disk: a file, a folder, or something else the host
--| has there (a device or a socket, say).
type FileKind = | File | Folder | Other

--| One thing in a folder, as [`Files.list`] gives it: its name (one part, not
--| a path) and what it is.
type Entry = { name: Text, kind: FileKind }

--| What [`Files.info`] says about a path: what it is, and its size in bytes
--| (0 for a folder).
type FileInfo = { kind: FileKind, size: Nat }

--| Why a file operation failed. Each says which path it was about. The host's
--| own error codes are mapped onto these; [`OtherError`] carries the host's
--| words for anything else.
type FileError =
  --| Nothing is there, or the folder it would go in isn't.
  | NotFound (path: Path)
  --| The system refused: the program's user may not read or write it.
  | NotPermitted (path: Path)
  --| A folder is there, where a file was wanted: [`Files.read`] or
  --| [`Files.write`] of a folder.
  | NotAFile (path: Path)
  --| A file is there, where a folder was wanted: [`Files.list`] of a file, or
  --| a file in the middle of a path.
  | NotAFolder (path: Path)
  --| The file's bytes aren't UTF-8 text.
  | NotText (path: Path)
  --| Anything else, in the host's words, which differ between hosts.
  | OtherError (path: Path) (message: Text)

--| The error as a sentence for people: `notes/today.txt: no such file or
--| folder`.
def FileError.show: (error: FileError) → Text
  | NotFound path => "${path}: no such file or folder"
  | NotPermitted path => "${path}: not permitted"
  | NotAFile path => "${path}: is a folder, not a file"
  | NotAFolder path => "${path}: is a file, not a folder"
  | NotText path => "${path}: isn't UTF-8 text"
  | OtherError path message => "${path}: ${message}"

--| `${error}` prints [`FileError.show`], so `result.mapError .show |>
--| .orFail` turns a failed operation into `Fail`.
instance FileError.instShow: Show FileError := Show.fromText FileError.show

-- The ability

--| Reading and writing files, and looking at folders, a whole file at a time.
--| Only a runner performs these for real (`stitchwort run` and built
--| executables); in Stitchwort code, [`Files.simulate`] interprets them on a
--| [`Disk`]. Symbolic links are followed.
ability Files where
  read: Path → {Files} Result Text FileError -- the whole file, as UTF-8 text
  write: (Path, Text) → {Files} Result () FileError -- replaces the file whole, or creates it; never creates a folder
  list: Path → {Files} Result (List Entry) FileError -- a folder's entries, sorted by name
  info: Path → {Files} Result FileInfo FileError -- what is at the path

-- The pretend disk

--| A disk held in memory, for [`Files.simulate`]: each file's text by path,
--| the folders, each path normal ([`Path.normal`]), and the paths written so
--| far, oldest first, each one as written to ([`Disk.write`]). The starting folder
--| and the root (the paths with no parts) are always folders, and need not
--| be listed. The operations read a path through [`Path.normal`], as the
--| host does, and refuse one with a `..` part ([`Disk.noClimbing`]), where
--| the host would go to the folder above. A path is taken as written
--| otherwise, so `a.txt` is not `/home/a.txt`. Disks are equal when they hold
--| the same files with the same texts, the same folders and the same writes,
--| so a test can compare a disk after a run with the one it expects:
--| `after == before` says nothing was written, not even a file's own text
--| again, and `after.writes` says what was.
type Disk = { files: Map Path Text, folders: Set Path, writes: List Path }

--| A disk with no files, no writes, and no folders but the starting folder and the root.
def Disk.empty: Disk := { files = Map.empty, folders = Set.empty, writes = [] }

--| The folders `path` is in, outermost first, the starting folder and the
--| root left out: `a` and `a/b` for `a/b/c.txt`.
def Disk.foldersAbove (path: Path): List Path := match path.parts with
  | [] => []
  | parts =>
    let above := parts.init
    List.range 1 (above.length + 1) |> .map (n => { parts = above.take n, absolute = path.absolute })

--| The disk with these files, and every folder they are in, each path
--| normal; none of them counts as written. A path given as a file stays a file even if another file is
--| given under it, which then can't be reached.
def Disk.fromList (files: List (Path, Text)): Disk :=
  let normal := files.map (entry => (entry.fst.normal, entry.snd))
  let fileMap := Map.fromList normal
  {
    files = fileMap,
    folders = normal.concatMap (entry => Disk.foldersAbove entry.fst)
      |> .filter (folder => !fileMap.contains folder)
      |> Set.fromList,
    writes = []
  }

--| Whether the normal path `place` is a folder on the disk.
def Disk.isFolder (disk: Disk) (place: Path): Bool := place.parts.isEmpty || disk.folders.contains place

--| Whether the normal path `place` is a file on the disk.
def Disk.isFile (disk: Disk) (place: Path): Bool := disk.files.contains place

--| Whether a file stands where one of the folders the normal path `place`
--| is in should be.
def Disk.blocked (disk: Disk) (place: Path): Bool := Disk.foldersAbove place |> .any (folder => disk.isFile folder)

--| Whether `path` goes up a folder somewhere: the pretend disk refuses it.
def Disk.climbs (path: Path): Bool := path.normal.parts.contains ".."

--| The error for a path with `..`, which the pretend disk has no folder above
--| for.
def Disk.noClimbing (path: Path): FileError := OtherError path "the pretend disk has no `..`"

--| The error for `path`, which is neither a file nor a folder:
--| [`NotAFolder`] if a file stands in the way, [`NotFound`] otherwise.
def Disk.missingError (disk: Disk) (path: Path): FileError :=
  if disk.blocked path.normal then NotAFolder path else NotFound path

--| What [`Files.read`] gives on this disk.
def Disk.read (disk: Disk) (path: Path): Result Text FileError :=
  if Disk.climbs path then Err (Disk.noClimbing path)
  else
    match disk.files.get path.normal with
      | Some text => Ok text
      | None => Err (if disk.isFolder path.normal then NotAFile path else disk.missingError path)

--| The disk after [`Files.write`], or why the write fails: there's a folder
--| at the path, a file in the way, or the folder it would go in is missing.
--| A write that works adds the path, normal, to `writes`, even if the text
--| is what the file already held.
def Disk.write (disk: Disk) (path: Path) (text: Text): Result Disk FileError :=
  let place := path.normal
  if Disk.climbs path then Err (Disk.noClimbing path)
  else if disk.isFolder place then Err (NotAFile path)
  else if disk.blocked place then Err (NotAFolder path)
  else
    match place.parent with
      | Some folder =>
        if disk.isFolder folder then Ok { disk | files = disk.files.insert place text, writes = disk.writes ++ [place] }
        else Err (NotFound path)
      | None => Err (NotFound path)

--| Whether `child` is directly in the folder `folder`.
def Disk.isChild (folder child: Path): Bool := child.parent == Some folder

--| What [`Files.list`] gives on this disk: the files and folders directly in
--| the folder, sorted by name.
def Disk.list (disk: Disk) (path: Path): Result (List Entry) FileError :=
  let place := path.normal
  if Disk.climbs path then Err (Disk.noClimbing path)
  else if disk.isFolder place then
    let named := (kind: FileKind) => (child: Path) => { name = child.name.getOrElse "", kind = kind }
    let files := disk.files.keys.filter (Disk.isChild place) |> .map (named File)
    let folders := disk.folders.toList.filter (Disk.isChild place) |> .map (named Folder)
    Ok (files ++ folders |> .sortBy (a b => Text.compare a.name b.name))
  else if disk.isFile place then Err (NotAFolder path)
  else Err (disk.missingError path)

--| What [`Files.info`] gives on this disk: a file's size is its text's
--| length in UTF-8 ([`Text.utf8Length`]).
def Disk.info (disk: Disk) (path: Path): Result FileInfo FileError :=
  if Disk.climbs path then Err (Disk.noClimbing path)
  else
    match disk.files.get path.normal with
      | Some text => Ok { kind = File, size = text.utf8Length }
      | None => if disk.isFolder path.normal then Ok { kind = Folder, size = 0 } else Err (disk.missingError path)

--| Runs a program against a disk held in memory: what it reads comes from
--| `disk`, and what it writes changes it. Gives the disk at the end with the
--| program's result. Nothing outside the disk is touched.
def Files.simulate (disk: Disk) (prog: () → {Files | e} a): {e} (Disk, a) :=
  let run: Disk → {e} (Disk, a) :=
    handle prog() with
      | return x => now => (now, x)
      | Files.read path, k => now => k (now.read path) now
      | Files.write request, k => now =>
        match now.write request.fst request.snd with
          | Ok after => k (Ok ()) after
          | Err error => k (Err error) now
      | Files.list path, k => now => k (now.list path) now
      | Files.info path, k => now => k (now.info path) now
  run disk

-- Watching a program

--| One call a program made to [`Files`], without its reply: the path it was
--| about, which every constructor has as `path`. [`Files.tracing`] lists them in the order they happened.
type FileOp =
  | Reads (path: Path)
  | Writes (path: Path)
  | Lists (path: Path)
  | Infos (path: Path)

--| Runs `prog` with every `Files` operation passed on unchanged, and gives
--| the operations it made, oldest first, with its result. The operations are
--| performed by whatever handler is outside, so `Files.simulate disk (()
--| => Files.tracing prog)` watches a program on a pretend disk. A test uses
--| it to show what a program didn't do: no reads of a file, or a count of
--| writes (`ops.filter (match | Writes _ => True | _ => False)`).
def Files.tracing (prog: () → {Files | e} a): {Files | e} (List FileOp, a) :=
  let run: List FileOp → {Files | e} (List FileOp, a) :=
    handle prog() with
      | return x => seen => (seen, x)
      | Files.read path, k => seen => k (Files.read path) (seen ++ [Reads path])
      | Files.write request, k => seen => k (Files.write request) (seen ++ [Writes request.fst])
      | Files.list path, k => seen => k (Files.list path) (seen ++ [Lists path])
      | Files.info path, k => seen => k (Files.info path) (seen ++ [Infos path])
  run []

-- Laws. A handled computation computes, so each holds by `rfl` or after one
-- rewrite: they are what a proof about a file loop is built from.

theorem Files.simulatePure ∀ (disk: Disk) (x: a): Files.simulate disk (() => x) = (disk, x) := rfl

theorem Files.simulateRead ∀ (disk: Disk) (path: Path):
    Files.simulate disk (() => Files.read path) = (disk, disk.read path) :=
  rfl

theorem Files.simulateList ∀ (disk: Disk) (path: Path):
    Files.simulate disk (() => Files.list path) = (disk, disk.list path) :=
  rfl

theorem Files.simulateInfo ∀ (disk: Disk) (path: Path):
    Files.simulate disk (() => Files.info path) = (disk, disk.info path) :=
  rfl

--| A write the disk allows changes it, and gives `Ok ()`.
theorem Files.simulateWriteOk ∀ (disk after: Disk) (path: Path) (text: Text)
    (allowed: disk.write path text = Ok after):
    Files.simulate disk (() => Files.write (path, text)) = (after, Ok ()) :=
  rewrite allowed in rfl

--| A write the disk refuses leaves it as it was, and gives the error.
theorem Files.simulateWriteErr ∀ (disk: Disk) (path: Path) (text: Text) (error: FileError)
    (refused: disk.write path text = Err error):
    Files.simulate disk (() => Files.write (path, text)) = (disk, Err error) :=
  rewrite refused in rfl

--| A read, then the rest of the program: the rest runs on the read's reply.
theorem Files.simulateReadThen ∀ (disk: Disk) (path: Path) (rest: Result Text FileError → {Files} a):
    Files.simulate disk (() => rest (Files.read path)) = Files.simulate disk (() => rest (disk.read path)) :=
  rfl

--| A program that makes no operation leaves an empty trace.
theorem Files.tracingPure ∀ (disk: Disk) (x: a):
    Files.simulate disk (() => Files.tracing (() => x)) = (disk, ([], x)) :=
  rfl

test "tracing lists each operation in order and changes nothing" :=
  let disk := Disk.fromList [("a.txt".toPath, "x")]
  let prog := () =>
    Files.tracing (() =>
      let first := Files.read "a.txt".toPath
      let second := Files.write ("b.txt".toPath, "y")
      let third := Files.list ".".toPath
      (first, second, third))
  let (after, (ops, (first, second, third))) := Files.simulate disk prog
  ops == [Reads "a.txt".toPath, Writes "b.txt".toPath, Lists ".".toPath]
    && first == Ok "x"
    && second == Ok ()
    && after.read "b.txt".toPath == Ok "y"

test "the disk records each write, in order, even of the text already there" :=
  let disk := Disk.fromList [("a.txt".toPath, "x")]
  let (after, replies) := Files.simulate disk (() =>
    (Files.write ("a.txt".toPath, "x"), Files.write ("./b.txt".toPath, "y"), Files.write ("a.txt".toPath, "z")))
  after.writes == ["a.txt".toPath, "b.txt".toPath, "a.txt".toPath]
    && after.files == (Disk.fromList [("a.txt".toPath, "z"), ("b.txt".toPath, "y")]).files

test "a refused write and the other operations leave the disk equal" :=
  let disk := Disk.fromList [("a.txt".toPath, "x")]
  let (after, replies) := Files.simulate disk (() =>
    (
      Files.write ("no/such/b.txt".toPath, "y"),
      Files.read "a.txt".toPath,
      Files.list ".".toPath,
      Files.info "a.txt".toPath
    ))
  after == disk
