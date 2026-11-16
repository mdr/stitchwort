--| The `toyfmt` file loop: the paths from the command line are walked for
--| `.sprig` files, each is formatted, and only a file whose text changes is
--| written. Everything here says `{Files}` and nothing else; `Toy.Fmt.run`
--| adds the command line and the printing.

namespace Toy.Fmt
import Std (Entry, FileError, FileKind, Files, List, Nat, Option, Path, Result, Text)

--| What the command line asked for.
type Options = { check: Bool, width: Nat, paths: List Path }

--| What formatting a file did to it, or would do with `--check`.
type Change = | Unchanged | Rewritten | WouldChange

--| What happened to one path: a file formatted, or something that went
--| wrong, as a sentence that names the path.
type Outcome = | Done (path: Path) (change: Change) | Problem (message: Text)

--| The extension of the files a folder walk picks.
def sourceExtension: Text := "sprig"

--| How many folders deep a walk goes below an argument; a folder deeper
--| than that is reported, not entered.
def maxDepth: Nat := 32

--| What listing some folders found.
type Found = { files: List Path, folders: List Path, problems: List Text }

def Found.empty: Found := { files = [], folders = [], problems = [] }

def Found.join (first second: Found): Found := {
  files = first.files ++ second.files,
  folders = first.folders ++ second.folders,
  problems = first.problems ++ second.problems
}

--| The `.sprig` files and the folders directly in `folder`, or why it
--| couldn't be listed.
def listFolder (folder: Path): {Files} Found := match Files.list folder with
  | Err error => { Found.empty | problems = ["${error}"] }
  | Ok entries =>
    let paths := (kind: FileKind) =>
      entries.filter (entry => entry.kind == kind) |> .map (entry => folder.child entry.name)
    {
      files = paths FileKind.File |> .filter (path => path.extension == Some sourceExtension),
      folders = paths FileKind.Folder,
      problems = []
    }

--| The files under `folders`, going down at most `levels` more levels, a
--| level at a time (`Files.walk` isn't in std yet).
def walkLevels: (levels: Nat) → (folders: List Path) → (found: Found) → {Files} Found
  | _, [], found => found
  | 0, folders, found => { found |
    problems = found.problems ++ folders.map (folder => "${folder}: more than ${maxDepth} folders deep, not entered")
  }
  | Succ levels, folders, found =>
    let level := folders.foldLeft Found.empty (sofar folder => sofar.join (listFolder folder))
    walkLevels levels level.folders { found |
      files = found.files ++ level.files,
      problems = found.problems ++ level.problems
    }

--| What an argument names: a file as itself, whatever its extension; a
--| folder as the `.sprig` files under it.
def expand (path: Path): {Files} Found := match Files.info path with
  | Err error => { Found.empty | problems = ["${error}"] }
  | Ok info =>
    match info.kind with
      | FileKind.File => { Found.empty | files = [path] }
      | FileKind.Folder => walkLevels maxDepth [path] Found.empty
      | FileKind.Other => { Found.empty | problems = ["${path}: not a file or a folder"] }

--| "line 3, column 9: expected ..." as "path:3:9: expected ...", the form
--| editors and `grep -n` make clickable; any other message follows the path.
def locate (path: Path) (message: Text): Text :=
  match message.stripPrefix "line " |> .flatMap (rest => rest.splitOnce ", column ") with
    | Some (line, tail) =>
      match tail.splitOnce ": " with
        | Some (column, words) => "${path}:${line}:${column}: ${words}"
        | None => "${path}: ${message}"
    | None => "${path}: ${message}"

--| Formats one file. Writes it only if the formatted text differs and
--| `--check` wasn't given.
def formatFile (options: Options) (path: Path): {Files} Outcome := match Files.read path with
  | Err error => Problem "${error}"
  | Ok source =>
    match format source options.width with
      | ParseError message => Problem (locate path message)
      | Formatted text =>
        if text == source then Outcome.Done path Unchanged
        else if options.check then Outcome.Done path WouldChange
        else
          match Files.write (path, text) with
            | Err error => Problem "${error}"
            | Ok written => Outcome.Done path Rewritten

--| Formats the files the paths name, folders walked: the problems with the
--| paths come first, then one outcome per file in path order. A problem with
--| one path never stops the others.
def formatPaths (options: Options) (paths: List Path): {Files} List Outcome :=
  let found := paths.foldLeft Found.empty (sofar path => sofar.join (expand path))
  let ordered := found.files.sort
  found.problems.map Problem ++ ordered.map (formatFile options)
