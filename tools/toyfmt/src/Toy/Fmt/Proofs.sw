--| What `format` guarantees, proved from its check: its definition parses the
--| source, prints the tree, parses the output and answers `Stable` only if
--| that tree comes back, so none of these theorems mentions a printing rule.
--|
--| The rules take the parsed tree and nothing else (`Tree.sw`: it keeps
--| nothing of the author's layout), so "the output depends on the source
--| only through its tree" is true by typing, and idempotence is the check
--| run a second time on the same tree.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Fmt (..)
import Std (DecEq, Disk, Eq, FileError, Files, Map, Path, Result, Text, Void)

def printedOr (fallback: Printed): FormatResult → Printed
  | Stable printed => printed
  | Refused _ => fallback

--| `Stable` holds one printed file: two equal answers have equal files.
theorem stableInjective ∀ (a b: Printed) (h: Stable a = Stable b): a = b := Eq.cong (printedOr a) h

--| If `format source width` answers `Stable output`, the source parses to
--| some `tree`, `output` is that tree printed at `width`, and `output`'s text
--| parses to the same `tree` (as `=`, which `format`'s `==` check implies).
theorem formatChecked ∀ (source: Text) (width: Nat) (output: Printed)
    (h: format source width = Stable output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.print width ∧ parse output.text = Ok tree :=
  match e: parse source with
    | Ok tree =>
      match c: parse (tree.print width).text == Ok tree with
        | True =>
          let same := stableInjective (tree.print width) output h
          Witness tree (Both rfl (Both (Eq.sym same) (rewrite <- same in DecEq.sound c)))

--| Round trip: if `format source width` answers `Stable output`, the source
--| parses to a tree and the output's text parses to that very tree, so
--| formatting never changes the tree. The tree has no layout, but keeps every
--| construct, name, number, string and bracket as written, the comments and
--| the kept blank lines, and the text of a declaration left as written.
theorem formatRoundTrip ∀ (source: Text) (width: Nat) (output: Printed)
    (h: format source width = Stable output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ parse output.text = Ok tree :=
  match formatChecked source width output h with
    | Witness tree (Both parsed (Both same reparsed)) => Witness tree (Both parsed reparsed)

--| Idempotence: if `format source width` answers `Stable output`, then
--| formatting `output`'s text at the same width answers `Stable output`, the
--| same text and the same count of declarations left as written. So a
--| formatted file is a fixed point, and `Stable` is what `format` says again.
theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Printed)
    (h: format source width = Stable output):
    format output.text width = Stable output :=
  match formatChecked source width output h with
    | Witness tree (Both parsed (Both same reparsed)) =>
      rewrite reparsed in
        match c: parse (tree.print width).text == Ok tree with
          | True => rewrite <- same in rfl
          | False => Void.exfalso (DecEq.soundFalse _ _ c (rewrite same at reparsed in reparsed))

-- The file loop, under `Files.simulate`: `formatFile options path` reads
-- `path` and writes only what `format` answered.

--| A file whose formatted text is its text is not written: the disk is left
--| as it was and the outcome is `Unchanged`.
theorem formatFileUnchanged ∀ (options: Options) (path: Path) (disk: Disk) (source: Text) (printed: Printed)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Stable printed)
    (same: printed.text = source):
    Files.simulate disk (() => formatFile options path) = (disk, Formatted path Unchanged printed.asWritten) :=
  rewrite readable, formatted in
    match c: printed.text == source with
      | True => rfl
      | False => Void.exfalso (DecEq.soundFalse _ _ c same)

--| With `--check`, a file whose formatted text differs is not written: the
--| disk is left as it was and the outcome is `WouldChange`.
theorem formatFileWouldChange ∀ (options: Options) (path: Path) (disk: Disk) (source: Text) (printed: Printed)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Stable printed)
    (differs: printed.text ≠ source)
    (checking: options.check = True):
    Files.simulate disk (() => formatFile options path) = (disk, Formatted path WouldChange printed.asWritten) :=
  rewrite readable, formatted in
    match c: printed.text == source with
      | True => Void.exfalso (differs (DecEq.sound c))
      | False => rewrite checking in rfl

--| Without `--check`, a file whose formatted text differs is written once,
--| with `format`'s text, at its own path: the disk afterwards is the one
--| `Disk.write path printed.text` gave, and the outcome is `Rewritten`.
theorem formatFileRewrites ∀ (options: Options) (path: Path) (disk after: Disk) (source: Text) (printed: Printed)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Stable printed)
    (differs: printed.text ≠ source)
    (writing: options.check = False)
    (allowed: disk.write path printed.text = Ok after):
    Files.simulate disk (() => formatFile options path) = (after, Formatted path Rewritten printed.asWritten) :=
  rewrite readable, formatted in
    match c: printed.text == source with
      | True => Void.exfalso (differs (DecEq.sound c))
      | False => rewrite writing, allowed in rfl

--| As `formatFileRewrites`, but the disk refuses the write: the disk is left
--| as it was and the outcome is a `Problem` naming the error.
theorem formatFileRefusedWrite ∀ (options: Options) (path: Path) (disk: Disk) (source: Text)
    (printed: Printed) (error: FileError)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Stable printed)
    (differs: printed.text ≠ source)
    (writing: options.check = False)
    (refused: disk.write path printed.text = Err error):
    Files.simulate disk (() => formatFile options path) = (disk, Problem "${error}") :=
  rewrite readable, formatted in
    match c: printed.text == source with
      | True => Void.exfalso (differs (DecEq.sound c))
      | False => rewrite writing, refused in rfl

--| A file that doesn't parse is not written: the disk is left as it was and
--| the outcome is a `Problem` with the parser's message.
theorem formatFileRefused ∀ (options: Options) (path: Path) (disk: Disk) (source message: Text)
    (readable: disk.read path = Ok source)
    (refused: format source options.width = Refused message):
    Files.simulate disk (() => formatFile options path) = (disk, Problem (locate path message)) :=
  rewrite readable, refused in rfl

--| A write the disk allows can be read back: reading `path` on the disk
--| `Disk.write path text` gave returns `text`.
theorem readAfterWrite ∀ (disk after: Disk) (path: Path) (text: Text)
    (written: disk.write path text = Ok after):
    after.read path = Ok text :=
  match climbs: Disk.climbs path with
    | False =>
      match inFolder: disk.isFolder path.normal with
        | False =>
          match blocked: disk.blocked path.normal with
            | False =>
              match parent: path.normal.parent with
                | Some folder =>
                  match folderExists: disk.isFolder folder with
                    | True =>
                      rewrite <- Result.okInjective written in rewrite Map.getInsert path.normal text disk.files in rfl

--| Formatting twice: if `format source` answered `Stable printed` and the disk
--| took `printed.text` at `path` (as `formatFileRewrites` does), then the next
--| run of `formatFile` on that disk writes nothing and finds the file
--| `Unchanged`.
theorem formatFileSettles ∀ (options: Options) (path: Path) (disk after: Disk) (source: Text) (printed: Printed)
    (formatted: format source options.width = Stable printed)
    (allowed: disk.write path printed.text = Ok after):
    Files.simulate after (() => formatFile options path) = (after, Formatted path Unchanged printed.asWritten) :=
  formatFileUnchanged options path after printed.text printed
    (readAfterWrite disk after path printed.text allowed)
    (formatIdempotent source options.width printed formatted)
    rfl
