--| What `format` guarantees for the file loop. `format` parses the source
--| and prints the tree; `DirectProofs.sw` proves the printed text parses
--| back to that tree (`printParses`), so these theorems follow from what
--| the rules print, and none mentions a printing rule.
--|
--| The rules take the parsed tree and nothing else (`Tree.sw`: it keeps
--| nothing of the author's layout), so "the output depends on the source
--| only through its tree" is true by typing, and idempotence follows from
--| the output parsing back to the same tree.
--|
--| The driver calls `format`, and the file loop's theorems below are
--| about it.

namespace Toy.Fmt.Proofs
import Toy.Fmt (..)
import Std (DecEq, Disk, FileError, Files, Map, Path, Result, Text, Void)

--| `Formatted` holds one printed file: two equal answers have equal texts.
theorem formattedInjective ∀ (a b: Text) (h: Formatted a = Formatted b): a = b := cases

--| Two equal refusals have equal messages.
theorem parseErrorInjective ∀ (a b: Text) (h: ParseError a = ParseError b): a = b := cases

-- The file loop, under `Files.simulate`: `formatFile options path` reads
-- `path` and writes only what `format` answered.

--| A file whose formatted text is its text is not written: the disk is left
--| as it was and the outcome is `Unchanged`.
theorem formatFileUnchanged ∀ (options: Options) (path: Path) (disk: Disk) (source printed: Text)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Formatted printed)
    (same: printed = source):
    Files.simulate disk (() => formatFile options path) = (disk, Outcome.Done path Unchanged) :=
  rewrite readable, formatted then
    match c: printed == source with
      | True => byComputing
      | False => (DecEq.soundFalse _ _ c same).impossible

--| With `--check`, a file whose formatted text differs is not written: the
--| disk is left as it was and the outcome is `WouldChange`.
theorem formatFileWouldChange ∀ (options: Options) (path: Path) (disk: Disk) (source printed: Text)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Formatted printed)
    (differs: printed ≠ source)
    (checking: options.check = True):
    Files.simulate disk (() => formatFile options path) = (disk, Outcome.Done path WouldChange) :=
  rewrite readable, formatted then
    match c: printed == source with
      | True => Void.impossible (differs (DecEq.sound c))
      | False => rewrite checking then byComputing

--| Without `--check`, a file whose formatted text differs is written once,
--| with `format`'s text, at its own path: the disk afterwards is the one
--| `Disk.write path printed` gave, and the outcome is `Rewritten`.
theorem formatFileRewrites ∀ (options: Options) (path: Path) (disk after: Disk) (source printed: Text)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Formatted printed)
    (differs: printed ≠ source)
    (writing: options.check = False)
    (allowed: disk.write path printed = Ok after):
    Files.simulate disk (() => formatFile options path) = (after, Outcome.Done path Rewritten) :=
  rewrite readable, formatted then
    match c: printed == source with
      | True => Void.impossible (differs (DecEq.sound c))
      | False => rewrite writing, allowed then byComputing

--| As `formatFileRewrites`, but the disk refuses the write: the disk is left
--| as it was and the outcome is a `Problem` naming the error.
theorem formatFileWriteError ∀ (options: Options) (path: Path) (disk: Disk) (source printed: Text) (error: FileError)
    (readable: disk.read path = Ok source)
    (formatted: format source options.width = Formatted printed)
    (differs: printed ≠ source)
    (writing: options.check = False)
    (refused: disk.write path printed = Err error):
    Files.simulate disk (() => formatFile options path) = (disk, Problem "${error}") :=
  rewrite readable, formatted then
    match c: printed == source with
      | True => Void.impossible (differs (DecEq.sound c))
      | False => rewrite writing, refused then byComputing

--| A file that doesn't parse is not written: the disk is left as it was and
--| the outcome is a `Problem` with the parser's message.
theorem formatFileParseError ∀ (options: Options) (path: Path) (disk: Disk) (source message: Text)
    (readable: disk.read path = Ok source)
    (refused: format source options.width = ParseError message):
    Files.simulate disk (() => formatFile options path) = (disk, Problem (locate path message)) :=
  rewrite readable, refused then byComputing

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
                      rewrite <- Result.okInjective written then
                        rewrite Map.getInsert path.normal text disk.files then byComputing

--| Formatting twice: if `format source` answered `Formatted printed` and the disk
--| took `printed` at `path` (as `formatFileRewrites` does), then the next
--| run of `formatFile` on that disk writes nothing and finds the file
--| `Unchanged`.
theorem formatFileSettles ∀ (options: Options) (path: Path) (disk after: Disk) (source printed: Text)
    (formatted: format source options.width = Formatted printed)
    (allowed: disk.write path printed = Ok after):
    Files.simulate after (() => formatFile options path) = (after, Outcome.Done path Unchanged) :=
  formatFileUnchanged options path after printed printed
    (readAfterWrite disk after path printed allowed)
    (formatIdempotent source options.width printed formatted)
    byComputing
