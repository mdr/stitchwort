--| The converse of `Parse.sw`: tiles written out as the puzzle has them
--| (a `Tile 2311:` heading and rows of `#` and `.`, a blank line between
--| tiles), then any line breaks, are read as those tiles.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20.Spec (JigsawWritten, PixelWritten, RowWritten, TileWritten)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem runsAsValue (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (w: a) (same: v = w) (runs: Parse.Runs p read rest v): Parse.Runs p read rest w :=
  rewrite same at runs in runs

--| A character a row of pixels can start with.
def pixelChar (char: Char): Bool := char == '#' ∨ char == '.'

def pixelSymbol: Pixel → Char
  | Rough => '#'
  | Calm => '.'

theorem spaceNotPixel (char: Char) (isSpace: Parse.isSpace char = True): pixelChar char = False := match isSpace with
  | Inl space => rewrite space.read in rfl
  | Inr tab => rewrite tab.read in rfl

--| A word that starts with a different character is not a start of the input.
theorem stripDifferent (first: Char) (others: List Char) (char: Char) (more: List Char) (different: (char == first) = False):
    Text.stripPrefixChars [first, ..others] [char, ..more] = None := match e: Text.sameChar first char with
      | False => rfl
      | True => Void.exfalso (different.read (Eq.sym (DecEq.sound (rewrite Text.sameCharEq first char at e in e))))

theorem runsPixel (shape: Pixel) (after: List Char): Parse.Runs pixel [pixelSymbol shape] after shape :=
  match shape with
    | Rough => Parse.runsPick [] "#" Rough [(".", Calm)] after rfl
    | Calm => Parse.runsPick [("#", Rough)] "." Calm [] after (Both rfl rfl)

theorem declinesPixel (rest: List Char) (stops: Parse.CannotStart pixelChar rest): Parse.Declines pixel rest :=
  Parse.declinesPick _ rest
    (match rest with
      | [] => Both rfl (Both rfl rfl)
      | [char, ..more] =>
        Both (stripDifferent '#' [] char more (Bool.orFalseLeft _ _ (stops char more rfl)))
          (Both (stripDifferent '.' [] char more (Bool.orFalseRight _ _ (stops char more rfl))) rfl))

theorem allPixels (pixels: List Pixel): (pixels.map pixelSymbol).all pixelChar = True := match pixels with
  | [] => rfl
  | [shape, ..more] => rewrite allPixels more in (match shape with | Rough => rfl | Calm => rfl)

theorem pixelWritten (read: List Char) (shape: Pixel) (written: PixelWritten read shape): read = [pixelSymbol shape] :=
  match written with
    | Inl (Both single same) => rewrite same, single in rfl
    | Inr (Both single same) => rewrite same, single in rfl

theorem eachPixels (pixels: List Pixel) (read: List Char) (h: Parse.Each PixelWritten read pixels): read = pixels.map pixelSymbol :=
  match pixels, h with
    | [], each => each
    | [shape, ..more], Witness first (Witness later (Both split (Both written each))) =>
      rewrite split, pixelWritten first shape written, eachPixels more later each in rfl

theorem runsRow (read: List Char) (row: List Pixel) (written: RowWritten read row) (after: List Char) (stops: Parse.CannotStart pixelChar after):
    Parse.Runs pixelRow read after row := match written with
      | Both each nonEmpty =>
        match row, nonEmpty with
          | [], notEmpty => Void.exfalso (notEmpty rfl)
          | [shape, ..more], notEmpty =>
            let read2 := Parse.runsMany1Symbols pixel pixelSymbol pixelChar (shape2 after _ => runsPixel shape2 after) declinesPixel shape more after
              (allPixels [shape, ..more]) stops
            rewrite eachPixels [shape, ..more] read each in
              Parse.runsMap (() => Parse.many1 pixel) NonEmptyList.toList ([shape, ..more].map pixelSymbol) after (NonEmptyList.cons shape more) read2

theorem declinesRow (input: List Char) (stops: Parse.CannotStart pixelChar input): Parse.Declines pixelRow input :=
  Parse.declinesBind (() => Parse.many1 pixel) _ input (Parse.declinesMany1 pixel input (declinesPixel input stops))

theorem runsTile (read: List Char) (tile2: Tile) (written: TileWritten read tile2) (after: List Char) (end: Parse.LinesEnd after): Parse.Runs tile read after tile2 :=
  match tile2, written with
    | { id, image }, Witness idRead (Witness lineBreak (Witness rowsRead (Both split (Both (Both idSome (Both idAll idValue)) (Both breakOk (Witness rows (Both rowsWritten rowsSame))))))) =>
      match image, rowsSame with
        | { rows = imageRows }, rowsSame2 =>
          match rows, rowsWritten with
            | { head, tail }, rowsWritten2 =>
              runsAsValue tile read after ({ id = Parse.digitsValue idRead, image = { rows = (NonEmptyList.cons head tail).toList } }: Tile) { id, image = { rows = imageRows } }
                (rewrite idValue, rowsSame2 in rfl)
                (rewrite split in
                  Parse.runsBind (() => Parse.text "Tile ") _ "Tile ".toList (idRead ++ [':'] ++ lineBreak ++ rowsRead) _ after () _ rfl
                    (Parse.runsText "Tile " _)
                    (Parse.runsBind Parse.nat _ idRead ([':'] ++ lineBreak ++ rowsRead) _ after (Parse.digitsValue idRead) _ rfl
                      (Parse.runsNat idRead _ idSome idAll rfl)
                      (Parse.runsBind (() => Parse.char ':') _ [':'] (lineBreak ++ rowsRead) _ after () _ rfl
                        (Parse.runsChar ':' _)
                        (Parse.runsBind Parse.newline _ lineBreak rowsRead _ after () _ rfl
                          (Parse.runsNewline lineBreak _ breakOk)
                          (Parse.runsBind (() => Parse.lines pixelRow) _ rowsRead [] _ after (NonEmptyList.cons head tail) _ (Eq.sym (List.appendNil rowsRead))
                            (Parse.runsLinesOf pixelRow RowWritten (Parse.CannotStart pixelChar) after
                              (read2 v after2 ok stops => runsRow read2 v ok after2 stops)
                              (read2 after2 isBreak => Parse.cannotStartAfterBreak pixelChar rfl rfl read2 after2 isBreak)
                              (Parse.cannotStartAtLinesEnd pixelChar rfl rfl spaceNotPixel after end)
                              (Parse.declinesLinesAtLinesEnd pixelRow pixelChar declinesRow rfl rfl spaceNotPixel after end)
                              rowsRead head tail rowsWritten2)
                            (Parse.runsPure _ after))))))

theorem declinesTile (input: List Char) (stops: Parse.CannotStart (char => char == 'T') input): Parse.Declines tile input :=
  Parse.declinesBind (() => Parse.text "Tile ") _ input
    (Parse.declinesText "Tile " input
      (match input with
        | [] => rfl
        | [char, ..more] => stripDifferent 'T' ['i', 'l', 'e', ' '] char more (stops char more rfl)))

theorem runsJigsaw (read: List Char) (jigsaw2: Jigsaw) (written: JigsawWritten read jigsaw2) (ending: List Char) (breaks: Parse.OnlyBreaks ending):
    Parse.Runs jigsaw read ending jigsaw2 := match jigsaw2, written with
      | { tiles }, Witness listed (Both tilesWritten same) =>
        match listed, tilesWritten with
          | { head, tail }, tilesWritten2 =>
            runsAsValue jigsaw read ending ({ tiles = (NonEmptyList.cons head tail).toList }: Jigsaw) { tiles } (rewrite same in rfl)
              (Parse.runsMap (() => Parse.sections tile) (tiles2 => { tiles = tiles2.toList }) read ending (NonEmptyList.cons head tail)
                (Parse.runsSectionsOf tile TileWritten Parse.LinesEnd ending
                  (read2 v after ok end => runsTile read2 v ok after end)
                  Parse.linesEndAfterBlank
                  (Parse.linesEndAtBreaks ending breaks)
                  (Parse.declinesSectionsAtBreaks tile (char => char == 'T') declinesTile rfl rfl ending breaks)
                  read head tail tilesWritten2))

--| The soundness theorem's conclusion: the input is the tiles written out,
--| then any line breaks.
def InputWritten (input: Text) (jigsaw2: Jigsaw): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) =>
    input.toList = read ++ ending ∧ JigsawWritten read jigsaw2 ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is tiles written out is read as those tiles.
theorem parseComplete (input: Text) (jigsaw2: Jigsaw) (written: InputWritten input jigsaw2): Fail.toResult (() => parseJigsaw input) = Ok jigsaw2 :=
  match written with
    | Witness read (Witness ending (Both split (Both jigsawWritten breaks))) =>
      Parse.runsAll input jigsaw read ending jigsaw2 split breaks (runsJigsaw read jigsaw2 jigsawWritten ending breaks)

--| Soundness (`parseWritten`) is the converse: the input is written as at most one jigsaw.
theorem writtenUnique (input: Text) (a: Jigsaw) (b: Jigsaw) (writtenA: InputWritten input a) (writtenB: InputWritten input b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
