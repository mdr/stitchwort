--| The parser reads exactly the puzzle's format: if `parseJigsaw` reads
--| `input`, the input is the tiles written out, as `Spec.JigsawWritten`
--| says, then any line breaks.

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20.Spec (JigsawWritten, PixelWritten, RowWritten, TileWritten)
import Std (Char, Fail, List, NonEmptyList, Parse, Text)

theorem readsPixel: Parse.Reads pixel PixelWritten :=
  Parse.readsWeaken (Parse.readsPickBy [Rough, Calm] Pixel.symbol)
    (read value (Both member same) =>
      match value with
        | Rough => Inl (Both same rfl)
        | Calm => Inr (Both same rfl))

theorem readsRow: Parse.Reads pixelRow RowWritten :=
  Parse.readsThen (Parse.readsMany1 pixel PixelWritten readsPixel) (pixelsRead pixels each =>
    Parse.readsDone pixels.toList _ (Both (rewrite List.appendNil pixelsRead in each) (NonEmptyList.toListNotNil pixels)))

theorem readsTile: Parse.Reads tile TileWritten :=
  Parse.readsThen (Parse.readsText "Tile ") (headRead u head =>
    Parse.readsThen Parse.readsNat (idRead id idWritten =>
      Parse.readsThen (Parse.readsChar ':') (colonRead u2 colon =>
        Parse.readsThen Parse.readsNewline (breakRead u3 break =>
          Parse.readsThen (Parse.readsLines pixelRow RowWritten readsRow) (rowsRead rows rowsWritten =>
            Parse.readsDone { id, image = { rows = rows.toList } } _
              (Witness idRead (Witness breakRead (Witness rowsRead
                (Both (rewrite head, colon, List.appendNil rowsRead in rfl)
                  (Both idWritten (Both break (Witness rows (Both rowsWritten rfl)))))))))))))

theorem readsJigsaw: Parse.Reads jigsaw JigsawWritten :=
  Parse.readsThen (Parse.readsSections tile TileWritten readsTile) (tilesRead tiles written =>
    Parse.readsDone { tiles = tiles.toList } _ (Witness tiles (Both (rewrite List.appendNil tilesRead in written) rfl)))

theorem parseWritten ∀ (input: Text) (parsed: Jigsaw) (h: Fail.toResult (() => parseJigsaw input) = Ok parsed):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ JigsawWritten read parsed ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input Aoc.Year2020.Day20.jigsaw JigsawWritten parsed h readsJigsaw
