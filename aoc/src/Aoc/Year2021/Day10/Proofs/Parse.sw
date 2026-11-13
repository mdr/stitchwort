--| The parser keeps the puzzle's promise: every character of the input
--| is one of the eight brackets. If `parseLines` reads `input` as
--| `lines`, the tokens of each line, written back as characters, are
--| that line of the input exactly: nothing dropped, added or changed.
--| The answers' theorems hold for every list of token lines, so they
--| need nothing more from the parser.
--
-- From std's lemmas on what parsers read (Std/Parse/Reads.sw): `eachLine`
-- gives one value per line, each what its parser read of the whole line;
-- `many` reads one part per value; `pick` from a table built from
-- `Token.char` reads a token's own character.
--
-- (D2108)

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Std (Eq, Fail, List, Parse, Text)

--| What `parseLines` reads is the input, line by line and character by
--| character.
theorem parseReadsLines ∀ (input: Text) (lines: List (List Token)) (parsed: Fail.toResult (() => parseLines input) = Ok lines):
    lines.map (tokens => tokens.map Token.char) = input.lines.map Text.toList :=
  let readsToken := Parse.readsLabel "a bracket" bracket _ (Parse.readsPickBy allTokens (token => Text.fromList [token.char]))
  let read := Parse.eachLineReads input (() => Parse.many token) _ lines parsed (Parse.readsMany token _ readsToken)
  Eq.sym (List.all2Map _ _
    (List.all2Weaken
      (line tokens each => Parse.eachChars Token.char line tokens (Parse.eachWeaken (chars token both => And.right both) tokens each)) _ _
      read))
