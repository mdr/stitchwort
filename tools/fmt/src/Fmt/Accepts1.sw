--| Slice 1's third top theorem (D3687, Matt, 19 Nov 2026): the driver formats every source of slice 1's grammar.
--| `formatKeepsProgram1` and `formatIdempotent1` (`Fmt.TopStatements`) say what holds of a source the driver
--| accepts; this says which sources those are. Slice 1 is done when all three are proved.
--|
--| The statement is fixed. `inGrammar1` is the design's grammar (`Fmt.Grammar1`), not a test taken from the
--| driver, so the theorem is proved by making `formatWithin1` accept more, never by narrowing the grammar or adding a
--| condition here. A case leaves the grammar only by a decision of Matt's that names the later slice it moves to.

namespace Fmt.Accepts1
import Std (Bool, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Grammar1 (..)
import Fmt.Driver1 (..)
import Fmt.SourcePlainProofs (alphabetOfAlphabet1, parsedSourcePlain1)
import Fmt.SettleParseProofs (settledParsesGrammar1)
import Fmt.PlacedProofs (parsedWithin1)

--| Every source in slice 1's grammar is formatted: whatever its layout and wherever its comments are, the driver
--| refuses none of it.
--|
--| Proof idea: each of the driver's tests passes on the grammar. The alphabet is the grammar's
--| (`alphabetOfAlphabet1`); a parsed source of the grammar is `sourcePlain1` (`parsedSourcePlain1`); comment placement keeps the
--| parse, so the leaves the driver parses give a tree of the grammar (`settledParsesGrammar1`); and the parser's `KeptTree`
--| walk puts a tree of the grammar in the driver's slice (`parsedWithin1`).
theorem formatAccepts1 ∀ (source: Text)
    (inGrammar: inGrammar1 source = True):
    ∃ (out: Text) => formatWithin1 source = Ok out :=
  match lexes: lex source, inGrammar with
    | Err message, inGrammar => (Bool.falseNotTrue inGrammar).impossible
    | Ok lexed, inGrammar =>
      let alphabetAll: lexed.leaves.all (leaf => leaf.token.kind.alphabet1) = True := Bool.andLeft inGrammar
      match parses: parseFile lexed, inGrammar with
        | Err message, inGrammar => (Bool.falseNotTrue (Bool.andRight inGrammar)).impossible
        | Ok file, inGrammar =>
          let grammar: file.grammar1 = True := Bool.andRight inGrammar
          let alphabet := alphabetOfAlphabet1 lexed.leaves alphabetAll
          let plain := parsedSourcePlain1 source lexed file lexes alphabetAll parses grammar
          let leaves: leavesWithin1 lexed.leaves = True := Bool.andIntro alphabet plain
          let (settled, settles, _, settledGrammar) :=
            settledParsesGrammar1 source lexed file lexes alphabetAll parses grammar
          let within := parsedWithin1 source lexed settled lexes leaves settles settledGrammar
          (settled.tidy1.printed1, formatsFrom source lexed settled lexes leaves settles within)
