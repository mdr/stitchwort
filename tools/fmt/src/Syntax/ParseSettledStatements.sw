--| What slice 1's proofs still have to say about the parser, stated and not yet proved (SW-4018; the reasons are in
--| docs/reviews/SW-4018-parser-statements.md). The sketch (docs/proposals/self-hosted-fmt-s1-sketch.md §2) names
--| `parseSettled1`, `parseCarries1` and `fuelEnough1`:
--|
--| - `parseCarries1` is the parser's one new fact: a declaration's words are its group's leaves, commas left out.
--| - `parseSettled1` follows from it without another walk of the parser, given that the leaves' words are settled
--|   (`Lexed.wordsSettled1`), which `onceWordsSettled1` gets from comment placement and `lexLaid1` from the lexer.
--| - `fuelEnough1` is not stated: no top theorem needs it (the note, §4).
--|
--| Each open goal is a proof ticket.

namespace Syntax.ParseSettledStatements
import Std (Bool, Eq, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.LexProofs (..)
import Syntax.ParseProofs (..)
import Syntax.ParseWalkFrame (..)
import Syntax.ParseCarries (codeWords)
import Syntax.ParseCarriesFile (parseCarriesOf)
import Syntax.ParseCarriesDecl (groupCarries)
import Syntax.SettleProofs (alphabet1, laidOut, lexedTexts, sourcePlain1, tokens)
import Syntax.SettleOnceProofs (onceSettledProved)
import Syntax.SettleSplitProofs (declsSettled, declsWordsOpen, groupWordsConcat, groupsConcat, settledOf, settledPieces)
import Syntax.GoodItemProofs (settledGood)
import Syntax.GlueQuietProofs (settledItemsQuiet)
import Syntax.LexLaidProofs (lexLaidProved)

-- The words of leaves.

-- `codeWords`, the words the tree keeps of some leaves, is `ParseCarries`'s, where the walk that proves
-- `parseCarries1` speaks of it.

--| `Decl.settled`, of the declaration's words alone: closers homed, `->` bare, every comment as comment placement leaves it.
def settledWords (words: List Word): Bool :=
  homedBack words.reverse && arrowsBare words && words.all (word => word.comments.texts.all commentText)

--| `settled` reads only the words.
theorem settledIsWords ∀ (decl: Decl): decl.settled = settledWords decl.words := byComputing

--| The leaves the parser reads are settled, said of their words: `settledWords` of the whole file's words in order
--| (not a group at a time: a closer's comment is homed by the code before it, which comment placement looks for across the
--| whole file), and the end's comments as comment placement leaves them.
def Lexed.wordsSettled1 (lexed: Lexed): Bool :=
  settledWords (codeWords lexed.leaves) && lexed.end.comments.texts.all commentText && lexed.end.comments.after.isNone

-- The parser.

--| `parseCarries1`: the parser carries every token to the tree. Each declaration's words are the words of its
--| group's leaves, commas left out, each with the comments its leaf had; and the file's end is the lexed end. So a
--| test on the words of the tree (`settled`) is a test on the leaves, and no comment is lost but a comma's.
--|
--| The hypotheses are `parseShaped1`'s. `good` is needed for the three tokens the tree keeps only the comments of
--| (`def`, `:`, `:=`), whose texts `Decl.words` writes back.
--|
--| Proof idea: each group's declaration carries its items (`groupCarries`: the parser reads them all, the `def`, name,
--| `:`, result type, `:=` and body in order, and what a header or body outside slice 1 would read is absent), and the
--| file's declarations are those of the groups in order (`parseCarriesOf`).
theorem parseCarries1 ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.decls.map Decl.words = (groupsOf lexed.leaves).map codeWords ∧ file.end = lexed.end.comments :=
  parseCarriesOf frame (groupCarries frame) lexed file good quiet parses within

--| `parseSettled1`: the tree of settled leaves is settled.
--|
--| Proof idea: by `parseCarries1` the declarations' words are the groups' words, and the groups in order are the
--| leaves (`groupsOf` only splits), so `settledWords` holds of all the
--| declarations' words together; each declaration's words start with `def`, which is no closer, so a closer's
--| look back (`trailsBack`) never leaves its declaration and `homedBack` holds of each alone; `arrowsBare` and the
--| comments' texts hold of every part of a list they hold of (`settledPieces`, `Syntax.SettleSplitProofs`).
theorem parseSettled1 ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (quiet: List.All (group => itemsQuiet (items group) = True) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True)
    (settled: lexed.wordsSettled1 = True):
    file.settled = True :=
  match parseCarries1 frame lexed file good quiet parses within with
    | (words, fileEnd) =>
      let joined: (file.decls.map Decl.words).concat = codeWords lexed.leaves :=
        rewrite words then Eq.trans (groupWordsConcat (groupsOf lexed.leaves)) (rewrite groupsConcat lexed.leaves)
      let whole: settledOf (file.decls.map Decl.words).concat = True := rewrite joined then Bool.andLeft settled
      let ends := Bool.andRight settled
      let pieces := settledPieces (file.decls.map Decl.words) (declsWordsOpen file.decls) whole
      rewrite fileEnd then Bool.andIntro (declsSettled file.decls pieces) ends

-- What the parser's leaves must be, and who gives it.

--| A comment's text as the lexer reads it: `--` to the end of its line.
def rawComment (text: Text): Bool := text.startsWith "--" && !text.contains "\n"

--| A leaf's text says whether it is a closer and whether it is `->`, as its kind does. The tree tests the text
--| (`isCloserText`, `operatorTok`) where comment placement tests the kind.
def Leaf.marked (leaf: Leaf): Bool :=
  isCloserText leaf.token.text == leaf.kind.isCloser
    && (operatorTok leaf.token.text == Some Arrow) == (leaf.kind == Arrow)

--| Leaves as the lexer gives them, as far as comment placement and `settled` need: laid out (a token with own-line comments,
--| or after a trailing comment, starts its line), each token's text agreeing with its kind on closers and `->`, each
--| comment `--` to the end of a line, and no trailing comment at the file's end.
def Lexed.laid1 (lexed: Lexed): Bool :=
  laidOut False lexed.leaves
    && lexed.leaves.all Leaf.marked
    && (lexedTexts lexed).all rawComment
    && lexed.end.trailing.isNone

--| The lexer's side: what it reads from any source in slice 1's alphabet is `laid1`. It is the lexer's soundness
--| (what a successful `lex` gave), where `Syntax.LexProofs` has only its completeness for printed pieces.
theorem lexLaid1 ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (within: alphabet1 lexed.leaves = True):
    lexed.laid1 = True :=
  match lexLaidProved source lexed lexes within with
    | Both laid (Both marked (Both texts ends)) => Bool.andIntro laid (Bool.andIntro marked (Bool.andIntro texts ends))

--| Comment placement's side: the leaves the formatter parses (`settledOnce`) are settled, said of their words, for `plain`
--| leaves of slice 1's alphabet as the lexer gives them.
--|
--| Proof idea: `bareSettles` makes `settledOnce`'s leaves, last commas dropped, `settledBare`'s, which are comment placement
--| on the leaves without last commas; those are still laid out and `plain`, so `settledHomed`, `settledArrowsBare1`,
--| `settledCommasBare` and `settledTrimmed` apply. Dropping the other commas, all bare, changes no closer's look
--| back (`endsOn` passes a bare comma as `trailsBack` passes nothing), `sourcePlain1` puts no comma and no `->` after a
--| `->`, and trimming keeps a comment's `--`.
theorem onceWordsSettled1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (laid: lexed.laid1 = True):
    lexed.settledOnce.wordsSettled1 = True :=
  onceSettledProved lexed within plain
    (Bool.andLeft laid)
    (Bool.andLeft (Bool.andRight laid))
    (Bool.andLeft (Bool.andRight (Bool.andRight laid)))
    (Bool.andRight (Bool.andRight (Bool.andRight laid)))

-- Cases the statements apply to, so their hypotheses can be met; and two the lexer's spelling leaves out.

--| What the statements above say of one source, as a test: lexed, in the alphabet, plain and laid; parsed from
--| `settledOnce` to a file within the slice whose words are its groups' and which is settled as its leaves are.
def holdsOn (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    match parseFile lexed.settledOnce with
      | Err _ => False
      | Ok file =>
        alphabet1 lexed.leaves
          && sourcePlain1 (tokens lexed.leaves)
          && lexed.laid1
          && file.within1
          && file.decls.map Decl.words == (groupsOf lexed.settledOnce.leaves).map codeWords
          && lexed.settledOnce.wordsSettled1
          && file.settled

--| A list broken over lines with comments in every kind of place, a last comma, a `->` and a bracket closed after a
--| comment; and a second declaration.
theorem holdsOnSettledExample: holdsOn
        "-- top\ndef d: A -> (B) := g [ -- open\n    a, -- first\n    -- above\n    b,\n  ] -- close\n\ndef e: C := -1 + f x -- end\n-- last\n"
      = True :=
  byComputing

--| A last comma that holds a comment, which `settledOnce` moves before comment placement runs.
theorem holdsOnParked: holdsOn "def d: A := (a, b, -- comma\n  )\n" = True := byComputing

--| A qualified name is one `Lower` token, in the alphabet, the slice and `lexical`, and `Spells Lower` has it.
theorem qualifiedIsLower: textLexesAs "List.map" Lower = True := byComputing

--| Likewise a number with an exponent, a `Float` that `Spells Float` has.
theorem exponentIsFloat: textLexesAs "1e3" Float = True := byComputing

--| A last comma that starts its line, which `sourcePlain1` allows (`plain1` doesn't).
theorem holdsOnOwnLineComma: holdsOn "def d: A := [1, 2\n  ,]\n" = True := byComputing

--| A comma that starts a line elsewhere than before a closer, which `plain1` allows.
theorem holdsOnLineComma: holdsOn "def d: A := f (a -- item\n  , b) -- close\n" = True := byComputing

-- The parser's statements from the source, `good` discharged.

--| `parseCarries1` for the leaves the formatter parses (`settledOnce` of what `lex` gave), from the source: `good` is
--| `settledGood`, which needs `sourcePlain1`, under which comment placement keeps every token's kind and text; the lexer spells
--| every name and numeral as slice 1 has it (`lexFixed`).
theorem parseCarriesSource ∀ (frame: FrameRest expressionAt) (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (parses: parseFile lexed.settledOnce = Ok file)
    (within: file.within1 = True):
    file.decls.map Decl.words = (groupsOf lexed.settledOnce.leaves).map codeWords
      ∧ file.end = lexed.settledOnce.end.comments :=
  parseCarries1 frame lexed.settledOnce file
    (settledGood source lexed lexes alphabet plain)
    (settledItemsQuiet source lexed lexes alphabet)
    parses
    within

--| `parseSettled1` from the source: the tree the formatter parses from a source of slice 1's alphabet and plain is
--| settled. Its leaves are settled by `onceWordsSettled1`, with `lexLaid1`.
theorem parseSettledSource ∀ (frame: FrameRest expressionAt) (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (parses: parseFile lexed.settledOnce = Ok file)
    (within: file.within1 = True):
    file.settled = True :=
  parseSettled1 frame lexed.settledOnce file
    (settledGood source lexed lexes alphabet plain)
    (settledItemsQuiet source lexed lexes alphabet)
    parses
    within
    (onceWordsSettled1 lexed alphabet plain (lexLaid1 source lexed lexes alphabet))
