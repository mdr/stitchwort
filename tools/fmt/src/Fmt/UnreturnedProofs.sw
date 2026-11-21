--| No comment of the tree the formatter prints ends in a carriage return or a space (SW-4089): the declarations' words,
--| `Decl.unreturned`, and the comments the file loop prints above each declaration and at the end,
--| `SourceFile.unreturned`. The lexer takes both off (`Syntax.LexUnreturnedProofs`), comment placement and the parser carry
--| comments without changing a text, and P2 keeps every word.

namespace Fmt.UnreturnedProofs
import Std (Bool, Eq, List, Nat, Option, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (alphabet1, lexedTexts, sourcePlain1, tokens)
import Syntax.SettleSplitProofs (allPrefix, allSuffix, groupWordsConcat, groupsConcat)
import Syntax.ParseSettledStatements (lexLaid1)
import Syntax.ParseWalkOthers (parseCarriesSourceProved)
import Syntax.ParseCarries (codeWords)
import Syntax.LexUnreturnedProofs (lexUnreturned, plainEnd)
import Syntax.OnceUnreturnedProofs (onceTextsPlain)
import Fmt.PassProofs (..)
import Fmt.SettleOutputProofs (..)
import Fmt.StandsProofs (..)

-- From the words' comment texts to `unreturned`.

--| Comments whose texts all end plainly: those above end plainly (`Note.unreturned`) and the one after.
theorem commentsUnreturned ∀ (comments: Comments)
    (texts: comments.texts.all plainEnd = True):
    comments.above.all Note.unreturned = True ∧ afterUnreturned comments.after = True :=
  let split :=
    rewrite List.allAppendAnd (comments.above.map (note => note.text)) comments.after.toList plainEnd at texts then
      texts
  let aboveMap: (comments.above.map (note => note.text)).all plainEnd = True := Bool.andLeft split
  let aboveAll: comments.above.all (note => plainEnd note.text) = True :=
    rewrite List.allMapBool comments.above plainEnd (note => note.text) at aboveMap then aboveMap
  (
    aboveAll,
    match after: comments.after with
      | None => byComputing
      | Some text => Bool.andLeft (Bool.andRight split)
  )

--| A word whose comment texts all end plainly is `unreturned`.
theorem wordUnreturned ∀ (word: Word) (texts: word.comments.texts.all plainEnd = True): word.unreturned = True :=
  match commentsUnreturned word.comments texts with | (above, after) => Bool.andIntro above after

theorem wordsUnreturned ∀ (words: List Word)
    (texts: words.all (word => word.comments.texts.all plainEnd) = True):
    words.all Word.unreturned = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      Bool.andIntro (wordUnreturned word (Bool.andLeft texts)) (wordsUnreturned rest (Bool.andRight texts))

--| A test on the words of some pieces together is a test on each piece.
theorem piecesAll ∀ (pieces: List (List Word)) (p: Word → Bool)
    (all: pieces.concat.all p = True):
    pieces.all (piece => piece.all p) = True :=
  match pieces with
    | [] => byComputing
    | [piece, ..more] =>
      Bool.andIntro (allPrefix piece more.concat p all) (piecesAll more p (allSuffix piece more.concat p all))

theorem exprUnreturned ∀ (expr: Expr)
    (within: expr.within1 = True)
    (words: expr.words.all Word.unreturned = True):
    expr.unreturned = True :=
  match expr with
    | Atom kind word => Bool.andLeft words
    | Paren open inner close =>
      let tail := Bool.andRight words
      let split := rewrite List.allAppendAnd inner.words [close] Word.unreturned at tail then tail
      Bool.andIntro
        (Bool.andLeft words)
        (Bool.andIntro (exprUnreturned inner within (Bool.andLeft split)) (Bool.andLeft (Bool.andRight split)))
    | Tuple _ items _ close | ListOf _ items _ close =>
      let tail := Bool.andRight words
      let split := rewrite List.allAppendAnd (itemsWords items) [close] Word.unreturned at tail then tail
      Bool.andIntro
        (Bool.andLeft words)
        (Bool.andIntro (itemsUnreturned items within (Bool.andLeft split)) (Bool.andLeft (Bool.andRight split)))
    | App head arguments =>
      let split := rewrite List.allAppendAnd head.words (itemsWords arguments) Word.unreturned at words then words
      Bool.andIntro
        (exprUnreturned head (Bool.andLeft within) (Bool.andLeft split))
        (itemsUnreturned arguments (Bool.andRight within) (Bool.andRight split))
    | Infix kind left operator right =>
      let split := rewrite List.allAppendAnd left.words [operator, ..right.words] Word.unreturned at words then words
      let rest := Bool.andRight split
      match kind with
        | InfixBinary =>
          Bool.andIntro
            (exprUnreturned left (Bool.andLeft within) (Bool.andLeft split))
            (Bool.andIntro
              (Bool.andLeft rest)
              (exprUnreturned right (Bool.andLeft (Bool.andRight within)) (Bool.andRight rest)))
        | InfixArrow =>
          Bool.andIntro
            (exprUnreturned left (Bool.andLeft within) (Bool.andLeft split))
            (Bool.andIntro
              (Bool.andLeft rest)
              (exprUnreturned right (Bool.andLeft (Bool.andRight within)) (Bool.andRight rest)))
        | _ => cases
    | Prefix operator operand =>
      Bool.andIntro (Bool.andLeft words) (exprUnreturned operand (Bool.andLeft within) (Bool.andRight words))

theorem itemsUnreturned ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (words: (itemsWords items).all Word.unreturned = True):
    allUnreturned items = True :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      let split := rewrite List.allAppendAnd first.words (itemsWords rest) Word.unreturned at words then words
      Bool.andIntro
        (exprUnreturned first (Bool.andLeft within) (Bool.andLeft split))
        (itemsUnreturned rest (Bool.andRight within) (Bool.andRight split))

theorem declUnreturned ∀ (decl: Decl)
    (within: decl.within1 = True)
    (words: decl.words.all Word.unreturned = True):
    decl.unreturned = True :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } =>
          let tail := Bool.andRight (Bool.andRight (Bool.andRight words))
          let split :=
            rewrite List.allAppendAnd result.words
                  ([fixedWord ":=" colonEq] ++ value.words)
                  Word.unreturned at tail then
              tail
          let rest := Bool.andRight split
          Bool.andIntro
            (Bool.andLeft words)
            (Bool.andIntro
              (Bool.andLeft (Bool.andRight words))
              (Bool.andIntro
                (Bool.andLeft (Bool.andRight (Bool.andRight words)))
                (Bool.andIntro
                  (exprUnreturned result (Bool.andRight (Bool.andLeft within)) (Bool.andLeft split))
                  (Bool.andIntro
                    (Bool.andLeft rest)
                    (exprUnreturned value (Bool.andRight within) (Bool.andRight rest))))))
        | _ => cases

theorem declsUnreturned ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (pieces: (decls.map Decl.words).all (piece => piece.all Word.unreturned) = True):
    decls.all Decl.unreturned = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      Bool.andIntro
        (declUnreturned decl (Bool.andLeft within) (Bool.andLeft pieces))
        (declsUnreturned rest (Bool.andRight within) (Bool.andRight pieces))

--| The comments above a declaration's first token end plainly when the declaration's do.
theorem firstUnreturned ∀ (decl: Decl)
    (unreturned: decl.unreturned = True):
    decl.firstComments.above.all Note.unreturned = True :=
  match decl with | Definition attributes header (Assigned colonEq value) => Bool.andLeft (Bool.andLeft unreturned)

theorem declsFirstUnreturned ∀ (decls: List Decl)
    (unreturned: decls.all Decl.unreturned = True):
    decls.all (decl => decl.firstComments.above.all Note.unreturned) = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      Bool.andIntro
        (firstUnreturned decl (Bool.andLeft unreturned))
        (declsFirstUnreturned rest (Bool.andRight unreturned))

-- The parser's tree.

--| The tree the formatter parses from a source of slice 1 has declarations whose words, and an end whose comments,
--| end in neither a carriage return nor a space.
--|
--| Proof idea: the lexer's comments do (`lexUnreturned`), and `settledOnce` keeps that of its words and its end
--| (`onceTextsPlain`); the declarations' words are the groups' words, which are the file's in a row
--| (`parseCarriesSourceProved`), cut into declarations (`piecesAll`).
theorem parsedUnreturned ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    (parsed.decls.map Decl.words).all (piece => piece.all Word.unreturned) = True
      ∧ parsed.end.texts.all plainEnd = True :=
  let unreturned := lexUnreturned source lexed lexes
  let laid := lexLaid1 source lexed lexes alphabet
  let (once, onceEnd) := onceTextsPlain lexed alphabet plain (Bool.andLeft laid) unreturned
  let (words, fileEnd) := parseCarriesSourceProved source lexed parsed lexes alphabet plain parses within
  let joined: (parsed.decls.map Decl.words).concat = codeWords lexed.settledOnce.leaves :=
    rewrite words then
      Eq.trans (groupWordsConcat (groupsOf lexed.settledOnce.leaves)) (rewrite groupsConcat lexed.settledOnce.leaves)
  let all: (codeWords lexed.settledOnce.leaves).all Word.unreturned = True :=
    wordsUnreturned (codeWords lexed.settledOnce.leaves) once
  (piecesAll (parsed.decls.map Decl.words) Word.unreturned (rewrite joined then all), rewrite fileEnd then onceEnd)

--| The tree after P2 has no comment ending in a carriage return or a space: the declarations' (`Decl.unreturned`),
--| and so the file's own-line comments (`SourceFile.unreturned`). P2 keeps every word, and the end.
theorem commaUnreturned ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.withoutTrailingCommas.decls.all Decl.unreturned = True ∧ parsed.withoutTrailingCommas.unreturned = True :=
  let (pieces, ends) := parsedUnreturned source lexed parsed lexes alphabet plain parses within
  let mapped := commaMap parsed within
  let (_, endSame) := commaKeepsComments parsed within
  let commaWithin := commaKeepsWithin within
  let uncommaWords: (parsed.decls.map Decl.uncomma).map Decl.words = parsed.decls.map Decl.words :=
    declsWordsUncomma parsed.decls
  let decls: parsed.withoutTrailingCommas.decls.all Decl.unreturned = True :=
    declsUnreturned parsed.withoutTrailingCommas.decls commaWithin (rewrite mapped, uncommaWords then pieces)
  let (above, _) := commentsUnreturned parsed.end ends
  (decls, Bool.andIntro (declsFirstUnreturned parsed.withoutTrailingCommas.decls decls) (rewrite endSame then above))
