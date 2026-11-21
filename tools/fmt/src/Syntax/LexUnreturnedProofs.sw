--| What the lexer does to a comment's end (SW-4089): `withoutReturn` leaves a text ending in neither a carriage return
--| nor a space, so every comment of every lexed source is so, whatever the source (`lexUnreturned`). Rule N's
--| `trimEnd` keeps such a text.

namespace Syntax.LexUnreturnedProofs
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Parse, Result, Text)
import Syntax (..)
import Syntax.SettleProofs (leafTexts, leavesTextsSplit, lexedTexts, optionText, triviaTexts)
import Syntax.SettleOnceProofs (textsParked, textsReverseOnto)
import Syntax.LexLaidProofs (textsReversed)

--| A comment's text that ends in neither a carriage return nor a space.
def plainEnd (text: Text): Bool := !text.endsWith "\r" && !text.endsWith " "

--| A kept tail that ends in neither mark leaves the characters, with one more in front, so too: the front character
--| is the end only when nothing is kept, and then it is no mark.
theorem keepEnds ∀ (char: Char) (kept: List Char)
    (cr: Text.startsWithChars ['\r'] kept.reverse = False)
    (sp: Text.startsWithChars [' '] kept.reverse = False):
    Text.startsWithChars ['\r'] (if (char == '\r' || char == ' ') && kept.isEmpty then [] else [char, ..kept]).reverse
      = False
      ∧ Text.startsWithChars
        [' ']
        (if (char == '\r' || char == ' ') && kept.isEmpty then [] else [char, ..kept]).reverse
        = False :=
  match guard: (char == '\r' || char == ' ') && kept.isEmpty with
    | True => (byComputing, byComputing)
    | False =>
      match kept with
        | [] =>
          match isCr: char == '\r' with
            | False =>
              match isSp: char == ' ' with
                | False =>
                  let differCr: Text.sameChar '\r' char = False := arithmetic [isCr]
                  let differSp: Text.sameChar ' ' char = False := arithmetic [isSp]
                  ((rewrite differCr), (rewrite differSp))
        | [next, ..more] =>
          let filled: (List.reverse [next, ..more]).isEmpty = False := List.reverseOntoNonEmpty more [next] byComputing
          let goalCr: Text.startsWithChars ['\r'] (List.reverse [char, next, ..more]) = False :=
            rewrite List.reverseCons char [next, ..more],
                Text.startsWithCharsHead '\r' (List.reverse [next, ..more]) [char] filled then
              cr
          let goalSp: Text.startsWithChars [' '] (List.reverse [char, next, ..more]) = False :=
            rewrite List.reverseCons char [next, ..more],
                Text.startsWithCharsHead ' ' (List.reverse [next, ..more]) [char] filled then
              sp
          (goalCr, goalSp)

--| The characters left by `trimReturns` don't end in a carriage return or a space.
theorem trimReturnsEnds ∀ (chars: List Char):
    Text.startsWithChars ['\r'] (trimReturns chars).reverse = False
      ∧ Text.startsWithChars [' '] (trimReturns chars).reverse = False :=
  match chars with
    | [] => (byComputing, byComputing)
    | [char, ..rest] =>
      match trimReturnsEnds rest with
        | (cr, sp) => keepEnds char (trimReturns rest) cr sp

--| `withoutReturn`'s text ends in neither.
theorem withoutReturnPlain ∀ (text: Text): plainEnd (withoutReturn text) = True :=
  match trimReturnsEnds text.toList with | (cr, sp) => Bool.andIntro (rewrite cr) (rewrite sp)

-- The lexer's fold.

--| An assembly whose comments, in its leaves and waiting, end in neither mark.
def asmPlain (asm: Assembly): Bool :=
  (leafTexts asm.leaves).all plainEnd && asm.pending.all (comment => plainEnd comment.text)

theorem withTrailingPlain ∀ (leaves: List Leaf) (comment: Comment)
    (old: (leafTexts leaves).all plainEnd = True)
    (said: plainEnd comment.text = True):
    (leafTexts (withTrailing leaves comment)).all plainEnd = True :=
  match leaves with
    | [] => byComputing
    | [last, ..earlier] => textsParked plainEnd comment last earlier old said

--| One lexeme added keeps an assembly's comments ending in neither mark.
theorem addPlain ∀ (asm: Assembly) (source: Text) (lexeme: Parse.Located Lexeme)
    (plain: asmPlain asm = True):
    asmPlain (asm.add source lexeme) = True :=
  match lexeme with
    | { value, offset, length } =>
      match value with
        | Spaces | LineBreak => plain
        | CommentLexeme =>
          match asm.freshLine with
            | True =>
              Bool.andIntro
                (Bool.andLeft plain)
                (Bool.andIntro (withoutReturnPlain (source.slice offset (offset + length))) (Bool.andRight plain))
            | False =>
              Bool.andIntro
                (withTrailingPlain asm.leaves _
                  (Bool.andLeft plain)
                  (withoutReturnPlain (source.slice offset (offset + length))))
                (Bool.andRight plain)
        | TokenLexeme kind =>
          let waiting: (asm.pending.reverse.map (comment => comment.text)).all plainEnd = True :=
            rewrite textsReversed asm.pending plainEnd then Bool.andRight plain
          let lead: (asm.pending.reverse.map (comment => comment.text) ++ []).all plainEnd = True :=
            rewrite List.appendNil (asm.pending.reverse.map (comment => comment.text)) then waiting
          Bool.andIntro
            (rewrite List.allAppendAnd
                  (asm.pending.reverse.map (comment => comment.text) ++ [])
                  (leafTexts asm.leaves)
                  plainEnd then
              Bool.andIntro lead (Bool.andLeft plain))
            byComputing

theorem foldPlain ∀ (source: Text) (lexemes: List (Parse.Located Lexeme)) (asm: Assembly)
    (plain: asmPlain asm = True):
    asmPlain (lexemes.foldLeft asm (assembly lexeme => assembly.add source lexeme)) = True :=
  match lexemes with
    | [] => plain
    | [lexeme, ..rest] => foldPlain source rest (asm.add source lexeme) (addPlain asm source lexeme plain)

--| The comments of what `assemble` makes of any lexemes end in neither a carriage return nor a space.
theorem assemblePlain ∀ (source: Text) (lexemes: List (Parse.Located Lexeme)):
    (lexedTexts (assemble source lexemes)).all plainEnd = True :=
  let done := lexemes.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
  let ok := foldPlain source lexemes Assembly.start byComputing
  calc (lexedTexts (assemble source lexemes)).all plainEnd
    _ = (leafTexts done.leaves.reverse ++ triviaTexts (assemble source lexemes).end).all plainEnd :=
      rewrite leavesTextsSplit done.leaves.reverse (assemble source lexemes).end
    _ = ((leafTexts done.leaves.reverse).all plainEnd && (triviaTexts (assemble source lexemes).end).all plainEnd) :=
      List.allAppendAnd (leafTexts done.leaves.reverse) (triviaTexts (assemble source lexemes).end) plainEnd
    _ = True :=
      rewrite textsReverseOnto plainEnd done.leaves [],
          List.appendNil (done.pending.reverse.map (comment => comment.text)),
          textsReversed done.pending plainEnd then
        Bool.andIntro (Bool.andIntro (Bool.andLeft ok) byComputing) (Bool.andRight ok)

--| Every comment of a lexed source ends in neither a carriage return nor a space, whatever the source.
--|
--| Proof idea: `assemble` adds each lexeme to an assembly whose comments all end plainly; a comment it adds is
--| `withoutReturn` of the lexeme's text, which does (`trimReturnsEnds`), and moving comments to leaves changes no text.
theorem lexUnreturned ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed):
    (lexedTexts lexed).all plainEnd = True :=
  match r: lexemes source with
    | Ok found =>
      let same: assemble source found = lexed := Result.okInjective lexes
      rewrite <- same then assemblePlain source found
