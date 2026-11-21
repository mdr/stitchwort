--| The lexer's soundness for slice 1 (SW-4023, `lexLaid1` of `Syntax.ParseSettledStatements`): what a successful
--| `lex` of a source in the alphabet gives is laid out, its tokens' texts agree with their kinds on closers and `->`,
--| its comments run from `--` to the end of a line, and nothing trails the end.
--|
--| In two layers:
--|
--| 1. `assemble`'s fold (`assembleLaid`): lexemes whose texts are fine (`lexemesFine`: a comment `--` to the end of
--|    its line and followed by a line break, a token's text agreeing with its kind) make leaves that are `laid1`.
--| 2. The lexemes' reading: what `lexemes` gives of any source is fine, unless a token outside the alphabet was read.

namespace Syntax.LexLaidProofs
import Std (Bool, Char, List, Nat, Option, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (
  alphabet1,
  alphabet1Leaves,
  laidOut,
  leafTexts,
  leavesTextsSplit,
  lexedTexts,
  optionText,
  tokens,
  triviaTexts
)
import Syntax.SettleOnceProofs (isMarked, laidBack, laidOnto, laidParkedBack, pendB, textsReverseOnto)
import Syntax.LexReadsProofs (..)

-- What the lexemes must be.

--| The part of the source a lexeme says it was read from.
def lexemeText (source: Text) (lexeme: Parse.Located Lexeme): Text :=
  source.slice lexeme.offset (lexeme.offset + lexeme.length)

def Lexeme.isBreak: Lexeme → Bool
  | LineBreak => True
  | _ => False

def Lexeme.isComment: Lexeme → Bool
  | CommentLexeme => True
  | _ => False

--| A lexeme read from `text` as `assemble` needs it: a comment `--` to the end of its line once a carriage return is
--| taken off, a token of the alphabet with a text that agrees with its kind.
def lexemeFine (text: Text): Lexeme → Bool
  | CommentLexeme => rawText (withoutReturn text)
  | TokenLexeme kind => !kind.within1 || markedText text kind
  | _ => True

--| The next lexeme, if any, is a line break.
def breakNext: List (Parse.Located Lexeme) → Bool
  | [] => True
  | [next, .._] => next.value.isBreak

--| Each lexeme is fine, and each comment is followed by a line break or ends the lexemes.
def lexemesFine (source: Text): List (Parse.Located Lexeme) → Bool
  | [] => True
  | [lexeme, ..rest] =>
    lexemeFine (lexemeText source lexeme) lexeme.value
      && (!lexeme.value.isComment || breakNext rest)
      && lexemesFine source rest

-- `assemble`'s fold.

--| What holds of an assembly as it goes: its leaves are laid out (newest first), comments wait only at the start of a
--| line, a trailing comment is followed by a line break (`afterComment`: the last lexeme was a comment, whose line
--| break comes next), and the leaves' tokens and every comment's text are fine.
def asmFine (asm: Assembly) (afterComment: Bool): Bool :=
  laidBack asm.leaves
    && (asm.pending.isEmpty || asm.freshLine)
    && (!pendB asm.leaves || (asm.freshLine || afterComment))
    && asm.leaves.all (leaf => !leaf.kind.within1 || isMarked leaf)
    && (leafTexts asm.leaves).all rawText
    && asm.pending.all (comment => rawText comment.text)

--| `asmFine` without what only the next lexeme needs.
def asmDone (asm: Assembly): Bool :=
  laidBack asm.leaves
    && asm.leaves.all (leaf => !leaf.kind.within1 || isMarked leaf)
    && (leafTexts asm.leaves).all rawText
    && asm.pending.all (comment => rawText comment.text)

--| The comments' texts of reversed comments, all fine as the comments are.
theorem textsReversed ∀ (comments: List Comment) (q: Text → Bool):
    (comments.reverse.map (comment => comment.text)).all q = comments.all (comment => q comment.text) :=
  rewrite List.allMapBool comments.reverse q (comment => comment.text),
      List.allReverseOntoAnd comments [] (comment => q comment.text) then
    cases

theorem withTrailingLaid ∀ (leaves: List Leaf) (comment: Comment):
    laidBack (withTrailing leaves comment) = laidBack leaves :=
  match leaves with
    | [] => byComputing
    | [last, ..earlier] => laidParkedBack last earlier (Some comment)

theorem withTrailingMarked ∀ (leaves: List Leaf) (comment: Comment) (p: Leaf → Bool)
    (same: ∀ (leaf: Leaf) => p { leaf | trivia = { leaf.trivia | trailing = Some comment } } = p leaf):
    (withTrailing leaves comment).all p = leaves.all p :=
  match leaves with
    | [] => byComputing
    | [last, ..earlier] => rewrite same last

theorem withTrailingRaw ∀ (leaves: List Leaf) (comment: Comment)
    (old: (leafTexts leaves).all rawText = True)
    (raw: rawText comment.text = True):
    (leafTexts (withTrailing leaves comment)).all rawText = True :=
  match leaves with
    | [] => byComputing
    | [last, ..earlier] =>
      let leading := last.trivia.leading.map (comment => comment.text)
      let oldSplit: (leafTexts [last, ..earlier]).all rawText
        = ((leading ++ optionText last.trivia.trailing).all rawText && (leafTexts earlier).all rawText) :=
        List.allAppendAnd (leading ++ optionText last.trivia.trailing) (leafTexts earlier) rawText
      let oldParts := rewrite oldSplit at old then old
      let lastOld := Bool.andLeft oldParts
      let leadOk :=
        Bool.andLeft
          (rewrite List.allAppendAnd leading (optionText last.trivia.trailing) rawText at lastOld then lastOld)
      calc (leafTexts (withTrailing [last, ..earlier] comment)).all rawText
        _ = ((leading ++ [comment.text]).all rawText && (leafTexts earlier).all rawText) :=
          List.allAppendAnd (leading ++ [comment.text]) (leafTexts earlier) rawText
        _ = ((leading.all rawText && [comment.text].all rawText) && (leafTexts earlier).all rawText) :=
          rewrite List.allAppendAnd leading [comment.text] rawText
        _ = True := rewrite leadOk, raw, Bool.andRight oldParts

--| One lexeme added keeps the assembly fine, when the lexeme is and a comment's line break comes next.
--|
--| Proof idea: by the lexeme. Spaces change only the bytes; a line break starts a fresh line, which a pending comment
--| or a trailing one needs; a comment on a fresh line waits, and one after a token is that token's trailing comment,
--| with the line break known to come next; a token takes the waiting comments and starts its line if they were
--| there or the leaf before it had a trailing comment.
theorem addFine ∀ (asm: Assembly) (last: Bool) (source: Text) (lexeme: Parse.Located Lexeme)
    (fine: asmFine asm last = True)
    (ok: lexemeFine (lexemeText source lexeme) lexeme.value = True)
    (gap: (!last || lexeme.value.isBreak) = True):
    asmFine (asm.add source lexeme) lexeme.value.isComment = True :=
  match lexeme with
    | { value, offset, length } =>
      match value with
        | Spaces => rewrite Bool.notOrFalse last gap at fine then fine
        | LineBreak =>
          Bool.andIntro
            (Bool.andLeft fine)
            (Bool.andIntro
              (Bool.orTrue asm.pending.isEmpty)
              (Bool.andIntro (Bool.orTrue (!pendB asm.leaves)) (Bool.andRight (Bool.andRight (Bool.andRight fine)))))
        | CommentLexeme => addCommentFine asm last source offset length fine ok
        | TokenLexeme kind =>
          addTokenFine asm source kind offset length (rewrite Bool.notOrFalse last gap at fine then fine) ok

theorem addCommentFine ∀ (asm: Assembly) (last: Bool) (source: Text) (offset length: Nat)
    (fine: asmFine asm last = True)
    (ok: rawText (withoutReturn (source.slice offset (offset + length))) = True):
    asmFine (asm.add source { value = CommentLexeme, offset, length }) True = True :=
  match fresh: asm.freshLine with
    | True =>
      Bool.andIntro
        (Bool.andLeft fine)
        (Bool.andIntro
          (Bool.orTrue False)
          (Bool.andIntro
            (Bool.orTrue (!pendB asm.leaves))
            (Bool.andIntro
              (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight fine))))
              (Bool.andIntro
                (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fine)))))
                (Bool.andIntro ok
                  (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fine))))))))))
    | False =>
      let comment: Comment := {
        text = withoutReturn (source.slice offset (offset + length)),
        column = asm.bytes - asm.lineStart,
        blankLines = 0
      }
      let markedOld := Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight fine)))
      let markedNew: (withTrailing asm.leaves comment).all (leaf => !leaf.kind.within1 || isMarked leaf) = True :=
        rewrite withTrailingMarked asm.leaves comment (leaf => !leaf.kind.within1 || isMarked leaf) (leaf =>
              byComputing) then
          markedOld
      let laid: laidBack (withTrailing asm.leaves comment) = True :=
        rewrite withTrailingLaid asm.leaves comment then Bool.andLeft fine
      Bool.andIntro laid
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight fine))
          (Bool.andIntro
            (Bool.orTrue (!pendB (withTrailing asm.leaves comment)))
            (Bool.andIntro markedNew
              (Bool.andIntro
                (withTrailingRaw asm.leaves comment
                  (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fine)))))
                  ok)
                (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fine)))))))))

theorem addTokenFine ∀ (asm: Assembly) (source: Text) (kind: Tok) (offset length: Nat)
    (fine: asmFine asm False = True)
    (ok: (!kind.within1 || markedText (source.slice offset (offset + length)) kind) = True):
    asmFine (asm.add source { value = TokenLexeme kind, offset, length }) False = True :=
  let waiting := Bool.andLeft (Bool.andRight fine)
  let pendingFact := Bool.andLeft (Bool.andRight (Bool.andRight fine))
  let pendingOk: (!pendB asm.leaves || asm.freshLine) = True :=
    rewrite Bool.orFalse asm.freshLine at pendingFact then pendingFact
  let leadOk: (asm.pending.reverse.isEmpty || asm.freshLine) = True :=
    rewrite List.isEmptyReverseOnto asm.pending [] then (rewrite Bool.andTrue asm.pending.isEmpty then waiting)
  let textsOld := Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fine))))
  let pendingRaw := Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight fine))))
  let leadRaw: (asm.pending.reverse.map (comment => comment.text) ++ []).all rawText = True :=
    rewrite List.appendNil (asm.pending.reverse.map (comment => comment.text)), textsReversed asm.pending rawText then
      pendingRaw
  let textsNew: ((asm.pending.reverse.map (comment => comment.text) ++ []) ++ leafTexts asm.leaves).all rawText
    = True :=
    rewrite List.allAppendAnd (asm.pending.reverse.map (comment => comment.text) ++ []) (leafTexts asm.leaves) rawText,
        leadRaw then
      textsOld
  Bool.andIntro
    (Bool.andIntro leadOk (Bool.andIntro pendingOk (Bool.andLeft fine)))
    (Bool.andIntro byComputing
      (Bool.andIntro byComputing
        (Bool.andIntro
          (Bool.andIntro ok (Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight fine)))))
          (Bool.andIntro textsNew byComputing))))

--| `assemble`'s fold over fine lexemes, from a fine assembly: a fine assembly.
theorem foldFine ∀ (source: Text) (lexemes: List (Parse.Located Lexeme)) (asm: Assembly) (last: Bool)
    (fine: asmFine asm last = True)
    (gap: (!last || breakNext lexemes) = True)
    (all: lexemesFine source lexemes = True):
    asmDone (lexemes.foldLeft asm (assembly lexeme => assembly.add source lexeme)) = True :=
  match lexemes with
    | [] => Bool.andIntro (Bool.andLeft fine) (Bool.andRight (Bool.andRight (Bool.andRight fine)))
    | [lexeme, ..rest] =>
      foldFine source rest
        (asm.add source lexeme)
        lexeme.value.isComment
        (addFine asm last source lexeme fine (Bool.andLeft all) gap)
        (Bool.andLeft (Bool.andRight all))
        (Bool.andRight (Bool.andRight all))

--| `assemble` of fine lexemes: laid out, each token of the alphabet marked, each comment `--` to the end of its line,
--| nothing trailing the end.
theorem assembleLaid ∀ (source: Text) (lexemes: List (Parse.Located Lexeme))
    (fine: lexemesFine source lexemes = True):
    laidOut False (assemble source lexemes).leaves
      ∧ (assemble source lexemes).leaves.all (leaf => !leaf.kind.within1 || isMarked leaf)
      ∧ (lexedTexts (assemble source lexemes)).all rawText
      ∧ (assemble source lexemes).end.trailing.isNone :=
  let done := lexemes.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
  let ok := foldFine source lexemes Assembly.start False byComputing byComputing fine
  let texts: (lexedTexts (assemble source lexemes)).all rawText = True :=
    calc (lexedTexts (assemble source lexemes)).all rawText
      _ = (leafTexts done.leaves.reverse ++ triviaTexts (assemble source lexemes).end).all rawText :=
        rewrite leavesTextsSplit done.leaves.reverse (assemble source lexemes).end
      _ = ((leafTexts done.leaves.reverse).all rawText && (triviaTexts (assemble source lexemes).end).all rawText) :=
        List.allAppendAnd (leafTexts done.leaves.reverse) (triviaTexts (assemble source lexemes).end) rawText
      _ = True :=
        rewrite textsReverseOnto rawText done.leaves [],
            List.appendNil (done.pending.reverse.map (comment => comment.text)),
            textsReversed done.pending rawText then
          Bool.andIntro
            (Bool.andIntro (Bool.andLeft (Bool.andRight (Bool.andRight ok))) byComputing)
            (Bool.andRight (Bool.andRight (Bool.andRight ok)))
  (
    laidOnto done.leaves [] (Bool.andLeft ok) byComputing,
    rewrite List.allReverseOntoAnd done.leaves [] (leaf => !leaf.kind.within1 || isMarked leaf) then
      Bool.andIntro (Bool.andLeft (Bool.andRight ok)) byComputing,
    texts,
    byComputing
  )

-- The tokens `assemble` makes.

--| A lexeme added makes a leaf of the alphabet if it is a token of it, and keeps the leaves' kinds.
theorem addWithin ∀ (asm: Assembly) (source: Text) (lexeme: Parse.Located Lexeme):
    (asm.add source lexeme).leaves.all (leaf => leaf.kind.within1)
      = (lexeme.value.within && asm.leaves.all (leaf => leaf.kind.within1)) :=
  match lexeme with
    | { value, offset, length } =>
      match value with
        | Spaces => byComputing
        | LineBreak => byComputing
        | TokenLexeme kind => byComputing
        | CommentLexeme =>
          match asm.freshLine with
            | True => byComputing
            | False => withTrailingMarked asm.leaves _ (leaf => leaf.kind.within1) (leaf => byComputing)

theorem foldWithin ∀ (source: Text) (lexemes: List (Parse.Located Lexeme)) (asm: Assembly):
    (lexemes.foldLeft asm (assembly lexeme => assembly.add source lexeme)).leaves.all (leaf => leaf.kind.within1)
      = (asm.leaves.all (leaf => leaf.kind.within1) && lexemes.all (lexeme => lexeme.value.within)) :=
  match lexemes with
    | [] => rewrite Bool.andTrue (asm.leaves.all (leaf => leaf.kind.within1))
    | [lexeme, ..rest] =>
      rewrite foldWithin source rest (asm.add source lexeme), addWithin asm source lexeme then
        Bool.andShuffle lexeme.value.within
          (asm.leaves.all (leaf => leaf.kind.within1))
          (rest.all (lexeme => lexeme.value.within))

--| Leaves in the alphabet were made of lexemes in it.
theorem assembleWithin ∀ (source: Text) (lexemes: List (Parse.Located Lexeme))
    (within: alphabet1 (assemble source lexemes).leaves = True):
    lexemes.all (lexeme => lexeme.value.within) = True :=
  let done := lexemes.foldLeft Assembly.start (assembly lexeme => assembly.add source lexeme)
  let leaves: done.leaves.reverse.all (leaf => leaf.kind.within1) = True :=
    rewrite List.allMapBool done.leaves.reverse (token => token.kind.within1) (leaf => leaf.token) at within then within
  let forward: done.leaves.all (leaf => leaf.kind.within1) = True :=
    Bool.andLeft (rewrite List.allReverseOntoAnd done.leaves [] (leaf => leaf.kind.within1) at leaves then leaves)
  rewrite foldWithin source lexemes Assembly.start at forward then forward

-- The lexemes' reading: rounds of `item` that are fine make fine lexemes.

theorem startsBreakHead ∀ (char: Char) (one other: List Char):
    startsBreak [char, ..one] = startsBreak [char, ..other] :=
  match char with
    | '\n' => byComputing
    | _ => byComputing

theorem kindLexemeFine ∀ (chars next: List Char) (value: Lexeme)
    (fine: kindFine chars next value = True):
    lexemeFine (Text.fromList chars) value = True :=
  match value with
    | Spaces | LineBreak => byComputing
    | CommentLexeme => Bool.andLeft (Bool.andRight fine)
    | TokenLexeme kind => Bool.andRight fine

--| A round's lexeme after a comment, whose line ends where the rounds begin, is a line break: what it read starts with
--| one, and only a line break's text does.
theorem nextBreak ∀ (next read tail: List Char) (offset: Nat) (rounds: List (List (Parse.Located Lexeme)))
    (cover: next = read ++ tail)
    (each: EachAt RoundFine offset next read rounds)
    (within: rounds.concat.all (lexeme => lexeme.value.within) = True)
    (ends: endsLine next = True):
    breakNext rounds.concat = True :=
  match rounds, each with
    | [], each => byComputing
    | [round, ..more], Witness first (Witness later (Both split (Both fine rest))) =>
      let both: (round.all (lexeme => lexeme.value.within) && more.concat.all (lexeme => lexeme.value.within)) = True :=
        rewrite List.allAppendAnd round more.concat (lexeme => lexeme.value.within) at within then within
      match fine (Bool.andLeft both) with
        | Witness value (Both isRound chunk) =>
          match first with
            | [char, ..chars] =>
              let nextIs: next = [char, ..chars ++ later ++ tail] :=
                rewrite cover, split, List.appendAssoc chars later tail
              let breaks: startsBreak [char, ..chars ++ later ++ tail] = True := rewrite nextIs at ends then ends
              let headBreaks: startsBreak [char, ..chars] = True :=
                rewrite startsBreakHead char chars (chars ++ later ++ tail) then breaks
              match value with
                | LineBreak => rewrite isRound
                | Spaces =>
                  let notBreak: (!startsBreak [char, ..chars]) = True := Bool.andRight chunk
                  (Bool.falseNotTrue (rewrite headBreaks at notBreak then notBreak)).impossible
                | CommentLexeme =>
                  let notBreak: (!startsBreak [char, ..chars]) = True := Bool.andLeft chunk
                  (Bool.falseNotTrue (rewrite headBreaks at notBreak then notBreak)).impossible
                | TokenLexeme kind =>
                  let notBreak: (!startsBreak [char, ..chars]) = True := Bool.andLeft chunk
                  (Bool.falseNotTrue (rewrite headBreaks at notBreak then notBreak)).impossible

--| Fine rounds read in turn from `rest`, the source after `before`, make fine lexemes.
--|
--| Proof idea: by the rounds. Each round's one lexeme is located at `before`'s length and as long as what it read, so
--| its text is what it read (`Text.sliceMiddle`); a comment's line ends where the next round begins, so its lexeme is a
--| line break (`nextBreak`); the next rounds go on after what was read.
theorem roundsFine ∀ (source: Text) (before rest read tail: List Char) (rounds: List (List (Parse.Located Lexeme)))
    (made: source.toList = before ++ rest)
    (cover: rest = read ++ tail)
    (each: EachAt RoundFine before.length rest read rounds)
    (within: rounds.concat.all (lexeme => lexeme.value.within) = True):
    lexemesFine source rounds.concat = True :=
  match rounds, each with
    | [], each => byComputing
    | [round, ..more], Witness first (Witness later (Both split (Both fine rest1))) =>
      let both: (round.all (lexeme => lexeme.value.within) && more.concat.all (lexeme => lexeme.value.within)) = True :=
        rewrite List.allAppendAnd round more.concat (lexeme => lexeme.value.within) at within then within
      match fine (Bool.andLeft both) with
        | Witness value (Both isRound chunk) =>
          let restIs: rest = first ++ (later ++ tail) := rewrite cover, split then List.appendAssoc first later tail
          let nextIs: rest.drop first.length = later ++ tail := List.dropAppendOf rest first (later ++ tail) restIs
          let text: source.slice before.length (before.length + first.length) = Text.fromList first :=
            Text.sliceMiddle source before first (later ++ tail) (rewrite made, restIs)
          let kind: kindFine first (rest.drop first.length) value = True := Bool.andRight chunk
          let lexeme: lexemeFine (Text.fromList first) value = True :=
            kindLexemeFine first (rest.drop first.length) value kind
          let made2: source.toList = (before ++ first) ++ rest.drop first.length :=
            rewrite made, nextIs, restIs then (List.appendAssoc before first (later ++ tail)).flipped
          let rest2: EachAt RoundFine (before ++ first).length (rest.drop first.length) later more :=
            rewrite List.lengthAppend before first then rest1
          let laterFine :=
            roundsFine source
              (before ++ first)
              (rest.drop first.length)
              later
              tail
              more
              made2
              nextIs
              rest2
              (Bool.andRight both)
          let afterComment: (!value.isComment || breakNext more.concat) = True := match value with
            | CommentLexeme =>
              let ends: endsLine (rest.drop first.length) = True := Bool.andRight (Bool.andRight kind)
              rewrite nextBreak (rest.drop first.length) later tail _ more nextIs rest1 (Bool.andRight both) ends
            | _ => cases value then byComputing
          rewrite isRound then Bool.andIntro (rewrite text then lexeme) (Bool.andIntro afterComment laterFine)

theorem allMarked ∀ (leaves: List Leaf)
    (within: leaves.all (leaf => leaf.kind.within1) = True)
    (marked: leaves.all (leaf => !leaf.kind.within1 || isMarked leaf) = True):
    leaves.all isMarked = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..more] =>
      let inside: leaf.kind.within1 = True := Bool.andLeft within
      let first: (!leaf.kind.within1 || isMarked leaf) = True := Bool.andLeft marked
      let leafMarked: isMarked leaf = True := rewrite inside at first then first
      Bool.andIntro leafMarked (allMarked more (Bool.andRight within) (Bool.andRight marked))

--| What `lex` gives of a source in the alphabet is laid out, its tokens' texts agree with their kinds, its comments
--| run from `--` to the end of a line, and nothing trails the end: `lexLaid1`, in this file's names.
--|
--| Proof idea: the lexemes are all of the alphabet (`assembleWithin`), so they are fine rounds of `item`
--| (`lexemesRounds`) and fine lexemes (`roundsFine`), which `assemble` lays out (`assembleLaid`); in the alphabet,
--| every token is one whose text must agree with its kind (`allMarked`).
theorem lexLaidProved ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (within: alphabet1 lexed.leaves = True):
    laidOut False lexed.leaves
      ∧ lexed.leaves.all isMarked
      ∧ (lexedTexts lexed).all rawText
      ∧ lexed.end.trailing.isNone :=
  match r: lexemes source with
    | Ok found =>
      let same: assemble source found = lexed := Result.okInjective lexes
      let within2: alphabet1 (assemble source found).leaves = True := rewrite same then within
      let lexWithin := assembleWithin source found within2
      match lexemesRounds source found r lexWithin with
        | Witness rounds (Witness read (Witness tail (Both foundIs (Both cover each)))) =>
          let roundsWithin: rounds.concat.all (lexeme => lexeme.value.within) = True :=
            rewrite <- foundIs then lexWithin
          let fine: lexemesFine source found = True :=
            rewrite foundIs then roundsFine source [] source.toList read tail rounds byComputing cover each roundsWithin
          match assembleLaid source found fine with
            | Both laid (Both marked (Both texts ends)) =>
              let leavesWithin := alphabet1Leaves (assemble source found).leaves within2
              rewrite <- same then Both laid (Both (allMarked _ leavesWithin marked) (Both texts ends))

-- Witnesses: the narrow hypotheses above can all hold.

def noteAt: Comment := { text = "-- note", column = 0, blankLines = 0 }

theorem withTrailingTextsExample: (leafTexts (withTrailing [] noteAt)).all rawText = True :=
  withTrailingRaw [] noteAt byComputing byComputing

theorem addCommentFineExample: asmFine
      (Assembly.start.add "-- note" { value = CommentLexeme, offset = 0, length = 7 })
      True
      = True :=
  addCommentFine Assembly.start False "-- note" 0 7 byComputing byComputing
