--| Proofs about `settledOnce` (`Syntax/Settle.sw`): the leaves the formatter parses are settled, read as words
--| (SW-4022, `onceWordsSettled1`).

namespace Syntax.SettleOnceProofs
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (
  alphabet1,
  alphabet1Leaves,
  bareComma,
  dropSpacesStart,
  emptyOf,
  endsOn,
  homedBehind,
  homedLeaf,
  leavesTextsSplit,
  laidOut,
  lexedTexts,
  arrowFollow,
  backOk,
  leafTexts,
  optionText,
  passable,
  passableKind,
  plain1,
  plainFrom,
  plainFromOf,
  settledAlphabet1,
  settledArrowsBare1,
  settledCommasBare,
  settledHomed,
  settledKeepsComments,
  settledKeepsTokens,
  stopsAt,
  tokens,
  tokensReverseOnto,
  triviaTexts
)
import Syntax.SettleBareProofs (..)

--| What `commaMoved` leaves behind a last comma that doesn't start its line: a trailing comment goes to the
--| leaf before.
def parked (trailing: Option Comment) (behind: List Leaf): List Leaf := match trailing, behind with
  | Some comment, [previous, ..earlier] => [previous.withTrailing (Some comment), ..earlier]
  | _, _ => behind

theorem leafEta ∀ (leaf: Leaf): { leaf | token = leaf.token, trivia = leaf.trivia } = leaf := match leaf with
  | { token, trivia } => byComputing

theorem triviaEta ∀ (trivia: Trivia): { trivia | leading = trivia.leading } = trivia := match trivia with
  | { leading, blankLines, trailing } => byComputing

theorem commaMovedPlain ∀ (comma closer: Leaf) (behind: List Leaf)
    (nostart: comma.token.lineStart = False)
    (nolead: comma.trivia.leading = []):
    (commaMoved comma closer behind).fst = closer
      ∧ (commaMoved comma closer behind).snd = parked comma.trivia.trailing behind :=
  match closer with
    | { token = closerToken, trivia = closerTrivia } =>
      match closerTrivia with
        | { leading = closerLeading, blankLines = closerBlank, trailing = closerTrailing } =>
          match closerToken with
            | { kind, text, column, lineStart } =>
              match comma with
                | { token = commaToken, trivia = commaTrivia } =>
                  match commaTrivia with
                    | { leading = commaLeading, blankLines = commaBlank, trailing = commaTrailing } =>
                      match commaToken with
                        | { kind = commaKind, text = commaText, column = commaColumn, lineStart = commaStart } =>
                          rewrite nostart, nolead then
                            match closerLeading with
                              | [] =>
                                match commaTrailing with
                                  | None => (byComputing, byComputing)
                                  | Some comment =>
                                    match behind with
                                      | [] => (byComputing, byComputing)
                                      | [previous, ..earlier] => (byComputing, byComputing)
                              | [first, ..others] =>
                                match commaTrailing with
                                  | None => (byComputing, byComputing)
                                  | Some comment =>
                                    match behind with
                                      | [] => (byComputing, byComputing)
                                      | [previous, ..earlier] => (byComputing, byComputing)

-- Leaves laid out, read newest first.

--| Whether the newest leaf has a trailing comment: what the next leaf is laid out after.
def pendB: List Leaf → Bool
  | [] => False
  | [leaf, .._] => leaf.trivia.trailing.isSome

--| `laidOut`, newest leaf first: each leaf with own-line comments, or after a trailing comment, starts its line.
def laidBack: List Leaf → Bool
  | [] => True
  | [leaf, ..older] =>
    (leaf.trivia.leading.isEmpty || leaf.token.lineStart) && (!pendB older || leaf.token.lineStart) && laidBack older

theorem orOfFalse ∀ (x s: Bool) (h: (x || s) = True) (off: s = False): x = True := cases

theorem laidNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) [leaf, ..after] = True):
    laidBack [leaf, ..behind] = True ∧ laidOut (pendB [leaf, ..behind]) after = True :=
  (
    Bool.andIntro (Bool.andLeft fwd) (Bool.andIntro (Bool.andLeft (Bool.andRight fwd)) back),
    Bool.andRight (Bool.andRight fwd)
  )

theorem notOrFalse ∀ (x: Bool) (h: (!x || False) = True): x = False := cases

theorem laidParkedBack ∀ (previous: Leaf) (tail: List Leaf) (trailing: Option Comment):
    laidBack [previous.withTrailing trailing, ..tail] = laidBack [previous, ..tail] :=
  match previous with
    | { token, trivia } =>
      match trivia with
        | { leading, blankLines, trailing = old } => byComputing

theorem laidPair ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (nostart: comma.token.lineStart = False)
    (back: laidBack [previous, ..tail] = True)
    (fwd: laidOut (pendB [previous, ..tail]) [comma, closer, ..after] = True):
    laidBack [closer, ..parked comma.trivia.trailing [previous, ..tail]] = True
      ∧ laidOut (pendB [closer, ..parked comma.trivia.trailing [previous, ..tail]]) after = True :=
  let commaOk := Bool.andLeft fwd
  let commaPending := Bool.andLeft (Bool.andRight fwd)
  let closerPart := Bool.andRight (Bool.andRight fwd)
  let closerLead := Bool.andLeft closerPart
  let closerPending := Bool.andLeft (Bool.andRight closerPart)
  let closerRest := Bool.andRight (Bool.andRight closerPart)
  let noPending: previous.trivia.trailing.isSome = False :=
    notOrFalse previous.trivia.trailing.isSome (rewrite nostart at commaPending then commaPending)
  match trailing: comma.trivia.trailing with
    | None => (Bool.andIntro closerLead (Bool.andIntro (rewrite noPending) back), closerRest)
    | Some comment =>
      let closerStarts: closer.token.lineStart = True := closerPending
      (
        Bool.andIntro closerLead
          (Bool.andIntro (rewrite closerStarts) (rewrite laidParkedBack previous tail (Some comment) then back)),
        closerRest
      )

--| Laid out stays laid out through `withoutLastCommas`: a last comma that is laid out starts no line and holds no
--| own-line comment, so only its trailing comment moves, to the leaf before, whose closer then starts its line.
theorem laidWithout ∀ (behind rest: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) rest = True)
    (plain: plainFrom (tokens rest) = True):
    laidBack (withoutR behind rest) = True :=
  match rest with
    | [] => back
    | [leaf, ..after] =>
      match pair: fwdPair behind leaf after with
        | False =>
          let (b, f) := laidNop leaf behind after back fwd
          rewrite withoutRNop leaf behind after pair then
            laidWithout [leaf, ..behind] after b f (plainTail leaf after plain)
        | True =>
          match after with
            | [closer, ..after2] =>
              let isComma: (leaf.token.kind == Comma) = True := Bool.andLeft pair
              let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
              let item: hasItem behind = True := Bool.andRight (Bool.andRight pair)
              let item: hasItem behind = True := Bool.andRight (Bool.andRight pair)
              let nostart := plainNoStart leaf closer after2 isComma isCloser plain
              let leadOk := Bool.andLeft fwd
              let nolead: leaf.trivia.leading = [] :=
                emptyOf leaf.trivia.leading (orOfFalse leaf.trivia.leading.isEmpty leaf.token.lineStart leadOk nostart)
              match behind with
                | [previous, ..tail] =>
                  let (b, f) := laidPair leaf closer previous tail after2 nostart back fwd
                  let (movedFst, movedSnd) := commaMovedPlain leaf closer [previous, ..tail] nostart nolead
                  rewrite withoutRPair leaf closer [previous, ..tail] after2 pair, movedFst, movedSnd then
                    laidWithout
                      [closer, ..parked leaf.trivia.trailing [previous, ..tail]]
                      after2
                      b
                      f
                      (plainTail closer after2 (plainTail leaf [closer, ..after2] plain))

-- Plain, read newest first.

theorem plainBackConverse ∀ (ahead: List Token) (newest: Token) (behind: List Token)
    (ok: backOk (ahead.reverseOnto [newest, ..behind]) = True):
    plainFrom [newest, ..ahead] = True ∧ backOk [newest, ..behind] = True :=
  match ahead with
    | [] => (byComputing, ok)
    | [next, ..rest] =>
      let (more, older) := plainBackConverse rest next [newest, ..behind] ok
      (
        Bool.andIntro (Bool.andLeft older) (Bool.andIntro (Bool.andLeft (Bool.andRight older)) more),
        Bool.andRight (Bool.andRight older)
      )

theorem plainOfBack ∀ (forward: List Token) (ok: backOk (forward.reverseOnto []) = True): plain1 forward = True :=
  match forward with
    | [] => byComputing
    | [first, ..ahead] =>
      let (more, only) := plainBackConverse ahead first [] ok
      Bool.andIntro only more

--| The leaves done, newest first, and the leaves to come read as plain.
def plainJoin (behind rest: List Leaf): Bool := match behind with
  | [] => plain1 (tokens rest)
  | [newest, ..older] => backOk (tokens behind) && plainFrom [newest.token, ..tokens rest]

theorem plainNop ∀ (leaf: Leaf) (behind after: List Leaf)
    (join: plainJoin behind [leaf, ..after] = True):
    plainJoin [leaf, ..behind] after = True :=
  match behind with
    | [] => Bool.andIntro (Bool.andLeft join) (Bool.andRight join)
    | [newest, ..older] =>
      Bool.andIntro
        (Bool.andIntro
          (Bool.andLeft (Bool.andRight join))
          (Bool.andIntro (Bool.andLeft (Bool.andRight (Bool.andRight join))) (Bool.andLeft join)))
        (Bool.andRight (Bool.andRight (Bool.andRight join)))

theorem itemNotComma ∀ (previous: Leaf) (tail: List Leaf)
    (item: hasItem [previous, ..tail] = True):
    (previous.token.kind == Comma) = False :=
  match isComma: previous.token.kind == Comma with
    | False => byComputing
    | True =>
      let nothing: hasItem [previous, ..tail] = False := hasItemComma previous tail isComma
      rewrite nothing at item then cases

theorem notArrowBeforeComma ∀ (x: Bool) (h: (!x || !arrowFollow Comma) = True): x = False := cases

theorem tokensParked ∀ (trailing: Option Comment) (behind: List Leaf):
    tokens (parked trailing behind) = tokens behind :=
  match trailing with
    | None => byComputing
    | Some comment =>
      match behind with
        | [] => byComputing
        | [previous, ..earlier] => byComputing

theorem plainPair ∀ (comma closer previous: Leaf) (tail after: List Leaf)
    (isComma: (comma.token.kind == Comma) = True)
    (nostart: comma.token.lineStart = False)
    (item: hasItem [previous, ..tail] = True)
    (join: plainJoin [previous, ..tail] [comma, closer, ..after] = True):
    plainJoin
      [(commaMoved comma closer [previous, ..tail]).fst, ..(commaMoved comma closer [previous, ..tail]).snd]
      after
      = True :=
  let back := Bool.andLeft join
  let first := Bool.andLeft (Bool.andRight join)
  let second := Bool.andLeft (Bool.andRight (Bool.andRight join))
  let notComma := itemNotComma previous tail item
  let notArrow: (previous.token.kind == Arrow) = False :=
    notArrowBeforeComma (previous.token.kind == Arrow) (rewrite DecEq.sound isComma at first then first)
  let firstOk: (!(previous.token.kind == Arrow) || !arrowFollow closer.token.kind) = True := rewrite notArrow
  let secondOk: (!(previous.token.kind == Comma && previous.token.lineStart) || !passableKind closer.token.kind)
    = True :=
    rewrite notComma
  let (fstTok, sndToks) := commaMovedTokens comma closer [previous, ..tail] nostart
  rewrite fstTok, sndToks then
    Bool.andIntro
      (Bool.andIntro firstOk (Bool.andIntro secondOk back))
      (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight join)))))

--| Plain stays plain through `withoutLastCommas`: the closer after a dropped comma follows an item, which is neither
--| `->` (the comma after it was allowed) nor a comma.
theorem plainWithout ∀ (behind rest: List Leaf)
    (join: plainJoin behind rest = True)
    (plain: plainFrom (tokens rest) = True):
    plainJoin (withoutR behind rest) [] = True :=
  match rest with
    | [] => join
    | [leaf, ..after] =>
      match pair: fwdPair behind leaf after with
        | False =>
          rewrite withoutRNop leaf behind after pair then
            plainWithout [leaf, ..behind] after (plainNop leaf behind after join) (plainTail leaf after plain)
        | True =>
          match after with
            | [closer, ..after2] =>
              let isComma: (leaf.token.kind == Comma) = True := Bool.andLeft pair
              let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
              let item: hasItem behind = True := Bool.andRight (Bool.andRight pair)
              let nostart := plainNoStart leaf closer after2 isComma isCloser plain
              match behind with
                | [previous, ..tail] =>
                  rewrite withoutRPair leaf closer [previous, ..tail] after2 pair then
                    plainWithout
                      [
                        (commaMoved leaf closer [previous, ..tail]).fst,
                        ..(commaMoved leaf closer [previous, ..tail]).snd
                      ]
                      after2
                      (plainPair leaf closer previous tail after2 isComma nostart item join)
                      (plainTail closer after2 (plainTail leaf [closer, ..after2] plain))

-- What the leaves hold stays what they hold.

theorem allAppendB ∀ (xs ys: List a) (p: a → Bool): (xs ++ ys).all p = (xs.all p && ys.all p) := match xs with
  | [] => byComputing
  | [x, ..rest] =>
    match p x with
      | True => allAppendB rest ys p
      | False => byComputing

--| `withoutLastCommas` keeps every token, but the commas it drops: a test on every token still holds.
theorem allTokensWithout ∀ (q: Token → Bool) (behind rest: List Leaf)
    (plain: plainFrom (tokens rest) = True)
    (kept: (tokens behind).all q = True)
    (coming: (tokens rest).all q = True):
    (tokens (withoutR behind rest)).all q = True :=
  match rest with
    | [] => kept
    | [leaf, ..after] =>
      match pair: fwdPair behind leaf after with
        | False =>
          rewrite withoutRNop leaf behind after pair then
            allTokensWithout q
              [leaf, ..behind]
              after
              (plainTail leaf after plain)
              (Bool.andIntro (Bool.andLeft coming) kept)
              (Bool.andRight coming)
        | True =>
          match after with
            | [closer, ..after2] =>
              let isComma: (leaf.token.kind == Comma) = True := Bool.andLeft pair
              let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
              let nostart := plainNoStart leaf closer after2 isComma isCloser plain
              let (fstTok, sndToks) := commaMovedTokens leaf closer behind nostart
              rewrite withoutRPair leaf closer behind after2 pair then
                allTokensWithout q
                  [(commaMoved leaf closer behind).fst, ..(commaMoved leaf closer behind).snd]
                  after2
                  (plainTail closer after2 (plainTail leaf [closer, ..after2] plain))
                  (rewrite fstTok, sndToks then Bool.andIntro (Bool.andLeft (Bool.andRight coming)) kept)
                  (Bool.andRight (Bool.andRight coming))

theorem textsCons ∀ (leaf: Leaf) (rest: List Leaf):
    leafTexts [leaf, ..rest] = triviaTexts leaf.trivia ++ leafTexts rest :=
  byComputing

theorem textsParked ∀ (q: Text → Bool) (comment: Comment) (previous: Leaf) (earlier: List Leaf)
    (kept: (leafTexts [previous, ..earlier]).all q = True)
    (said: q comment.text = True):
    (leafTexts [previous.withTrailing (Some comment), ..earlier]).all q = True :=
  match previous with
    | { token, trivia } =>
      match trivia with
        | { leading, blankLines, trailing } =>
          let split :=
            rewrite textsCons { token, trivia = { leading, blankLines, trailing } } earlier,
                allAppendB (triviaTexts { leading, blankLines, trailing }) (leafTexts earlier) q at kept then
              kept
          let triv := Bool.andLeft split
          let lead: (leading.map (c => c.text)).all q = True :=
            Bool.andLeft (rewrite allAppendB (leading.map (c => c.text)) (optionText trailing) q at triv then triv)
          rewrite textsCons { token, trivia = { leading, blankLines, trailing = Some comment } } earlier,
              allAppendB (triviaTexts { leading, blankLines, trailing = Some comment }) (leafTexts earlier) q then
            Bool.andIntro
              (rewrite allAppendB (leading.map (c => c.text)) (optionText (Some comment)) q then
                Bool.andIntro lead (Bool.andIntro said byComputing))
              (Bool.andRight split)

theorem textsParkedAll ∀ (q: Text → Bool) (trailing: Option Comment) (behind: List Leaf)
    (kept: (leafTexts behind).all q = True)
    (said: (optionText trailing).all q = True):
    (leafTexts (parked trailing behind)).all q = True :=
  match trailing with
    | None => kept
    | Some comment =>
      match behind with
        | [] => kept
        | [previous, ..earlier] => textsParked q comment previous earlier kept (Bool.andLeft said)

--| `withoutLastCommas` keeps every comment but the text it moves is the same text: a test on every comment text still
--| holds.
theorem textsWithout ∀ (q: Text → Bool) (behind rest: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) rest = True)
    (plain: plainFrom (tokens rest) = True)
    (kept: (leafTexts behind).all q = True)
    (coming: (leafTexts rest).all q = True):
    (leafTexts (withoutR behind rest)).all q = True :=
  match rest with
    | [] => kept
    | [leaf, ..after] =>
      match pair: fwdPair behind leaf after with
        | False =>
          let (b, f) := laidNop leaf behind after back fwd
          let split :=
            rewrite textsCons leaf after, allAppendB (triviaTexts leaf.trivia) (leafTexts after) q at coming then coming
          rewrite withoutRNop leaf behind after pair then
            textsWithout q
              [leaf, ..behind]
              after
              b
              f
              (plainTail leaf after plain)
              (rewrite textsCons leaf behind, allAppendB (triviaTexts leaf.trivia) (leafTexts behind) q then
                Bool.andIntro (Bool.andLeft split) kept)
              (Bool.andRight split)
        | True =>
          match after with
            | [closer, ..after2] =>
              let isComma: (leaf.token.kind == Comma) = True := Bool.andLeft pair
              let isCloser: closer.token.kind.isCloser = True := Bool.andLeft (Bool.andRight pair)
              let nostart := plainNoStart leaf closer after2 isComma isCloser plain
              let leadOk := Bool.andLeft fwd
              let nolead: leaf.trivia.leading = [] :=
                emptyOf leaf.trivia.leading (orOfFalse leaf.trivia.leading.isEmpty leaf.token.lineStart leadOk nostart)
              match behind with
                | [] => cases
                | [previous, ..tail] =>
                  let (b, f) := laidPair leaf closer previous tail after2 nostart back fwd
                  let (movedFst, movedSnd) := commaMovedPlain leaf closer [previous, ..tail] nostart nolead
                  let split1 :=
                    rewrite textsCons leaf [closer, ..after2],
                        allAppendB (triviaTexts leaf.trivia) (leafTexts [closer, ..after2]) q at coming then
                      coming
                  let commaHeld := Bool.andLeft split1
                  let commaAll: (optionText leaf.trivia.trailing).all q = True :=
                    rewrite nolead at commaHeld then commaHeld
                  let closerPart := Bool.andRight split1
                  let split2 :=
                    rewrite textsCons closer after2,
                        allAppendB (triviaTexts closer.trivia) (leafTexts after2) q at closerPart then
                      closerPart
                  let parkedAll := textsParkedAll q leaf.trivia.trailing [previous, ..tail] kept commaAll
                  rewrite withoutRPair leaf closer [previous, ..tail] after2 pair, movedFst, movedSnd then
                    textsWithout q
                      [closer, ..parked leaf.trivia.trailing [previous, ..tail]]
                      after2
                      b
                      f
                      (plainTail closer after2 (plainTail leaf [closer, ..after2] plain))
                      (rewrite textsCons closer (parked leaf.trivia.trailing [previous, ..tail]),
                          allAppendB
                            (triviaTexts closer.trivia)
                            (leafTexts (parked leaf.trivia.trailing [previous, ..tail]))
                            q then
                        Bool.andIntro (Bool.andLeft split2) parkedAll)
                      (Bool.andRight split2)

-- A comment trimmed of the spaces at its end is still a comment, and the lexer's test of one holds.

--| A comment's characters without those at their end that are spaces (`trimEnd`).
def trimChars (chars: List Char): List Char := (chars.reverse.dropWhile (char => char == ' ')).reverse

theorem dropWhileBefore ∀ (p: Char → Bool) (xs: List Char) (stop: Char) (more: List Char)
    (stops: p stop = False):
    (xs ++ [stop, ..more]).dropWhile p = xs.dropWhile p ++ [stop, ..more] :=
  match xs with
    | [] => rewrite stops
    | [x, ..rest] =>
      match p x with
        | True => dropWhileBefore p rest stop more stops
        | False => byComputing

theorem trimCharsSecond ∀ (first second: Char) (rest: List Char)
    (stops: (second == ' ') = False):
    trimChars [first, second, ..rest] = [first, second, ..trimChars rest] :=
  let reversed: [first, second, ..rest].reverse = rest.reverse ++ [second, first] := calc [
    first,
    second,
    ..rest
  ].reverse
    _ = [second, ..rest].reverse ++ [first] := List.reverseCons first [second, ..rest]
    _ = (rest.reverse ++ [second]) ++ [first] := rewrite List.reverseCons second rest
    _ = rest.reverse ++ [second, first] := List.appendAssoc rest.reverse [second] [first]
  calc trimChars [first, second, ..rest]
    _ = ((rest.reverse ++ [second, first]).dropWhile (char => char == ' ')).reverse := rewrite reversed
    _ = (rest.reverse.dropWhile (char => char == ' ') ++ [second, first]).reverse :=
      rewrite dropWhileBefore (char => char == ' ') rest.reverse second [first] stops
    _ = [first, second, ..trimChars rest] :=
      rewrite List.reverseAppend (rest.reverse.dropWhile (char => char == ' ')) [second, first]

theorem trimStartsDashes ∀ (chars: List Char)
    (h: Text.startsWithChars ['-', '-'] chars = True):
    Text.startsWithChars ['-', '-'] (trimChars chars) = True :=
  match chars with
    | [only] => cases
    | [first, second, ..rest] =>
      match same1: Text.sameChar '-' first with
        | True =>
          match same2: Text.sameChar '-' second with
            | True =>
              let equal: Char.toNat '-' = Char.toNat second := Nat.equalSound (Char.toNat '-') (Char.toNat second) same2
              let stops: (second == ' ') = False := rewrite <- equal
              rewrite trimCharsSecond first second rest stops

theorem trimSplit ∀ (chars: List Char):
    trimChars chars ++ (chars.reverse.takeWhile (char => char == ' ')).reverse = chars :=
  calc trimChars chars ++ (chars.reverse.takeWhile (char => char == ' ')).reverse
    _ = ((chars.reverse.takeWhile (char => char == ' ')) ++ chars.reverse.dropWhile (char => char == ' ')).reverse :=
      (List.reverseAppend
        (chars.reverse.takeWhile (char => char == ' '))
        (chars.reverse.dropWhile (char => char == ' '))).flipped
    _ = chars.reverse.reverse := rewrite List.takeWhileDropWhile (char => char == ' ') chars.reverse
    _ = chars := List.reverseReverse chars

theorem trimNoNewline ∀ (chars: List Char)
    (h: Text.containsChars ['\n'] chars = False):
    Text.containsChars ['\n'] (trimChars chars) = False :=
  match found: Text.containsChars ['\n'] (trimChars chars) with
    | False => byComputing
    | True =>
      let big :=
        Text.containsCharsAppendLeft
          ['\n']
          (trimChars chars)
          (chars.reverse.takeWhile (char => char == ' ')).reverse
          found
      rewrite trimSplit chars at big then rewrite h at big then cases

--| A comment as the lexer reads it (`--`, no line break) is one the formatter's `commentText` accepts once its
--| trailing spaces are trimmed.
theorem trimmedComment ∀ (text: Text)
    (starts: text.startsWith "--" = True)
    (single: text.contains "\n" = False):
    commentText (trimEnd text) = True :=
  match spaced: text.endsWith " " with
    | False => rewrite starts, single
    | True =>
      let kept := (text.toList.reverseOnto []).dropWhile (char => char == ' ')
      let back: (kept.reverseOnto []).reverseOnto [] = kept := List.reverseReverse kept
      let startsOk := trimStartsDashes text.toList starts
      let singleOk := trimNoNewline text.toList single
      rewrite startsOk, singleOk, back, dropSpacesStart (text.toList.reverseOnto [])

-- From leaves to words: comments.

--| `codeWords` of `Syntax.ParseSettledStatements`, which imports this file.
def wordsOf (leaves: List Leaf): List Word := leaves.filter (leaf => leaf.kind != Comma) |> .map Leaf.word

theorem noteTexts ∀ (comments: List Comment):
    (comments.map (comment => { text = comment.text, blankBefore = comment.blankLines > 0 })).map (note => note.text)
      = comments.map (comment => comment.text) :=
  match comments with
    | [] => byComputing
    | [comment, ..rest] => Eq.cong (tail => [comment.text, ..tail]) (noteTexts rest)

theorem optionTexts ∀ (trailing: Option Comment):
    (trailing.map (comment => comment.text)).toList = optionText trailing :=
  match trailing with
    | None => byComputing
    | Some comment => byComputing

--| A leaf's word holds the comment texts the leaf does.
theorem wordTexts ∀ (leaf: Leaf): leaf.word.comments.texts = triviaTexts leaf.trivia :=
  rewrite noteTexts leaf.trivia.leading, optionTexts leaf.trivia.trailing

theorem leavesCommentTexts ∀ (leaves: List Leaf)
    (all: (leafTexts leaves).all commentText = True):
    leaves.all (leaf => (triviaTexts leaf.trivia).all commentText) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let split :=
        rewrite textsCons leaf rest, allAppendB (triviaTexts leaf.trivia) (leafTexts rest) commentText at all then all
      Bool.andIntro (Bool.andLeft split) (leavesCommentTexts rest (Bool.andRight split))

theorem wordsCommentTexts ∀ (leaves: List Leaf)
    (all: leaves.all (leaf => (triviaTexts leaf.trivia).all commentText) = True):
    (wordsOf leaves).all (word => word.comments.texts.all commentText) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match comma: leaf.kind != Comma with
        | False => wordsCommentTexts rest (Bool.andRight all)
        | True =>
          Bool.andIntro (rewrite wordTexts leaf then Bool.andLeft all) (wordsCommentTexts rest (Bool.andRight all))

-- From leaves to words: closers homed.

--| `Leaf.marked` of `Syntax.ParseSettledStatements`: a leaf's text says whether it is a closer and whether it is `->`
--| as its kind does.
def isMarked (leaf: Leaf): Bool :=
  isCloserText leaf.token.text == leaf.token.kind.isCloser
    && (operatorTok leaf.token.text == Some Arrow) == (leaf.token.kind == Arrow)

theorem eqOfBeq ∀ (a b: Bool) (h: (a == b) = True): a = b := cases

theorem wordsOfComma ∀ (leaf: Leaf) (rest: List Leaf)
    (isComma: (leaf.token.kind == Comma) = True):
    wordsOf [leaf, ..rest] = wordsOf rest :=
  rewrite isComma

theorem wordsOfItem ∀ (leaf: Leaf) (rest: List Leaf)
    (notComma: (leaf.token.kind == Comma) = False):
    wordsOf [leaf, ..rest] = [leaf.word, ..wordsOf rest] :=
  rewrite notComma

theorem wordTrails ∀ (leaf: Leaf): leaf.word.trails = leaf.trivia.trailing.isSome := match leaf.trivia.trailing with
  | None => byComputing
  | Some comment => byComputing

theorem wordNoted ∀ (leaf: Leaf): leaf.word.noted = !leaf.trivia.leading.isEmpty := match leaf.trivia.leading with
  | [] => byComputing
  | [comment, ..rest] => byComputing

theorem endsOnStep ∀ (leaf: Leaf) (earlier: List Leaf):
    endsOn [leaf, ..earlier]
      = (leaf.trivia.trailing.isSome || (!(earlier.isEmpty || !passable leaf) && endsOn earlier)) :=
  match some: leaf.trivia.trailing.isSome with
    | True => byComputing
    | False =>
      match empty: earlier.isEmpty || !passable leaf with
        | True => byComputing
        | False => byComputing

theorem noneNotSome ∀ (option: Option Comment) (none: option.isNone = True): option.isSome = False := match option with
  | None => byComputing

theorem stopOfPassable ∀ (empty passes: Bool) (h: (!(empty || !passes)) = True): passes = True := cases

theorem orFalseLeft ∀ (a b: Bool) (h: (a || b) = True) (off: a = False): b = True := cases

theorem orNotTrue ∀ (a b: Bool) (h: (a || !b) = True) (on: b = True): a = True := cases

theorem endsOnTrailsComma ∀ (leaf: Leaf) (earlier: List Leaf)
    (isComma: (leaf.token.kind == Comma) = True)
    (ends: endsOn [leaf, ..earlier] = True)
    (bare: bareComma leaf = True)
    (rec: endsOn earlier = True → trailsBack (wordsOf earlier) = True):
    trailsBack (wordsOf [leaf, ..earlier]) = True :=
  let step: (leaf.trivia.trailing.isSome || (!(earlier.isEmpty || !passable leaf) && endsOn earlier)) = True :=
    rewrite endsOnStep leaf earlier at ends then ends
  let kept :=
    orNotTrue (leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone) (leaf.token.kind == Comma) bare isComma
  let notSome: leaf.trivia.trailing.isSome = False := noneNotSome leaf.trivia.trailing (Bool.andRight kept)
  let rest :=
    orFalseLeft leaf.trivia.trailing.isSome (!(earlier.isEmpty || !passable leaf) && endsOn earlier) step notSome
  rewrite wordsOfComma leaf earlier isComma then rec (Bool.andRight rest)

theorem endsOnTrailsItem ∀ (leaf: Leaf) (earlier: List Leaf)
    (notComma: (leaf.token.kind == Comma) = False)
    (ends: endsOn [leaf, ..earlier] = True)
    (marked: isMarked leaf = True)
    (rec: endsOn earlier = True → trailsBack (wordsOf earlier) = True):
    trailsBack (wordsOf [leaf, ..earlier]) = True :=
  let step: (leaf.trivia.trailing.isSome || (!(earlier.isEmpty || !passable leaf) && endsOn earlier)) = True :=
    rewrite endsOnStep leaf earlier at ends then ends
  let item := wordsOfItem leaf earlier notComma
  match some: leaf.trivia.trailing.isSome with
    | True => rewrite item then Bool.orLeft (rewrite wordTrails leaf then some)
    | False =>
      let rest :=
        orFalseLeft leaf.trivia.trailing.isSome (!(earlier.isEmpty || !passable leaf) && endsOn earlier) step some
      let passes := stopOfPassable earlier.isEmpty (passable leaf) (Bool.andLeft rest)
      let closer: leaf.token.kind.isCloser = True :=
        orFalseLeft (leaf.token.kind == Comma) leaf.token.kind.isCloser passes notComma
      let marker := eqOfBeq (isCloserText leaf.token.text) leaf.token.kind.isCloser (Bool.andLeft marked)
      let word: isCloserText leaf.token.text = True := rewrite closer at marker then marker
      rewrite item then Bool.orRight (Bool.andIntro word (rec (Bool.andRight rest)))

--| `trailsBack` of the words of leaves, newest first: a comment ends the line wherever rule 1 would put one, since
--| commas hold none (the leaves are settled), and the closers are the words that are closers.
theorem endsOnTrails ∀ (older: List Leaf)
    (ends: endsOn older = True)
    (bare: older.all bareComma = True)
    (marked: older.all isMarked = True):
    trailsBack (wordsOf older) = True :=
  match older with
    | [leaf, ..earlier] =>
      let rec := (more => endsOnTrails earlier more (Bool.andRight bare) (Bool.andRight marked))
      match isComma: leaf.token.kind == Comma with
        | True => endsOnTrailsComma leaf earlier isComma ends (Bool.andLeft bare) rec
        | False => endsOnTrailsItem leaf earlier isComma ends (Bool.andLeft marked) rec

theorem someNotNone ∀ (option: Option Comment) (some: option.isSome = True): option.isNone = False := match option with
  | Some comment => byComputing

theorem homedCore ∀ (tr cl ct lead em wem ls ends tb: Bool)
    (there: (!tr || (!cl || em || (ls && (!lead || ends)))) = True)
    (marker: (ct == cl) = True)
    (empty: (!em || wem) = True)
    (trails: (!ends || tb) = True):
    (!(ct && tr) || wem || !lead || tb) = True :=
  match tr with
    | False => cases
    | True =>
      match cl with
        | False => rewrite eqOfBeq ct False marker
        | True =>
          rewrite eqOfBeq ct True marker then
            match em with
              | True => rewrite empty
              | False =>
                match lead with
                  | False => cases
                  | True => cases

theorem wordsEmpty ∀ (leaves: List Leaf) (empty: leaves.isEmpty = True): (wordsOf leaves).isEmpty = True :=
  match leaves with | [] => byComputing

theorem noneIsNot ∀ (option: Option Comment): option.isNone = !option.isSome := match option with
  | None => byComputing
  | Some comment => byComputing

theorem orAndLeft ∀ (x a b: Bool) (h: (x || (a && b)) = True): (x || a) = True := cases

--| A closer that keeps a trailing comment stops rule 1's walk, in the leaves, so it has own-line comments or follows
--| code that ends with a comment, which the words say too.
theorem homedWordsLeaf ∀ (leaf: Leaf) (earlier: List Leaf)
    (there: homedLeaf leaf earlier = True)
    (marked: isMarked leaf = True)
    (bare: earlier.all bareComma = True)
    (markedEarlier: earlier.all isMarked = True):
    (!(isCloserText leaf.word.text && leaf.word.trails)
      || (wordsOf earlier).isEmpty
      || leaf.word.noted
      || trailsBack (wordsOf earlier))
      = True :=
  let thereNone: (leaf.trivia.trailing.isNone || (!leaf.token.kind.isCloser || earlier.isEmpty || stopsAt leaf earlier))
    = True :=
    orAndLeft _ _ _ there
  let tr: (!leaf.trivia.trailing.isSome
    || (!leaf.token.kind.isCloser
      || earlier.isEmpty
      || (leaf.token.lineStart && (!leaf.trivia.leading.isEmpty || endsOn earlier))))
    = True :=
    rewrite noneIsNot leaf.trivia.trailing at thereNone then thereNone
  let marker: (isCloserText leaf.token.text == leaf.token.kind.isCloser) = True := Bool.andLeft marked
  let empty: (!earlier.isEmpty || (wordsOf earlier).isEmpty) = True := match e: earlier.isEmpty with
    | True => rewrite wordsEmpty earlier e
    | False => byComputing
  let trails: (!endsOn earlier || trailsBack (wordsOf earlier)) = True := match e: endsOn earlier with
    | True => rewrite endsOnTrails earlier e bare markedEarlier
    | False => byComputing
  let core :=
    homedCore leaf.trivia.trailing.isSome leaf.token.kind.isCloser
      (isCloserText leaf.token.text)
      leaf.trivia.leading.isEmpty
      earlier.isEmpty
      (wordsOf earlier).isEmpty
      leaf.token.lineStart
      (endsOn earlier)
      (trailsBack (wordsOf earlier))
      tr
      marker
      empty
      trails
  rewrite wordTrails leaf, wordNoted leaf then core

--| A closer's trailing comment is where rule 1 leaves it: homed as the leaves read it, so homed as the words read
--| it (K1's `homed`, whose look back sees no commas).
theorem homedWords ∀ (older: List Leaf)
    (homed: homedBehind older = True)
    (bare: older.all bareComma = True)
    (marked: older.all isMarked = True):
    homedBack (wordsOf older) = True :=
  match older with
    | [] => byComputing
    | [leaf, ..earlier] =>
      let more := homedWords earlier (Bool.andRight homed) (Bool.andRight bare) (Bool.andRight marked)
      match isComma: leaf.token.kind == Comma with
        | True => more
        | False =>
          Bool.andIntro
            (homedWordsLeaf leaf earlier
              (Bool.andLeft homed)
              (Bool.andLeft marked)
              (Bool.andRight bare)
              (Bool.andRight marked))
            more

-- From leaves to words: `->` bare.

theorem arrowsBareCons ∀ (word: Word) (words: List Word)
    (notArrow: ((operatorTok word.text != Some Arrow): Bool) = True)
    (rest: arrowsBare words = True):
    arrowsBare [word, ..words] = True :=
  match words with
    | [] => byComputing
    | [next, ..more] => Bool.andIntro (Bool.orLeft notArrow) rest

theorem followFacts ∀ (kind: Tok) (h: arrowFollow kind = False): (kind == Comma) = False ∧ (kind == Arrow) = False := (
  Bool.orFalseLeft (kind == Comma) kind.isCloser (Bool.orFalseLeft (passableKind kind) (kind == Arrow) h),
  Bool.orFalseRight (passableKind kind) (kind == Arrow) h
)

theorem notTrue ∀ (b: Bool) (h: (!b) = True): b = False := cases

theorem notNotOr ∀ (a b: Bool) (h: (!a || !b) = True) (on: a = True): b = False := cases

theorem orFalseR ∀ (a b: Bool) (h: (a || b) = True) (off: b = False): a = True := cases

theorem arrowsWordsPlain ∀ (first: Leaf) (rest: List Leaf)
    (notComma: (first.token.kind == Comma) = False)
    (notArrow: (first.token.kind == Arrow) = False)
    (marked: isMarked first = True)
    (ih: arrowsBare (wordsOf rest) = True):
    arrowsBare (wordsOf [first, ..rest]) = True :=
  let marker := eqOfBeq (operatorTok first.token.text == Some Arrow) (first.token.kind == Arrow) (Bool.andRight marked)
  let notOperator: (operatorTok first.token.text == Some Arrow) = False := rewrite notArrow at marker then marker
  rewrite wordsOfItem first rest notComma then arrowsBareCons first.word (wordsOf rest) (rewrite notOperator) ih

theorem arrowsWordsArrow ∀ (first next: Leaf) (more: List Leaf)
    (notComma: (first.token.kind == Comma) = False)
    (leafArrows: (first.trivia.trailing.isNone && (next.trivia.leading.isEmpty || next.token.kind == Arrow)) = True)
    (plain: (!arrowFollow next.token.kind) = True)
    (ih: arrowsBare (wordsOf [next, ..more]) = True):
    arrowsBare (wordsOf [first, next, ..more]) = True :=
  let follow: arrowFollow next.token.kind = False := notTrue _ plain
  let (nextComma, nextNotArrow) := followFacts next.token.kind follow
  let own := Bool.andLeft leafArrows
  let noOwn: next.trivia.leading.isEmpty = True := orFalseR _ _ (Bool.andRight leafArrows) nextNotArrow
  let noTrail: first.trivia.trailing.isSome = False := noneNotSome first.trivia.trailing own
  let rest := rewrite wordsOfItem next more nextComma at ih then ih
  rewrite wordsOfItem first [next, ..more] notComma, wordsOfItem next more nextComma then
    Bool.andIntro
      (Bool.orRight (Bool.andIntro (rewrite wordTrails first, noTrail) (rewrite wordNoted next, noOwn)))
      rest

theorem arrowsWordsSingle ∀ (leaf: Leaf): arrowsBare (wordsOf [leaf]) = True :=
  match isComma: leaf.token.kind == Comma with
    | True => byComputing
    | False => byComputing

--| `->` keeps no comment after it as the leaves say it, so as the words say it: no comma follows a `->` (`plain`),
--| so the token after it is the word after it.
theorem arrowsWords ∀ (leaves: List Leaf)
    (arrows: Syntax.SettleProofs.arrowsBare leaves = True)
    (plain: plainFrom (tokens leaves) = True)
    (marked: leaves.all isMarked = True):
    arrowsBare (wordsOf leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] =>
      match rest with
        | [] => arrowsWordsSingle first
        | [next, ..more] =>
          let ih :=
            arrowsWords
              [next, ..more]
              (Bool.andRight arrows)
              (plainTail first [next, ..more] plain)
              (Bool.andRight marked)
          match isComma: first.token.kind == Comma with
            | True => ih
            | False =>
              match isArrow: first.token.kind == Arrow with
                | False => arrowsWordsPlain first [next, ..more] isComma isArrow (Bool.andLeft marked) ih
                | True => arrowsWordsArrow first next more isComma (Bool.andLeft arrows) (Bool.andLeft plain) ih

-- Reading the leaves the other way round.

theorem andSwap ∀ (a b c: Bool): (a && (b && c)) = (b && (a && c)) := cases

theorem allReverseOnto ∀ (xs acc: List a) (p: a → Bool): (xs.reverseOnto acc).all p = (xs.all p && acc.all p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc (rest.reverseOnto [x, ..acc]).all p
        _ = (rest.all p && [x, ..acc].all p) := allReverseOnto rest [x, ..acc] p
        _ = ([x, ..rest].all p && acc.all p) := cases

theorem textsReverseOnto ∀ (q: Text → Bool) (xs acc: List Leaf):
    (leafTexts (xs.reverseOnto acc)).all q = ((leafTexts xs).all q && (leafTexts acc).all q) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc (leafTexts (rest.reverseOnto [x, ..acc])).all q
        _ = ((leafTexts rest).all q && (leafTexts [x, ..acc]).all q) := textsReverseOnto q rest [x, ..acc]
        _ = ((leafTexts rest).all q && ((triviaTexts x.trivia).all q && (leafTexts acc).all q)) :=
          rewrite textsCons x acc, allAppendB (triviaTexts x.trivia) (leafTexts acc) q
        _ = ((triviaTexts x.trivia).all q && ((leafTexts rest).all q && (leafTexts acc).all q)) := andSwap _ _ _
        _ = ((leafTexts [x, ..rest]).all q && (leafTexts acc).all q) :=
          rewrite textsCons x rest, allAppendB (triviaTexts x.trivia) (leafTexts rest) q then cases

theorem laidOnto ∀ (behind rest: List Leaf)
    (back: laidBack behind = True)
    (fwd: laidOut (pendB behind) rest = True):
    laidOut False (behind.reverseOnto rest) = True :=
  match behind with
    | [] => fwd
    | [leaf, ..older] =>
      laidOnto older
        [leaf, ..rest]
        (Bool.andRight (Bool.andRight back))
        (Bool.andIntro (Bool.andLeft back) (Bool.andIntro (Bool.andLeft (Bool.andRight back)) fwd))

theorem plainOfJoin ∀ (out: List Leaf) (join: plainJoin out [] = True): plain1 (tokens (out.reverseOnto [])) = True :=
  match out with
    | [] => byComputing
    | [newest, ..older] =>
      plainOfBack
        (tokens ([newest, ..older].reverseOnto []))
        (rewrite tokensReverseOnto [newest, ..older] [], List.reverseReverse (tokens [newest, ..older]) then
          Bool.andLeft join)

--| `isMarked`, of the token alone.
def markedToken (token: Token): Bool :=
  isCloserText token.text == token.kind.isCloser && (operatorTok token.text == Some Arrow) == (token.kind == Arrow)

theorem markedTokens ∀ (leaves: List Leaf): leaves.all isMarked = (tokens leaves).all markedToken := match leaves with
  | [] => byComputing
  | [leaf, ..rest] => rewrite markedTokens rest

theorem wordsOfReverseOnto ∀ (xs acc: List Leaf):
    wordsOf (xs.reverseOnto acc) = (wordsOf xs).reverseOnto (wordsOf acc) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match isComma: x.token.kind == Comma with
        | True =>
          calc wordsOf (rest.reverseOnto [x, ..acc])
            _ = (wordsOf rest).reverseOnto (wordsOf [x, ..acc]) := wordsOfReverseOnto rest [x, ..acc]
            _ = (wordsOf rest).reverseOnto (wordsOf acc) := rewrite wordsOfComma x acc isComma
        | False =>
          calc wordsOf (rest.reverseOnto [x, ..acc])
            _ = (wordsOf rest).reverseOnto (wordsOf [x, ..acc]) := wordsOfReverseOnto rest [x, ..acc]
            _ = (wordsOf rest).reverseOnto [x.word, ..wordsOf acc] := rewrite wordsOfItem x acc isComma

theorem allTrimmed ∀ (texts: List Text)
    (raw: texts.all (text => text.startsWith "--" && !text.contains "\n") = True):
    (texts.map trimEnd).all commentText = True :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      Bool.andIntro
        (trimmedComment text (Bool.andLeft (Bool.andLeft raw)) (Bool.andRight (Bool.andLeft raw)).read)
        (allTrimmed rest (Bool.andRight raw))

-- The end of the file.

theorem intoTrailing ∀ (carry: Carried) (trivia: Trivia): (carry.into trivia).trailing = trivia.trailing :=
  match trivia with
    | { leading, blankLines, trailing } =>
      match leading with
        | [] => byComputing
        | [first, ..more] => byComputing

--| Rule 2 leaves the end's trailing comment as it was: a carried comment goes in front of the own-line ones.
theorem commasEndTrailing ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    (commasFrom done carried rest end).end.trailing = end.trailing :=
  match rest with
    | [] =>
      match carried with
        | None => byComputing
        | Some held => intoTrailing held end
    | [leaf, ..after] =>
      let step := (x: Leaf) (next: Option Carried) => commasEndTrailing [x, ..done] next after end
      match carried with
        | None =>
          match commaCarries leaf.trivia with
            | None => step leaf None
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry)
                | False => step leaf None
        | Some held =>
          let received := { leaf | trivia = held.into leaf.trivia }
          match commaCarries received.trivia with
            | None => step received None
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry)
                | False => step received None

theorem noneOf ∀ (option: Option Comment) (none: option.isNone = True): option = None := match option with
  | None => byComputing

--| No trailing comment comes out where none went in.
theorem settledEndNone ∀ (lexed: Lexed)
    (none: lexed.end.trailing.isNone = True):
    lexed.settled.end.trailing.isNone = True :=
  let homed := homeFrom [] None lexed.leaves
  let kept: (commasFrom [] None homed lexed.end).end.trailing = None :=
    Eq.trans (commasEndTrailing [] None homed lexed.end) (noneOf lexed.end.trailing none)
  match trailing: (commasFrom [] None homed lexed.end).end.trailing with | None => byComputing

theorem wordsOfCons ∀ (leaf: Leaf) (first second: List Leaf)
    (same: wordsOf first = wordsOf second):
    wordsOf [leaf, ..first] = wordsOf [leaf, ..second] :=
  match isComma: leaf.token.kind == Comma with
    | True => same
    | False => Eq.cong (tail => [leaf.word, ..tail]) same

--| Dropping the last commas drops no word: a comma is no word.
theorem wordsOfDropF ∀ (behind rest: List Leaf): wordsOf (dropF behind rest) = wordsOf rest := match rest with
  | [] => byComputing
  | [leaf, ..after] =>
    match after with
      | [] => wordsOfCons leaf (dropF [leaf, ..behind] []) [] byComputing
      | [closer, ..after2] =>
        match pair: lastPair closer.token.kind leaf behind with
          | True =>
            let isComma: (leaf.token.kind == Comma) = True := Bool.andLeft pair
            rewrite wordsOfComma leaf [closer, ..after2] isComma then
              wordsOfCons closer
                (dropF [closer, leaf, ..behind] after2)
                after2
                (wordsOfDropF [closer, leaf, ..behind] after2)
          | False =>
            wordsOfCons leaf
              (dropF [leaf, ..behind] [closer, ..after2])
              [closer, ..after2]
              (wordsOfDropF [leaf, ..behind] [closer, ..after2])

theorem endTexts ∀ (trivia: Trivia): trivia.comments.texts = triviaTexts trivia :=
  rewrite noteTexts trivia.leading, optionTexts trivia.trailing

theorem endAfterNone ∀ (trivia: Trivia) (none: trivia.trailing.isNone = True): trivia.comments.after.isNone = True :=
  match trivia.trailing with | None => byComputing

-- The leaves the formatter parses, read as words, are settled.

--| `settledWords`, `Lexed.wordsSettled1` of `Syntax.ParseSettledStatements` for the leaves rule N makes bare
--| (`settledOnce`).
def settledWordsOf (words: List Word): Bool :=
  homedBack words.reverse && arrowsBare words && words.all (word => word.comments.texts.all commentText)

--| The words of the leaves are settled, and so is the end.
def settledLexed (lexed: Lexed): Bool :=
  settledWordsOf (wordsOf lexed.leaves) && lexed.end.comments.texts.all commentText && lexed.end.comments.after.isNone

theorem settledFrom ∀ (once bare: Lexed)
    (wordsEq: wordsOf once.leaves = wordsOf bare.leaves)
    (endEq: once.end = bare.end)
    (homed: homedBack (wordsOf bare.leaves).reverse = True)
    (arrows: arrowsBare (wordsOf bare.leaves) = True)
    (texts: (wordsOf bare.leaves).all (word => word.comments.texts.all commentText) = True)
    (endTexts: bare.end.comments.texts.all commentText = True)
    (after: bare.end.comments.after.isNone = True):
    settledLexed once = True :=
  rewrite wordsEq, endEq then
    Bool.andIntro (Bool.andIntro homed (Bool.andIntro arrows texts)) (Bool.andIntro endTexts after)

--| The leaves the formatter parses, `settledOnce`, are settled as words: closers homed, `->` bare, every comment as
--| rule N leaves it, and the end likewise. For leaves of slice 1's alphabet that are `plain`, laid out as the lexer lays
--| them out, each token's text agreeing with its kind (`isMarked`), with comments `--` to the end of a line.
--|
--| Proof idea: `settledOnce` is `settledBare` with last commas, all bare, left in (`bareSettles`), and a comma is no
--| word, so the words are those of `settledBare`, rule N on `withoutLastCommas` of the leaves. That keeps the leaves
--| laid out, `plain`, in the alphabet and `marked`, and every comment's text (`laidWithout`, `plainWithout`,
--| `allTokensWithout`, `textsWithout`: a last comma that is laid out and `plain` starts no line and holds no own-line
--| comment, so only its trailing comment moves, to the leaf before). So rule N's facts apply to it: `settledHomed`,
--| `settledArrowsBare1`, `settledCommasBare`, `settledKeepsComments`. They are said of leaves; the words' versions
--| follow (`homedWords`: a closer's look back passes only bare commas, and `endsOnTrails` reads a comment ending the
--| line off the words; `arrowsWords`: no comma follows a `->`; `trimmedComment`: a trimmed `--` comment is a
--| `commentText`).
theorem onceSettledProved ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True)
    (laid: laidOut False lexed.leaves = True)
    (marked: lexed.leaves.all isMarked = True)
    (raw: (lexedTexts lexed).all (text => text.startsWith "--" && !text.contains "\n") = True)
    (noTrailing: lexed.end.trailing.isNone = True):
    settledLexed lexed.settledOnce = True :=
  let leaves := lexed.leaves
  let plainF := plainFromOf (tokens leaves) plain
  let out := withoutR [] leaves
  let swapped: withoutLastCommas [] leaves = out.reverseOnto [] := withoutFromR [] leaves
  let lexedB: Lexed := { lexed | leaves = withoutLastCommas [] lexed.leaves }
  let laidB: laidOut False lexedB.leaves = True :=
    rewrite swapped then laidOnto out [] (laidWithout [] leaves byComputing laid plainF) byComputing
  let plainB: plain1 (tokens lexedB.leaves) = True :=
    rewrite swapped then plainOfJoin out (plainWithout [] leaves plain plainF)
  let tokensB: ∀ (q: Token → Bool) (kept: (tokens leaves).all q = True) => (tokens lexedB.leaves).all q = True :=
    q kept =>
      rewrite swapped, tokensReverseOnto out [], allReverseOnto (tokens out) [] q then
        Bool.andIntro (allTokensWithout q [] leaves plainF byComputing kept) byComputing
  let withinB: alphabet1 lexedB.leaves = True := tokensB (token => token.kind.within1) within
  let markedB: lexedB.leaves.all isMarked = True :=
    rewrite markedTokens lexedB.leaves then tokensB markedToken (rewrite <- markedTokens leaves then marked)
  let rawSplit :=
    rewrite leavesTextsSplit leaves lexed.end,
        allAppendB (leafTexts leaves) (triviaTexts lexed.end) (text =>
          text.startsWith "--" && !text.contains "\n") at raw then
      raw
  let rawLeavesB: (leafTexts lexedB.leaves).all (text => text.startsWith "--" && !text.contains "\n") = True :=
    rewrite swapped, textsReverseOnto (text => text.startsWith "--" && !text.contains "\n") out [] then
      Bool.andIntro
        (textsWithout
          (text => text.startsWith "--" && !text.contains "\n")
          []
          leaves
          byComputing
          laid
          plainF
          byComputing
          (Bool.andLeft rawSplit))
        byComputing
  let rawB: (lexedTexts lexedB).all (text => text.startsWith "--" && !text.contains "\n") = True :=
    rewrite leavesTextsSplit lexedB.leaves lexedB.end,
        allAppendB (leafTexts lexedB.leaves) (triviaTexts lexedB.end) (text =>
          text.startsWith "--" && !text.contains "\n") then
      Bool.andIntro rawLeavesB (Bool.andRight rawSplit)
  let settled := lexedB.settled
  let homedS := settledHomed lexedB withinB laidB plainB
  let bareS := settledCommasBare lexedB
  let tokensS: tokens settled.leaves = tokens lexedB.leaves := settledKeepsTokens lexedB
  let plainS: plainFrom (tokens settled.leaves) = True := rewrite tokensS then plainFromOf (tokens lexedB.leaves) plainB
  let markedS: settled.leaves.all isMarked = True :=
    rewrite markedTokens settled.leaves, tokensS, <- markedTokens lexedB.leaves then markedB
  let arrowsS := settledArrowsBare1 lexedB withinB
  let textsS: (lexedTexts settled).all commentText = True :=
    rewrite settledKeepsComments lexedB withinB laidB then allTrimmed (lexedTexts lexedB) rawB
  let (leavesEq, endEq) := bareSettles lexed within plain
  let wordsEq: wordsOf lexed.settledOnce.leaves = wordsOf settled.leaves :=
    Eq.trans (wordsOfDropF [] lexed.settledOnce.leaves).flipped (rewrite leavesEq)
  let reversedWords := wordsOfReverseOnto settled.leaves []
  let bareR: (settled.leaves.reverseOnto []).all bareComma = True :=
    rewrite allReverseOnto settled.leaves [] bareComma then Bool.andIntro bareS byComputing
  let markedR: (settled.leaves.reverseOnto []).all isMarked = True :=
    rewrite allReverseOnto settled.leaves [] isMarked then Bool.andIntro markedS byComputing
  let homedWordsS: homedBack (wordsOf settled.leaves).reverse = True :=
    rewrite <- reversedWords then homedWords (settled.leaves.reverseOnto []) homedS bareR markedR
  let textsSplit :=
    rewrite leavesTextsSplit settled.leaves settled.end,
        allAppendB (leafTexts settled.leaves) (triviaTexts settled.end) commentText at textsS then
      textsS
  let wordTextsS := wordsCommentTexts settled.leaves (leavesCommentTexts settled.leaves (Bool.andLeft textsSplit))
  let endTextsS: lexedB.settled.end.comments.texts.all commentText = True :=
    rewrite endTexts lexedB.settled.end then Bool.andRight textsSplit
  let afterNone := endAfterNone lexedB.settled.end (settledEndNone lexedB noTrailing)
  settledFrom lexed.settledOnce settled wordsEq endEq homedWordsS
    (arrowsWords settled.leaves arrowsS plainS markedS)
    wordTextsS
    endTextsS
    afterNone

--| The hypotheses of `trimStartsDashes` and `trimmedComment` hold of a comment with spaces at its end.
theorem trimStartsDashesWitness: Text.startsWithChars ['-', '-'] (trimChars "-- x  ".toList) = True :=
  trimStartsDashes "-- x  ".toList byComputing

theorem trimmedCommentWitness: commentText (trimEnd "-- x  ") = True := trimmedComment "-- x  " byComputing byComputing
