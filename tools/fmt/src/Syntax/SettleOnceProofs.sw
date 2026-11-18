--| Proofs about `settledOnce` (`Syntax/Settle.sw`): the leaves the formatter parses are settled, read as words
--| (SW-4022, `onceWordsSettled1`).

namespace Syntax.SettleOnceProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (
  alphabet1,
  emptyOf,
  laidOut,
  lexedTexts,
  arrowFollow,
  backOk,
  passableKind,
  plain1,
  plainFrom,
  tokens
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
