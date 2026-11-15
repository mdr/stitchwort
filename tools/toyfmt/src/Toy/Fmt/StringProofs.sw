--| What the lexer read as a string is a string the printer may write. The
--| lexer's theorem gives a string's text as its quotes around pieces,
--| each an escape or some plain characters (`StringRead`), without saying
--| each plain piece was the longest; `IsString` wants the pieces `many
--| stringSegment` reads, whatever follows the closing quote. Between the
--| two: the characters one at a time (`Piece`), then neighbouring plain
--| ones joined into runs that stop at an escape or the closing quote.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (And, Bool, Eq, List, Option, Pair, Parse, Text, Void)

--| A plain character of a string, or an escape's second character.
type Piece = | PlainPiece (char: Char) | EscapePiece (escaped: Char)

def spellPieces: List Piece → List Char
  | [] => []
  | [PlainPiece char, ..rest] => [char, ..spellPieces rest]
  | [EscapePiece escaped, ..rest] => ['\\', escaped, ..spellPieces rest]

def GoodPieces: List Piece → Prop
  | [] => True
  | [PlainPiece char, ..rest] => isPlainChar char = True ∧ GoodPieces rest
  | [EscapePiece escaped, ..rest] => isEscaped escaped = True ∧ GoodPieces rest

theorem plainPieces ∀ (read: List Char) (later: List Piece)
    (plain: read.all isPlainChar = True)
    (good: GoodPieces later):
    GoodPieces (read.map PlainPiece ++ later)
      ∧ spellPieces (read.map PlainPiece ++ later) = read ++ spellPieces later :=
  match read, plain with
    | [], _ => Both good rfl
    | [char, ..chars], plain =>
      match first: isPlainChar char with
        | True =>
          match plainPieces chars later plain good with
            | Both goodRest same => Both (Both rfl goodRest) (rewrite same in rfl)

--| What the string's pieces read is some characters and escapes.
theorem eachPieces ∀ (segments: List ()) (body: List Char)
    (each: Parse.Each SegmentRead body segments):
    ∃ (pieces: List Piece) => GoodPieces pieces ∧ spellPieces pieces = body :=
  match segments, each with
    | [], none => Witness [] (Both rfl (Eq.sym none))
    | [segment, ..others], Witness first (Witness rest (Both split (Both read more))) =>
      match eachPieces others rest more with
        | Witness later (Both good same) =>
          match read with
            | Inl (Witness escaped (Both isEscape allowed)) =>
              Witness [EscapePiece escaped, ..later] (Both (Both allowed good) (rewrite split, isEscape, same in rfl))
            | Inr plain =>
              match plainPieces first later plain good with
                | Both goodAll spelled =>
                  Witness (first.map PlainPiece ++ later) (Both goodAll (rewrite split, spelled, same in rfl))

--| How the steps for some pieces start, as far as a plain character
--| before them needs to know: no steps for no pieces; for a plain first
--| piece, a first step of plain characters that starts with it, after
--| which no plain character follows.
def Headed: List Piece → List (List Char, ()) → Prop
  | [], steps => steps = []
  | [EscapePiece escaped, ..rest], steps => True
  | [PlainPiece char, ..rest], steps =>
    ∃ (run: List Char) => ∃ (later: List (List Char, ())) => steps = [([char, ..run], ()), ..later]
      ∧ [char, ..run].all isPlainChar = True
      ∧ (∀ (after: List Char) => (Parse.joinReads later ++ (['"'] ++ after)).takeWhile isPlainChar = [])

--| `steps` are the pieces as `many stringSegment` reads them before a
--| closing quote.
def Pieced (pieces: List Piece) (steps: List (List Char, ())): Prop :=
  Parse.joinReads steps = spellPieces pieces
    ∧ (∀ (after: List Char) => Parse.ManyRuns stringSegment steps (['"'] ++ after))
    ∧ Headed pieces steps

theorem plainApart ∀ (first other: Char)
    (plain: isPlainChar first = True)
    (apart: isPlainChar other = False):
    first ≠ other :=
  same =>
    let both: isPlainChar other = True := rewrite <- same in plain
    cases

theorem plainStarts ∀ (char: Char) (rest: List Char)
    (plain: isPlainChar char = True):
    segmentStart [char, ..rest] = Some PlainSegment :=
  segmentStart.eq2 char rest
    (among =>
      match among with
        | Inl same => plainApart char '\\' plain rfl (Eq.sym same)
        | Inr never => never)
    (Both (plainApart char '"' plain rfl) (plainApart char '\n' plain rfl))

theorem plainFirst ∀ (char: Char) (others: List Piece) (steps: List (List Char, ()))
    (plain: isPlainChar char = True)
    (joined: Parse.joinReads steps = spellPieces others)
    (runs: ∀ (after: List Char) => Parse.ManyRuns stringSegment steps (['"'] ++ after))
    (headed: Headed others steps):
    ∃ (longer: List (List Char, ())) => Pieced [PlainPiece char, ..others] longer :=
  let alone: [char].all isPlainChar = True := rewrite plain in rfl
  match others, joined, headed with
    | [], joined, none =>
      Witness
        [([char], ())]
        (Both rfl
          (Both
            (after =>
              Both
                (same => cases)
                (Both
                  (runsPlainSegment char [] (['"'] ++ after) (plainStarts char _ plain) alone rfl)
                  (stringSegmentDeclines after)))
            (Witness [] (Witness [] (Both rfl (Both alone (after => rfl)))))))
    | [EscapePiece escaped, ..more], joined, _ =>
      let ends: ∀ (after: List Char) => (Parse.joinReads steps ++ (['"'] ++ after)).takeWhile isPlainChar = [] :=
        after => rewrite joined in rfl
      Witness
        [([char], ()), ..steps]
        (Both
          (rewrite joined in rfl)
          (Both
            (after =>
              Both
                (same => cases)
                (Both
                  (runsPlainSegment char []
                    (Parse.joinReads steps ++ (['"'] ++ after))
                    (plainStarts char _ plain)
                    alone
                    (ends after))
                  (runs after)))
            (Witness [] (Witness steps (Both rfl (Both alone ends))))))
    | [PlainPiece next, ..more], joined, Witness run (Witness later (Both shape (Both runPlain ends))) =>
      let known: ∀ (after: List Char) => Parse.ManyRuns stringSegment [([next, ..run], ()), ..later] (['"'] ++ after) :=
        after =>
          let ran := runs after
          rewrite shape at ran in ran
      let joinedLater: Parse.joinReads [([next, ..run], ()), ..later] = spellPieces [PlainPiece next, ..more] :=
        rewrite shape at joined in joined
      let allPlain: [char, next, ..run].all isPlainChar = True := rewrite plain in runPlain
      Witness
        [([char, next, ..run], ()), ..later]
        (Both
          (Eq.cong ((tail: List Char) => [char, ..tail]) joinedLater)
          (Both
            (after =>
              Both
                (same => cases)
                (Both
                  (runsPlainSegment char
                    [next, ..run]
                    (Parse.joinReads later ++ (['"'] ++ after))
                    (plainStarts char _ plain)
                    allPlain
                    (ends after))
                  (known after).right.right))
            (Witness [next, ..run] (Witness later (Both rfl (Both allPlain ends))))))

--| Characters and escapes are read by `many stringSegment`, before a
--| closing quote and anything after it, as their plain runs and escapes.
theorem piecesRun ∀ (pieces: List Piece)
    (good: GoodPieces pieces):
    ∃ (steps: List (List Char, ())) => Pieced pieces steps :=
  match pieces, good with
    | [], _ => Witness [] (Both rfl (Both (after => stringSegmentDeclines after) rfl))
    | [EscapePiece escaped, ..others], Both allowed more =>
      match piecesRun others more with
        | Witness steps (Both joined (Both runs headed)) =>
          Witness
            [(['\\', escaped], ()), ..steps]
            (Both
              (rewrite joined in rfl)
              (Both
                (after =>
                  Both
                    (same => cases)
                    (Both (runsEscapeSegment escaped (Parse.joinReads steps ++ (['"'] ++ after)) allowed) (runs after)))
                rfl))
    | [PlainPiece char, ..others], Both plain more =>
      match piecesRun others more with
        | Witness steps (Both joined (Both runs headed)) => plainFirst char others steps plain joined runs headed

--| What the lexer read as a string is a string: its pieces are read whole
--| again, and its second quote closes it, whatever comes after.
theorem stringReadClosed ∀ (text: Text) (read: StringRead text.toList): IsString text := match read with
  | Witness body (Witness segments (Both shape each)) =>
    match eachPieces segments body each with
      | Witness pieces (Both good spelled) =>
        match piecesRun pieces good with
          | Witness steps (Both joined (Both runs headed)) =>
            Witness steps (Both (rewrite shape, joined, spelled in rfl) runs)
