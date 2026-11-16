--| The lexer's half of the walk's invariant (`Lexer`, CarryProofs.sw):
--| the tokens of a lex that succeeded are at rising offsets, and one that
--| doesn't start its line has no own-line comments above it. Both are
--| facts about `assemble`'s fold over the lexemes, given that every
--| lexeme read something and that a comment runs to the end of its line.

namespace Toy.Fmt.Carry
import Toy.Fmt (..)
import Toy.Fmt.Proofs (LexemeRead, LexemeSpec, lexRead)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (And, Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Void)

-- A comment is followed by a line break.

--| The text left where a comment stopped starts with a line break, if a
--| lexeme starts there at all.
theorem breakAfter ∀ (rest: List Char) (lexeme: Lexeme)
    (stops: rest.takeWhile (char => char != '\n') = [])
    (starts: lexemeStart rest = Some lexeme):
    lexeme = LineBreak :=
  match rest, stops, starts with
    | [char, ..chars], stops, starts =>
      let unfolded: (if char != '\n' then [char, ..chars.takeWhile (other => other != '\n')] else []) = [] := stops
      match differs: ((char != '\n'): Bool) with
        | False =>
          let isBreak: char = '\n' := DecEq.neFalse char '\n' differs
          let known: lexemeStart ['\n', ..chars] = Some lexeme := rewrite <- isBreak then starts
          (Option.someInjective known).flipped

--| The next step, if there is one, is a line break.
def NextBreaks: List (List Char, Lexeme) → Prop
  | [] => True
  | [(read, lexeme), ..later] => lexeme = LineBreak

--| Every step read something, and a comment is followed by a line break
--| or by nothing.
def Lined: List (List Char, Lexeme) → Prop
  | [] => True
  | [(read, lexeme), ..later] => read ≠ [] ∧ (lexeme = CommentLexeme → NextBreaks later) ∧ Lined later

theorem commentBreaks ∀ (read: List Char) (lexeme: Lexeme) (later: List (List Char, Lexeme))
    (isComment: lexeme = CommentLexeme)
    (spec: LexemeSpec (read ++ Parse.joinReads later) read lexeme)
    (others: Parse.LexemesRead LexemeSpec later):
    NextBreaks later :=
  match later, others, spec with
    | [], _, _ => byComputing
    | [(next, following), ..more], found, spec =>
      match found with
        | (nonEmpty, nextSpec, rest) =>
          let shape: read = (read ++ (next ++ Parse.joinReads more)).takeWhile (char => char != '\n') :=
            (rewrite isComment at spec then spec).right
          breakAfter
            (next ++ Parse.joinReads more)
            following
            (List.takeWhileAppendStops (char => char != '\n') read (next ++ Parse.joinReads more) shape)
            nextSpec.left

theorem linedOf ∀ (steps: List (List Char, Lexeme)) (lexemes: Parse.LexemesRead LexemeSpec steps): Lined steps :=
  match steps, lexemes with
    | [], _ => byComputing
    | [(read, lexeme), ..later], found =>
      match found with
        | (nonEmpty, spec, others) =>
          (nonEmpty, (isComment => commentBreaks read lexeme later isComment spec others), (linedOf later others))

-- What `assemble`'s fold keeps.

--| Tokens newest first: each offset below the one before it, the newest
--| below `bound`.
def Falling (bound: Nat): List Tok → Prop
  | [] => True
  | [newest, ..older] => newest.offset < bound ∧ Falling newest.offset older

theorem fallingWeaken ∀ (bound more: Nat) (tokens: List Tok)
    (atMost: bound ≤ more)
    (falling: Falling bound tokens):
    Falling more tokens :=
  match tokens, falling with
    | [], _ => byComputing
    | [newest, ..older], known => ((arithmetic [known.left, atMost]), known.right)

--| The assembly before the lexemes of `later`, the first of them at
--| `bound`: its tokens are below `bound` and tidy, and if something is on
--| the line already, either no trivia waits for the next token or the
--| line ends here.
def Kept (bound: Nat) (later: List (List Char, Lexeme)) (assembly: Assembly): Prop :=
  Falling bound assembly.tokens
    ∧ List.All Tidy assembly.tokens
    ∧ (assembly.lineEmpty = False → assembly.pending = [] ∨ NextBreaks later)

theorem withTrailingFalling ∀ (bound: Nat) (tokens: List Tok) (comment: Parse.Located Comment)
    (falling: Falling bound tokens):
    Falling bound (withTrailing tokens comment) :=
  match tokens, falling with
    | [], _ => byComputing
    | [last, ..earlier], known => known

theorem withTrailingTidy ∀ (tokens: List Tok) (comment: Parse.Located Comment)
    (tidy: List.All Tidy tokens):
    List.All Tidy (withTrailing tokens comment) :=
  match tokens, tidy with
    | [], _ => ()
    | [last, ..earlier], known => (known.left, known.right)

def isLineBreak: Lexeme → Bool
  | LineBreak => True
  | _ => False

theorem notBreak ∀ (lexeme: Lexeme) (other: isLineBreak lexeme = False) (never: lexeme = LineBreak): Void :=
  Bool.trueNotFalse (Eq.trans (Eq.cong isLineBreak never).flipped other)

theorem lengthPositive ∀ (bound: Nat) (read: List Char) (nonEmpty: read ≠ []): bound < bound + read.length :=
  match read, nonEmpty with
    | [], nonEmpty => (nonEmpty byComputing).impossible
    | [char, ..chars], _ => arithmetic []

--| A lexeme that becomes a token: the token is at `bound`, above the
--| others, and tidy, since on a line that has something no trivia waits.
theorem codeKept ∀ (source: Text) (bound: Nat) (read: List Char) (lexeme: Lexeme)
    (later: List (List Char, Lexeme)) (assembly: Assembly)
    (code: isCode lexeme = True)
    (other: isLineBreak lexeme = False)
    (nonEmpty: read ≠ [])
    (kept: Kept bound [(read, lexeme), ..later] assembly):
    Kept (bound + read.length) later (assembly.add source { value = lexeme, offset = bound, length = read.length }) :=
  let quiet: assembly.lineEmpty = False → assembly.pending = [] := busy =>
    match kept.right.right busy with
      | Inl none => none
      | Inr never => (notBreak lexeme other never).impossible
  rewrite addCode assembly source { value = lexeme, offset = bound, length = read.length } code then
    (
      ((lengthPositive bound read nonEmpty), kept.left),
      (
        (starts => Eq.cong ((pending: List Trivia) => pending.reverse.flatMap Trivia.comments) (quiet starts)),
        kept.right.left
      ),
      (busy => Inl byComputing)
    )

--| `Assembly.add` keeps `Kept`, the bound moving past the lexeme.
--|
--| Proof idea: by the lexeme. Spaces change nothing; a line break empties
--| the line; an own-line comment waits for the next token, and the next
--| lexeme is a line break (`breaks`); a trailing comment changes only the
--| newest token's `trailing`; anything else is a token (`codeKept`).
theorem addKept ∀ (source: Text) (bound: Nat) (read: List Char) (lexeme: Lexeme)
    (later: List (List Char, Lexeme)) (assembly: Assembly)
    (nonEmpty: read ≠ [])
    (breaks: lexeme = CommentLexeme → NextBreaks later)
    (kept: Kept bound [(read, lexeme), ..later] assembly):
    Kept (bound + read.length) later (assembly.add source { value = lexeme, offset = bound, length = read.length }) :=
  let further: Falling (bound + read.length) assembly.tokens :=
    fallingWeaken bound (bound + read.length) assembly.tokens (arithmetic []) kept.left
  match lexeme, breaks, kept with
    | Spaces, _, kept => (
      further,
      kept.right.left,
      (busy =>
        match kept.right.right busy with
          | Inl none => Inl none
          | Inr never => (notBreak Spaces byComputing never).impossible)
    )
    | LineBreak, _, kept => (further, kept.right.left, (busy => (Bool.trueNotFalse busy).impossible))
    | CommentLexeme, breaks, kept =>
      let quiet: assembly.lineEmpty = False → assembly.pending = [] := busy =>
        match kept.right.right busy with
          | Inl none => none
          | Inr never => (notBreak CommentLexeme byComputing never).impossible
      match empty: assembly.lineEmpty with
        | True => (further, kept.right.left, (busy => Inr (breaks byComputing)))
        | False => (
          (withTrailingFalling (bound + read.length) assembly.tokens _ further),
          (withTrailingTidy assembly.tokens _ kept.right.left),
          (busy => Inl (quiet byComputing))
        )
    | WordLexeme, _, kept => codeKept source bound read WordLexeme later assembly byComputing byComputing nonEmpty kept
    | DigitsLexeme, _, kept =>
      codeKept source bound read DigitsLexeme later assembly byComputing byComputing nonEmpty kept
    | StringLexeme, _, kept =>
      codeKept source bound read StringLexeme later assembly byComputing byComputing nonEmpty kept
    | SignLexeme, _, kept => codeKept source bound read SignLexeme later assembly byComputing byComputing nonEmpty kept
    | SymbolsLexeme, _, kept =>
      codeKept source bound read SymbolsLexeme later assembly byComputing byComputing nonEmpty kept
    | StrayLexeme, _, kept =>
      codeKept source bound read StrayLexeme later assembly byComputing byComputing nonEmpty kept

--| Folding `Assembly.add` over the steps' lexemes, the first at `bound`,
--| keeps `Kept`.
theorem foldKept ∀ (source: Text) (steps: List (List Char, Lexeme)) (bound: Nat) (assembly: Assembly)
    (lined: Lined steps)
    (kept: Kept bound steps assembly):
    ∃ (end: Nat) => Kept end []
      ((Parse.locatedSteps bound steps).foldLeft assembly (assembly lexeme => assembly.add source lexeme)) :=
  match steps, lined, kept with
    | [], _, kept => (bound, kept)
    | [(read, lexeme), ..later], found, kept =>
      match found with
        | (nonEmpty, breaks, others) =>
          foldKept source later
            (bound + read.length)
            (assembly.add source { value = lexeme, offset = bound, length = read.length })
            others
            (addKept source bound read lexeme later assembly nonEmpty breaks kept)

-- From the fold, newest first, to the tokens in order.

theorem risingSnoc ∀ (tokens: List Tok) (last: Tok)
    (rising: Rising tokens)
    (below: List.All (other => other.offset < last.offset) tokens):
    Rising (tokens ++ [last]) :=
  match tokens, rising, below with
    | [], _, _ => ((), byComputing)
    | [first, ..rest], rising, below => (
      (List.allAppend (other => first.offset < other.offset) rest [last] rising.left ((below.left, ()))),
      (risingSnoc rest last rising.right below.right)
    )

--| Tokens that fall, newest first, rise once reversed, all below the
--| bound.
--|
--| Proof idea: induction on the tokens; the newest goes last, above all
--| the older ones (`risingSnoc`).
theorem fallingRising ∀ (bound: Nat) (tokens: List Tok)
    (falling: Falling bound tokens):
    Rising tokens.reverse ∧ List.All (other => other.offset < bound) tokens.reverse :=
  match tokens, falling with
    | [], _ => (byComputing, ())
    | [newest, ..older], known =>
      match fallingRising newest.offset older known.right with
        | (rising, under) =>
          rewrite List.reverseCons newest older then
            (
              (risingSnoc older.reverse newest rising under),
              (List.allAppend
                (other => other.offset < bound)
                older.reverse
                [newest]
                (List.allImplies
                  (other => other.offset < newest.offset)
                  (other => other.offset < bound)
                  (other lower => arithmetic [lower, known.left])
                  older.reverse
                  under)
                ((known.left, ())))
            )

--| The lexer's tokens are what the walk assumes: tidy, at rising offsets.
--|
--| Proof idea: the lex read the source lexeme by lexeme (`lexRead`), each
--| reading something and each comment followed by a line break
--| (`linedOf`); `assemble`'s fold keeps `Kept` over such lexemes
--| (`foldKept`), and its tokens reversed are tidy and rising.
theorem lexFits ∀ (source: Text) (lexed: Lexed) (lexes: lex source = Ok lexed): Parse.Fits Tok Lexer lexed.tokens :=
  match lexRead source lexed lexes with
    | (steps, joined, lexemesSame, tokensSame, triviaSame, lexemes) =>
      match foldKept source steps 0 Assembly.start
        (linedOf steps lexemes)
        ((byComputing, (), (busy => (Bool.trueNotFalse busy).impossible))) with
        | (end, falling, tidy, settled) =>
          rewrite tokensSame, lexemesSame then
            {
              holds = (
                (List.allReverse Tidy
                  ((Parse.locatedSteps 0 steps).foldLeft Assembly.start (assembly lexeme =>
                    assembly.add source lexeme)).tokens
                  tidy),
                (fallingRising end
                  ((Parse.locatedSteps 0 steps).foldLeft Assembly.start (assembly lexeme =>
                    assembly.add source lexeme)).tokens
                  falling).left
              )
            }
