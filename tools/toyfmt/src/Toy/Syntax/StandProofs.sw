--| Lexing from the pieces. A text made of pieces, each shaped as one
--| lexeme and stopping where the next begins (`Stands`), lexes to exactly
--| those lexemes (`standingLex`): the lexer's longest match never runs
--| from one piece into the next. The conditions are about characters
--| only, so the printer's side owes them of what it writes next to what.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (Bool, Eq, List, Option, Parse, Text, Void)

--| `rest` doesn't go on with a character that `passes`: it is empty or
--| its first character fails.
def StopsAt (passes: Char → Bool) (rest: List Char): Prop := match rest with
  | [] => True
  | [char, .._] => passes char = False

theorem stopsTakeWhile ∀ (passes: Char → Bool) (rest: List Char)
    (stops: StopsAt passes rest):
    rest.takeWhile passes = [] :=
  match rest, stops with
    | [], _ => byComputing
    | [char, ..later], fails => rewrite fails

--| `read` is one `lexeme` as the lexer takes it before `rest`: its
--| characters are that lexeme's, and `rest` doesn't continue it. A stray
--| character never stands: nothing is printed as one.
def Stands (lexeme: Lexeme) (read rest: List Char): Prop := match lexeme with
  | Spaces =>
    ∃ (others: List Char) => read = [' ', ..others]
      ∧ others.all (char => char == ' ') = True
      ∧ StopsAt (char => char == ' ') rest
  | LineBreak => read = ['\n']
  --| A comment runs to the end of its line.
  | CommentLexeme =>
    ∃ (others: List Char) => read = ['-', '-', ..others]
      ∧ others.all (char => char != '\n') = True
      ∧ StopsAt (char => char != '\n') rest
  | WordLexeme =>
    ∃ (first: Char) => ∃ (others: List Char) => read = [first, ..others]
      ∧ isWordStart first = True
      ∧ others.all isWordChar = True
      ∧ StopsAt isWordChar rest
  | DigitsLexeme =>
    ∃ (first: Char) => ∃ (others: List Char) => read = [first, ..others]
      ∧ first.isAsciiDigit = True
      ∧ others.all (char => char.isAsciiDigit) = True
      ∧ StopsAt (char => char.isAsciiDigit) rest
  | StringLexeme =>
    ∃ (segments: List (List Char, ())) => read = ['"', ..Parse.joinReads segments ++ ['"']]
      ∧ Parse.ManyRuns stringSegment segments (['"'] ++ rest)
  | SignLexeme => ∃ (mark: Punctuation) => read = [signChar mark] ∧ mark ≠ Defines
  | SymbolsLexeme =>
    ∃ (first: Char) => ∃ (others: List Char) => read = [first, ..others]
      ∧ lexemeStart (read ++ rest) = Some SymbolsLexeme
      ∧ OperatorRun read rest
  | StrayLexeme => False

--| A piece that stands is read by `lexemeAt` as its lexeme, whole and no
--| further.
theorem standsRuns ∀ (lexeme: Lexeme) (read rest: List Char)
    (stands: Stands lexeme read rest):
    Parse.Runs (() => lexemeAt (read ++ rest)) read rest lexeme :=
  match lexeme, stands with
    | Spaces, Witness others (Both same (Both spaces stops)) =>
      rewrite same then runsSpacesLexeme others rest spaces (stopsTakeWhile _ rest stops)
    | LineBreak, same => rewrite same then runsLineBreakLexeme rest
    | CommentLexeme, Witness others (Both same (Both oneLine stops)) =>
      rewrite same then runsCommentLexeme others rest oneLine (stopsTakeWhile _ rest stops)
    | WordLexeme, Witness first (Witness others (Both same (Both starts (Both word stops)))) =>
      rewrite same then runsWordLexeme first others rest starts word (stopsTakeWhile _ rest stops)
    | DigitsLexeme, Witness first (Witness others (Both same (Both digit (Both digits stops)))) =>
      rewrite same then runsDigitsLexeme first others rest digit digits (stopsTakeWhile _ rest stops)
    | StringLexeme, Witness segments (Both same closes) => rewrite same then runsStringLexeme segments rest closes
    | SignLexeme, Witness mark (Both same notDefines) => rewrite same then runsPunctuationLexeme mark rest notDefines
    | SymbolsLexeme, Witness first (Witness others (Both same (Both starts isRun))) =>
      runsSymbolsLexeme read rest starts isRun
    | StrayLexeme, never =>
      match never with
        | ()

--| A piece that stands has at least one character.
theorem standsNonEmpty ∀ (lexeme: Lexeme) (read rest: List Char) (stands: Stands lexeme read rest): read ≠ [] :=
  match lexeme, stands with
    | Spaces, Witness others (Both same _) => rewrite same then (empty => cases)
    | LineBreak, same => rewrite same then (empty => cases)
    | CommentLexeme, Witness others (Both same _) => rewrite same then (empty => cases)
    | WordLexeme, Witness first (Witness others (Both same _)) => rewrite same then (empty => cases)
    | DigitsLexeme, Witness first (Witness others (Both same _)) => rewrite same then (empty => cases)
    | StringLexeme, Witness segments (Both same _) => rewrite same then (empty => cases)
    | SignLexeme, Witness mark (Both same _) => rewrite same then (empty => cases)
    | SymbolsLexeme, Witness first (Witness others (Both same _)) => rewrite same then (empty => cases)
    | StrayLexeme, never =>
      match never with
        | ()

--| Every piece stands before the pieces after it.
def StepsStand: (steps: List (List Char, Lexeme)) → Prop
  | [] => True
  | [(read, lexeme), ..steps] => Stands lexeme read (Parse.joinReads steps) ∧ StepsStand steps

--| Pieces that each stand before the next are what `lexemeAt` reads,
--| lexeme by lexeme.
theorem standingRun ∀ (steps: List (List Char, Lexeme)) (stand: StepsStand steps): Parse.LexemesRun lexemeAt steps :=
  match steps, stand with
    | [], _ => byComputing
    | [(read, lexeme), ..later], Both first others => (
      (standsNonEmpty lexeme read (Parse.joinReads later) first),
      (standsRuns lexeme read (Parse.joinReads later) first),
      (standingRun later others)
    )

--| A source made of pieces that each stand before the next lexes to those
--| pieces as its lexemes, and to the tokens `assemble` makes of them.
theorem standingLex ∀ (source: Text) (steps: List (List Char, Lexeme))
    (reads: source.toList = Parse.joinReads steps)
    (stand: StepsStand steps):
    lex source
      = Ok {
        lexemes = Parse.locatedSteps 0 steps,
        tokens = (assemble source (Parse.locatedSteps 0 steps)).fst,
        endTrivia = (assemble source (Parse.locatedSteps 0 steps)).snd
      } :=
  lexReads source steps reads (standingRun steps stand)

--| An operator run doesn't go on into text that starts with no operator
--| character.
theorem operatorStops ∀ (rest: List Char) (stops: StopsAt isOperatorChar rest): operatorNext rest = False :=
  match rest, stops with
    | [], _ => byComputing
    | [char, ..later], fails =>
      operatorNext.eq3
        [char, ..later]
        (tail same =>
          let head: char = '-' := Eq.cong (chars => chars.headOr ' ') same
          let minus: isOperatorChar '-' = False := rewrite <- head then fails
          Bool.falseNotTrue minus.flipped)
        (other tail same =>
          let head: char = other := Eq.cong (chars => chars.headOr ' ') same
          rewrite <- head then fails)

--| The last character of an operator run before text that starts with no
--| operator character: the run goes on to it (no comment starts there).
theorem lastGoesOn ∀ (char: Char) (rest: List Char)
    (holds: isOperatorChar char = True)
    (stops: StopsAt isOperatorChar rest):
    operatorNext ([char] ++ rest) = True :=
  match rest, stops with
    | [], _ => operatorNext.eq2 char [] (tail isMinus same => cases) holds
    | [next, ..later], fails =>
      operatorNext.eq2 char
        [next, ..later]
        (tail isMinus same =>
          let second: next = '-' := Eq.cong ((chars: List Char) => chars.headOr ' ') same
          let minus: isOperatorChar '-' = False := rewrite <- second then fails
          Bool.falseNotTrue minus.flipped)
        holds

--| A `-` before text that starts with no operator character starts an
--| operator run, not a comment.
theorem minusStarts ∀ (rest: List Char)
    (stops: StopsAt isOperatorChar rest):
    lexemeStart (['-'] ++ rest) = Some SymbolsLexeme :=
  cases

--| One operator character stands before text that starts with none.
theorem oneStands ∀ (char: Char) (rest: List Char)
    (starts: lexemeStart ([char] ++ rest) = Some SymbolsLexeme)
    (holds: isOperatorChar char = True)
    (stops: StopsAt isOperatorChar rest):
    Stands SymbolsLexeme [char] rest :=
  (char, [], byComputing, starts, (lastGoesOn char rest holds stops), (operatorStops rest stops))

--| Two operator characters stand before text that starts with none, if
--| they aren't a comment's `--`.
theorem twoStand ∀ (first second: Char) (rest: List Char)
    (starts: lexemeStart ([first, second] ++ rest) = Some SymbolsLexeme)
    (goesOn: operatorNext ([first, second] ++ rest) = True)
    (holds: isOperatorChar second = True)
    (stops: StopsAt isOperatorChar rest):
    Stands SymbolsLexeme [first, second] rest :=
  (first, [second], byComputing, starts, goesOn, (lastGoesOn second rest holds stops), (operatorStops rest stops))

--| Every operator, as it is spelled, stands before text that starts with
--| no operator character: a space, a name, a number, a bracket. Before a
--| `-` it would not (`- -x` printed `--x` is a comment).
theorem operatorStands ∀ (operator: Operator) (rest: List Char)
    (stops: StopsAt isOperatorChar rest):
    Stands SymbolsLexeme operator.spelling.toList rest :=
  match operator with
    | Or => twoStand '|' '|' rest byComputing byComputing byComputing stops
    | And => twoStand '&' '&' rest byComputing byComputing byComputing stops
    | EqualTo => twoStand '=' '=' rest byComputing byComputing byComputing stops
    | NotEqual => twoStand '!' '=' rest byComputing byComputing byComputing stops
    | LessThan => oneStands '<' rest byComputing byComputing stops
    | LessEqual => twoStand '<' '=' rest byComputing byComputing byComputing stops
    | Append => twoStand '+' '+' rest byComputing byComputing byComputing stops
    | Plus => oneStands '+' rest byComputing byComputing stops
    | Minus => oneStands '-' rest (minusStarts rest stops) byComputing stops
    | Times => oneStands '*' rest byComputing byComputing stops
    | Divide => oneStands '/' rest byComputing byComputing stops
    | Remainder => oneStands '%' rest byComputing byComputing stops

--| The `=` of a declaration or `let` stands before text that starts with
--| no operator character.
theorem definesStands ∀ (rest: List Char) (stops: StopsAt isOperatorChar rest): Stands SymbolsLexeme ['='] rest :=
  oneStands '=' rest byComputing byComputing stops

--| A keyword stands before text that starts with no word character.
theorem keywordStands ∀ (keyword: Keyword) (rest: List Char)
    (stops: StopsAt isWordChar rest):
    Stands WordLexeme keyword.spelling.toList rest :=
  match keyword with
    | FnKeyword => ('f', ['n'], byComputing, byComputing, byComputing, stops)
    | LetKeyword => ('l', ['e', 't'], byComputing, byComputing, byComputing, stops)
    | IfKeyword => ('i', ['f'], byComputing, byComputing, byComputing, stops)
    | ThenKeyword => ('t', ['h', 'e', 'n'], byComputing, byComputing, byComputing, stops)
    | ElseKeyword => ('e', ['l', 's', 'e'], byComputing, byComputing, byComputing, stops)
    | TakesKeyword => ('t', ['a', 'k', 'e', 's'], byComputing, byComputing, byComputing, stops)

--| Brackets, commas and dots stand before anything.
theorem signStands ∀ (mark: Punctuation) (rest: List Char)
    (notDefines: mark ≠ Defines):
    Stands SignLexeme [signChar mark] rest :=
  (mark, byComputing, notDefines)
