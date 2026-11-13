--| The converse of `Parse.sw`: lines of brackets are read as the tokens
--| their characters are, and a line is the characters of one list of tokens
--| at most.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Std (Eq, Exists, Fail, List, Parse, Result, Text)

def tokenEntry (which: Token): (Text, Token) := (Text.fromList [which.char], which)

--| `token` on a bracket's own character, whatever follows.
theorem runsToken (rest: List Char) (which: Token): Parse.Runs token [which.char] rest which := match which with
  | Opener Round => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick [] "(" (Opener Round) (allTokens.drop 1 |> .map tokenEntry) rest rfl)
  | Opener Square => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 1 |> .map tokenEntry) "[" (Opener Square) (allTokens.drop 2 |> .map tokenEntry) rest (Both rfl rfl))
  | Opener Curly => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 2 |> .map tokenEntry) "{" (Opener Curly) (allTokens.drop 3 |> .map tokenEntry) rest (Both rfl (Both rfl rfl)))
  | Opener Angle => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 3 |> .map tokenEntry) "<" (Opener Angle) (allTokens.drop 4 |> .map tokenEntry) rest (Both rfl (Both rfl (Both rfl rfl))))
  | Closer Round => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 4 |> .map tokenEntry) ")" (Closer Round) (allTokens.drop 5 |> .map tokenEntry) rest (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))
  | Closer Square => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 5 |> .map tokenEntry) "]" (Closer Square) (allTokens.drop 6 |> .map tokenEntry) rest (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl))))))
  | Closer Curly => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 6 |> .map tokenEntry) "}" (Closer Curly) (allTokens.drop 7 |> .map tokenEntry) rest (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))))
  | Closer Angle => Parse.runsLabel "a bracket" bracket _ rest _ (Parse.runsPick (allTokens.take 7 |> .map tokenEntry) ">" (Closer Angle) [] rest (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl))))))))

--| `token` declines at the end of the input.
theorem declinesTokenEnd: Parse.Declines token [] :=
  Parse.declinesLabel "a bracket" bracket []
    (Parse.declinesPick (allTokens.map tokenEntry) [] (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))))))

--| The rounds of `many token` on a line of these tokens: a token each.
def tokenSteps: List Token → List (List Char, Token)
  | [] => []
  | [which, ..more] => [([which.char], which), ..tokenSteps more]

theorem joinTokenSteps (tokens: List Token): Parse.joinReads (tokenSteps tokens) = tokens.map Token.char :=
  match tokens with
    | [] => rfl
    | [which, ..more] => rewrite joinTokenSteps more in rfl

theorem stepTokens (tokens: List Token): Parse.stepValues (tokenSteps tokens) = tokens := match tokens with
  | [] => rfl
  | [which, ..more] => rewrite stepTokens more in rfl

theorem tokenManyRuns (tokens: List Token): Parse.ManyRuns token (tokenSteps tokens) [] := match tokens with
  | [] => declinesTokenEnd
  | [which, ..more] =>
    Both (List.consNotNil which.char [])
      (Both (runsToken (Parse.joinReads (tokenSteps more) ++ []) which) (tokenManyRuns more))

--| `many token` on the characters of some tokens.
theorem runsLine (chars: List Char) (tokens: List Token) (written: tokens.map Token.char = chars): Parse.Runs (() => Parse.many token) chars [] tokens :=
  let runs := Parse.runsMany token (tokenSteps tokens) [] (tokenManyRuns tokens)
  rewrite joinTokenSteps tokens, stepTokens tokens, written at runs in runs

theorem linesRun (lines: List (List Token)):
    List.All2 (chars tokens => Parse.Runs (() => Parse.many token) chars [] tokens) (lines.map (tokens => tokens.map Token.char)) lines :=
  match lines with
    | [] => Trivial
    | [tokens, ..more] => Both (runsLine (tokens.map Token.char) tokens rfl) (linesRun more)

--| Input whose lines are the characters of these lists of tokens is read as
--| them.
theorem parseComplete (input: Text) (lines: List (List Token)) (written: lines.map (tokens => tokens.map Token.char) = input.lines.map Text.toList):
    Fail.toResult (() => parseLines input) = Ok lines :=
  Parse.runsEachLine input (() => Parse.many token) lines (rewrite <- written in linesRun lines)

--| A line is the characters of at most one list of tokens, because the parser
--| reads it as one and that read is a function of the line.
theorem writtenUnique (chars: List Char) (a: List Token) (b: List Token) (writtenA: a.map Token.char = chars) (writtenB: b.map Token.char = chars): a = b :=
  Result.okInjective
    (Eq.trans (Eq.sym (Parse.runsRun (() => Parse.many token) chars a (runsLine chars a writtenA)))
      (Parse.runsRun (() => Parse.many token) chars b (runsLine chars b writtenB)))
