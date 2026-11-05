--| The parser reads exactly the puzzle's format: each line of the input is a
--| person's, the letters `a` to `z` of the questions they answered "yes"
--| to, or blank (groups are what lies between the blank lines). If it reads
--| `input`, each non-blank line gives a person whose set of answers has
--| exactly the line's letters.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Std (Bool, Char, Eq, Fail, List, Option, Parse, Result, Set, Text)

--| A person's line: at least one letter, all questions, and the person's
--| answers hold those letters and no others.
def PersonWritten (read: List Char) (person: Person): Prop :=
  read ≠ [] ∧ read.all isQuestion = True ∧ ((question: Char) → person.answers.contains question = read.contains question)

theorem eachLetters: (read: List Char) → (letters: List Char) → Parse.Each (letter char => letter = [char] ∧ isQuestion char = True) read letters →
    read = letters ∧ letters.all isQuestion = True
  | read, [], each => Both each rfl
  | read, [letter, ..rest], Witness first (Witness after (Both split (Both (Both one question) more))) =>
    match eachLetters after rest more with
      | Both same questions => Both (rewrite split, one, same in rfl) (rewrite question, questions in rfl)

theorem containsFromList (letters: List Char) (question: Char): (Set.fromList letters).contains question = letters.contains question :=
  Bool.eqOf _ _
    (found => (List.memContains letters question).backward ((Set.containsFromListIff letters question).forward found))
    (found => (Set.containsFromListIff letters question).backward ((List.memContains letters question).forward found))

theorem readsPerson: Parse.Reads person PersonWritten :=
  Parse.readsThen _ _ _ _
    (Parse.readsMany1 _ _ (Parse.readsSatisfy _ _)) (lettersRead letters (Both each nonEmpty) =>
      match eachLetters lettersRead letters each with
        | Both same questions =>
          Parse.readsDone ({ answers = Set.fromList letters }: Person) _
            (rewrite List.appendNil lettersRead, same in
              Both (nonEmpty) (Both questions (question => containsFromList letters question))))

--| A line: a person's, or nothing but spaces and tabs.
def LineWritten (read: List Char): Option Person → Prop
  | Some person => PersonWritten read person
  | None => read.all Parse.isSpace = True

theorem readsAnswers: Parse.Reads answers LineWritten :=
  Parse.readsThen _ _ _ _ readsPerson (read person written =>
    Parse.readsDone (Some person) _ (rewrite List.appendNil read in written))

theorem readsBlank: Parse.Reads blank LineWritten :=
  Parse.readsThen _ _ _ _ Parse.readsSpaces (read u spaces =>
    Parse.readsDone (None: Option Person) _ (rewrite List.appendNil read in spaces))

theorem readsLine: Parse.Reads line LineWritten := Parse.readsOneOf LineWritten [answers, blank] (Both readsAnswers (Both readsBlank ()))

--| If `parseLines` reads `input`, each of its lines is a person's, or
--| blank.
theorem parseWritten (input: Text) (values: List (Option Person)) (parsed: Fail.toResult (() => parseLines input) = Ok values):
    List.All2 LineWritten (input.lines.map Text.toList) values :=
  Parse.eachLineReads input line LineWritten values parsed readsLine
