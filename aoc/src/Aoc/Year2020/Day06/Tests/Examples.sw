--| Day 6's puzzle examples, and the parser's errors.

namespace Aoc.Year2020.Day06.Tests
import Aoc.Year2020.Day06 (..)
import Std (Fail, List, Nat, Result, Set, Text)

def parsed (input: Text): Result (List Group) Text := Fail.toResult (() => parseGroups input)

def example: Text := "abc\n\na\nb\nc\n\nab\nac\n\na\na\na\na\n\nb"

test "example, the groups" := (parsed example).map (groups => groups.map (group => group.people.length)) == Ok [1, 3, 2, 4, 1]
test "example, anyone" := (parsed example).map (groups => groups.map (group => group.anyone.toList)) == Ok ["abc".toList, "abc".toList, "abc".toList, ['a'], ['b']]
test "example, everyone" := (parsed example).map (groups => groups.map (group => group.everyone.toList)) == Ok ["abc".toList, [], ['a'], ['a'], ['b']]
test "example, part 1" := (parsed example).map solvePart1 == Ok 11
test "example, part 2" := (parsed example).map solvePart2 == Ok 6

test "a person's answers are a set" := (parsed "abca").map (groups => groups.map (group => group.anyone.size)) == Ok [3]
test "a final line break" := (parsed "ab\nac\n").map (groups => (solvePart1 groups, solvePart2 groups)) == Ok (3, 1)
test "windows line breaks" := (parsed "ab\r\nac\r\n\r\na\r\n").map (groups => (solvePart1 groups, solvePart2 groups)) == Ok (4, 2)

test "not a question" := parsed "ab\nA" == Err "line 2, column 1: expected a question, 'a' to 'z' or the end of the line, got 'A'"
test "blank lines before, between and after groups" := (parsed "\n\nab\n\n\n \t\nac\n\n").map (groups => (groups.length, solvePart1 groups)) == Ok (2, 4)
test "a space in a line" := parsed "ab cd" == Err "line 1, column 3: expected a question, 'a' to 'z' or the end of the line, got ' '"
