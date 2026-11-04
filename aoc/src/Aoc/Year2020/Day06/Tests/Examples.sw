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

test "not a question" := parsed "ab\nA" == Err "line 2, column 1: expected a question, 'a' to 'z', a blank line or the end of the input, got 'A'"
test "a blank line before the first group" := parsed "\nab" == Err "line 1, column 1: expected a question, 'a' to 'z', got the end of the line"
test "two blank lines" := parsed "ab\n\n\nac" == Err "line 3, column 1: expected a question, 'a' to 'z', got the end of the line"
test "a space in a line" := parsed "ab cd" == Err "line 1, column 3: expected a question, 'a' to 'z', the end of the line or a blank line, got ' '"
