--| Day 19's puzzle examples: the first's rules and messages, and the
--| second's, whose count changes once rules 8 and 11 can repeat.

namespace Aoc.Year2020.Day19.Tests
import Aoc.Year2020.Day19 (..)
import Std (Fail, List, Nat, Result, Text)

def parsed (input: Text): Result Received Text := Fail.toResult (() => parseReceived input)

def matching (input: Text): Result (List Text) Text := (parsed input).map (received =>
  received.messages.filter received.rules.matchesCompletely |> .map (message => Text.fromList message.letters))

def example1: Text := """
  0: 4 1 5
  1: 2 3 | 3 2
  2: 4 4 | 5 5
  3: 4 5 | 5 4
  4: "a"
  5: "b"

  ababbb
  bababa
  abbbab
  aaabbb
  aaaabbb
  """

def example2: Text := """
  42: 9 14 | 10 1
  9: 14 27 | 1 26
  10: 23 14 | 28 1
  1: "a"
  11: 42 31
  5: 1 14 | 15 1
  19: 14 1 | 14 14
  12: 24 14 | 19 1
  16: 15 1 | 14 14
  31: 14 17 | 1 13
  6: 14 14 | 1 14
  2: 1 24 | 14 4
  0: 8 11
  13: 14 3 | 1 12
  15: 1 | 14
  17: 14 2 | 1 7
  23: 25 1 | 22 14
  28: 16 1
  4: 1 1
  20: 14 14 | 1 15
  3: 5 14 | 16 1
  27: 1 6 | 14 18
  14: "b"
  21: 14 1 | 1 14
  25: 1 1 | 1 14
  22: 14 14
  8: 42
  26: 14 22 | 1 20
  18: 15 15
  7: 14 5 | 1 21
  24: 14 1

  abbbbbabbbaaaababbaabbbbabababbbabbbbbbabaaaa
  bbabbbbaabaabba
  babbbbaabbbbbabbbbbbaabaaabaaa
  aaabbbbbbaaaabaababaabababbabaaabbababababaaa
  bbbbbbbaaaabbbbaaabbabaaa
  bbbababbbbaaaaaaaabbababaaababaabab
  ababaaaaaabaaab
  ababaaaaabbbaba
  baabbaaaabbaaaababbaababb
  abbbbabbbbaaaababbbbbbaaaababb
  aaaaabbaabaaaaababaa
  aaaabbaaaabbaaa
  aaaabbaabbaaaaaaabbbabbbaaabbaabaaa
  babaaabbbaaabaababbaabababaaab
  aabbbbbaabbbaaaaaabbbbbababaaaaabbaaabba
  """

test "the first example, 6 rules and 5 messages" :=
  (parsed example1).map (received => (received.rules.numbered.length, received.messages.length)) == Ok (6, 5)
test "the first example's rule 1" :=
  (parsed example1).map (received => received.rules.rule 1) == Ok (Some (Alternatives [[2, 3], [3, 2]]))
test "the first example, the messages that match" := matching example1 == Ok ["ababbb", "abbbab"]
test "the first example, part 1" := (parsed example1).map .matchingCount == Ok 2

test "the second example, part 1" := (parsed example2).map .matchingCount == Ok 3
test "the second example, part 2" := (parsed example2).map (received => received.withLoops.matchingCount) == Ok 12
test "the second example, part 1's messages" :=
  matching example2 == Ok ["bbabbbbaabaabba", "ababaaaaaabaaab", "ababaaaaabbbaba"]

test "a rule of one alternative of one rule" := (parsed "0: 1\n1: \"a\"\n\na\nb").map .matchingCount == Ok 1
test "a message must match completely" := (parsed "0: 1 1\n1: \"a\"\n\na\naa\naaa").map .matchingCount == Ok 1
test "a rule that refers to itself repeats" := (parsed "0: 1 | 1 0\n1: \"a\"\n\na\naaaa\nab").map .matchingCount == Ok 2
test "the rules are productive" := [example1, example2].all (input =>
  (parsed input).map (received => received.rules.productive && received.withLoops.rules.productive) == Ok True)
test "a rule that comes back to itself without reading isn't productive" :=
  (parsed "0: 0 | 1\n1: \"a\"\n\na").map (received => received.rules.productive) == Ok False
test "such a rule still matches" := (parsed "0: 0 | 1\n1: \"a\"\n\na\naa").map .matchingCount == Ok 1
test "the rules must be followed by a blank line" := not (parsed "0: \"a\"\na").isOk
test "a letter in quotes" := not (parsed "0: a\n\na").isOk
