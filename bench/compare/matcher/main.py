import sys

# 2020 day 19: numbered rules, then messages of a's and b's. A rule is a
# letter or alternatives, each a sequence of rule numbers matched one after
# another. A message matches rule 0 completely. The matcher gives every way
# a rule can match a start of the message, as the positions it can end at,
# so a rule that repeats is no special case. Part 2 replaces rules 8 and 11
# with ones that refer to themselves.


def parse_rules(text):
    rules = {}
    for line in text.splitlines():
        number, body = line.split(": ")
        if body.startswith('"'):
            rules[int(number)] = body[1:-1]
        else:
            rules[int(number)] = [
                [int(n) for n in sequence.split(" ")] for sequence in body.split(" | ")
            ]
    return rules


def ends_after(rules, number, message, position):
    """The positions a match of rule `number` at `position` can end at."""
    rule = rules.get(number)
    if rule is None:
        return []
    if isinstance(rule, str):
        if position < len(message) and message[position] == rule:
            return [position + 1]
        return []
    return [
        end
        for sequence in rule
        for end in ends_after_all(rules, sequence, message, position)
    ]


def ends_after_all(rules, sequence, message, position):
    positions = [position]
    for number in sequence:
        positions = [
            end
            for start in positions
            for end in ends_after(rules, number, message, start)
        ]
    return positions


def matching_count(rules, messages):
    return sum(
        len(message) in ends_after(rules, 0, message, 0) for message in messages
    )


rule_text, message_text = sys.stdin.read().split("\n\n")
rules = parse_rules(rule_text)
messages = message_text.split()

print(f"Part 1: {matching_count(rules, messages)}")
rules[8] = [[42], [42, 8]]
rules[11] = [[42, 31], [42, 11, 31]]
print(f"Part 2: {matching_count(rules, messages)}")
