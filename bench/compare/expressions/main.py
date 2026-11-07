import sys

# 2020 day 18: each line is an expression of numbers, +, * and parentheses;
# the answer is the sum of their values. Part 1: + and * bind equally,
# left to right. Part 2: + binds tighter than *. One recursive-descent
# parser serves both: a precedence lists the operator levels, loosest first,
# and each level is a left-to-right chain of the next level's expressions.
# The parser builds the expression tree, which is then evaluated.

SAME_PRECEDENCE = [["+", "*"]]
ADDITION_FIRST = [["*"], ["+"]]


class Parser:
    def __init__(self, text, levels):
        self.text = text
        self.levels = levels
        self.position = 0

    def expression(self):
        return self.level(0)

    def level(self, depth):
        if depth == len(self.levels):
            return self.operand()
        left = self.level(depth + 1)
        while True:
            for operator in self.levels[depth]:
                spaced = f" {operator} "
                if self.text.startswith(spaced, self.position):
                    self.position += len(spaced)
                    right = self.level(depth + 1)
                    left = ("operation", operator, left, right)
                    break
            else:
                return left

    def operand(self):
        if self.text.startswith("(", self.position):
            self.position += 1
            inner = self.expression()
            if not self.text.startswith(")", self.position):
                raise ValueError(f"expected ) at {self.position}")
            self.position += 1
            return ("parenthesised", inner)
        start = self.position
        while self.position < len(self.text) and self.text[self.position].isdigit():
            self.position += 1
        if start == self.position:
            raise ValueError(f"expected a number at {start}")
        return ("number", int(self.text[start : self.position]))


def parse_line(line, levels):
    parser = Parser(line, levels)
    tree = parser.expression()
    if parser.position != len(line):
        raise ValueError(f"unexpected input at {parser.position}")
    return tree


def value(tree):
    kind = tree[0]
    if kind == "number":
        return tree[1]
    if kind == "parenthesised":
        return value(tree[1])
    _, operator, left, right = tree
    if operator == "+":
        return value(left) + value(right)
    return value(left) * value(right)


lines = sys.stdin.read().splitlines()
for part, levels in ((1, SAME_PRECEDENCE), (2, ADDITION_FIRST)):
    print(f"Part {part}: {sum(value(parse_line(line, levels)) for line in lines)}")
