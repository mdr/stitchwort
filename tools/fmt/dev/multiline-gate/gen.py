#!/usr/bin/env python3
"""Generates slice 1 declarations in many layouts for SW-4121's checks.

Usage: gen.py SEED COUNT MODE OUT.cases
Writes COUNT sources, each ended by a line `###`.
MODE: wild (some line starts break the line rule), legal (none, by this script's port of Fmt.hangs),
long (long names on few lines, so the printer must break), noted (legal, many comments), longnoted.
"""
import random, sys

LOWER = ['a', 'b', 'c', 'f', 'g', 'h', 'x', 'y', 'n', 'foo', 'bar', 'value1', 'go_on']
UPPER = ['A', 'B', 'C', 'Nat', 'List', 'Option', 'Tree']
LONGL = ['computeTheWholeThing', 'anotherRatherLongName', 'yetAnotherVeryLongIdentifier', 'stepFunctionOverLeaves',
         'aNameLongEnoughToMatterALot', 'shortish', 'x']
LONGU = ['SomeVeryLongTypeName', 'AnotherQuiteLongTypeName', 'ResultOfTheWholeComputation', 'T']
NUMS = ['0', '1', '42', '1.5', '10']
CMP = ['==', '!=', '<', '<=', '>', '>=', '≤']
OPENERS = {'(', '['}
CLOSERS = {')', ']'}


class Gen:
    def __init__(self, rng, long):
        self.r = rng
        self.long = long

    def word(self):
        r = self.r
        k = r.random()
        if k < 0.45:
            return [(r.choice(LONGL if self.long else LOWER), False)]
        if k < 0.75:
            return [(r.choice(LONGU if self.long else UPPER), False)]
        return [(r.choice(NUMS), False)]

    def atom(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.6:
            return self.word()
        k = r.random()
        if k < 0.3:
            return [('(', False)] + self.expr(d - 1) + [(')', True)]
        if k < 0.55:
            out = [('(', False)]
            for i in range(r.randint(2, 3)):
                if i:
                    out.append((',', True))
                out += self.expr(d - 1, first_glued=(i == 0))
            return out + [(')', True)]
        if k < 0.65:
            return [('[', False), (']', True)]
        out = [('[', False)]
        for i in range(r.randint(1, 3)):
            if i:
                out.append((',', True))
            out += self.expr(d - 1, first_glued=(i == 0))
        return out + [(']', True)]

    def arg(self, d):
        r = self.r
        if r.random() < 0.12:
            inner = self.atom(d - 1)
            return [(r.choice(['-', '!']), False), (inner[0][0], True)] + inner[1:]
        return self.atom(d - 1)

    def app(self, d):
        out = self.atom(d)
        for _ in range(self.r.choice([0, 0, 0, 0, 1, 1, 2, 4 if self.long else 2])):
            out += self.arg(d)
        return out

    def unary(self, d):
        r = self.r
        k = r.random()
        if k < 0.06:
            return [('-', False), (r.choice(['1', '2.5', '7']), True)] + (self.arg(d) if r.random() < 0.3 else [])
        if k < 0.10:
            inner = self.app(d)
            return [('-', False), (inner[0][0], r.random() < 0.5)] + inner[1:]
        if k < 0.14:
            inner = self.app(d)
            return [('!', False), (inner[0][0], True)] + inner[1:]
        return self.app(d)

    def chain(self, d, ops, sub, p):
        out = sub(d)
        while self.r.random() < p:
            out += [(self.r.choice(ops), False)] + sub(d)
        return out

    def mul(self, d):
        return self.chain(d, ['*', '/', '%'], self.unary, 0.1)

    def add(self, d):
        return self.chain(d, ['+', '-'], self.mul, 0.12)

    def append(self, d):
        return self.chain(d, ['++'], self.add, 0.06)

    def cmp(self, d):
        out = self.append(d)
        if self.r.random() < 0.12:
            out += [(self.r.choice(CMP), False)] + self.append(d)
        return out

    def conj(self, d):
        return self.chain(d, ['&&'], self.cmp, 0.06)

    def disj(self, d):
        return self.chain(d, ['||'], self.conj, 0.06)

    def expr(self, d, first_glued=True, arrows=0.15):
        out = self.disj(d)
        while self.r.random() < arrows:
            out += [(self.r.choice(['->', '->', '->', '→']), False)] + self.disj(d)
        out[0] = (out[0][0], first_glued)
        return out


class Hang:
    """Fmt.HangState, ported, to choose columns that keep the line rule."""

    def __init__(self):
        self.blocks, self.top, self.start, self.glue = [], None, False, False

    def in_force(self):
        for b in self.blocks:
            if b is not None:
                return b
        return self.top if self.top is not None else 0

    def legal(self, text, r):
        if self.glue or text == ',':
            return None
        if text in CLOSERS:
            block = self.blocks[0] if self.blocks else None
            if block is None:
                return r.randint(0, 8)
            return None if block == 0 else r.choice([max(0, block - 2), r.randint(0, block - 1)])
        if text == ':=' and not self.blocks:
            return r.randint(0, 6)
        return self.in_force() + r.choice([1, 2, 2, 2, 4, 7])

    def step(self, text, column, starts):
        fresh = self.start and starts
        if text in CLOSERS:
            self.blocks = self.blocks[1:]
            self.start = self.glue = False
        elif text == ',':
            self.blocks = [None] + self.blocks[1:]
            self.start, self.glue = True, False
        elif text in (':=', ':') and not self.blocks:
            self.blocks, self.top, self.start, self.glue = [], None, True, False
        else:
            if fresh:
                if self.blocks:
                    self.blocks = [column] + self.blocks[1:]
                else:
                    self.top = column
            if text in OPENERS:
                self.blocks = [None] + self.blocks
                self.start = True
            else:
                self.start = False
            self.glue = text in ('->', '→')


def lay(tokens, r, p_break, p_wild, p_note, counter):
    out, column, hang = [], 0, Hang()
    for i, (text, glued) in enumerate(tokens):
        starts = False
        if i == 0:
            starts = True
        elif r.random() < p_break or (out and out[-1].startswith(' --')):
            legal = hang.legal(text, r)
            forced = bool(out and out[-1].startswith(' --'))
            if legal is None or r.random() < p_wild:
                want = r.randint(0, 10) if (p_wild > 0 or forced) else None
            else:
                want = legal
            if want is not None:
                if r.random() < p_note and not forced:
                    counter[0] += 1
                    out.append(' -- t%d' % counter[0])
                out.append('\n')
                if r.random() < p_note * 0.4:
                    out.append('\n')
                for _ in range(r.choice([0, 0, 0, 1, 2]) if r.random() < p_note else 0):
                    counter[0] += 1
                    out.append(' ' * want + '-- o%d\n' % counter[0])
                    if r.random() < 0.15:
                        out.append('\n')
                out.append(' ' * want)
                column, starts = want, True
        if not starts:
            if not glued:
                out.append(' ')
                column += 1
        out.append(text)
        hang.step(text, column, starts)
        column += len(text.encode())
        # A comment after this token, which makes the next one start a line.
        if i + 1 < len(tokens) and r.random() < p_note * 0.25:
            counter[0] += 1
            out.append(' -- e%d' % counter[0])
    if r.random() < p_note:
        counter[0] += 1
        out.append(' -- z%d' % counter[0])
    out.append('\n')
    return ''.join(out)


def declaration(g, r, index):
    name = r.choice(['d', 'e', 'main1', 'theAnswer']) + str(index)
    depth = r.choice([0, 1, 1, 2, 2, 3])
    return [('def', False), (name, False), (':', True)] + g.expr(depth, False, arrows=0.35) + [(':=', False)] \
        + g.expr(depth, False)


def case(r, mode):
    long = mode.startswith('long')
    g = Gen(r, long)
    p_wild = 0.08 if mode == 'wild' else 0.0
    p_note = {'wild': 0.2, 'legal': 0.15, 'long': 0.0, 'noted': 0.6, 'longnoted': 0.4}[mode]
    p_break = r.choice([0.0, 0.02, 0.05]) if long else r.choice([0.1, 0.2, 0.35, 0.6])
    counter = [0]
    out = []
    for index in range(r.choice([1, 1, 1, 2])):
        if r.random() < p_note:
            out.append('-- above\n')
        out.append(lay(declaration(g, r, index), r, p_break, p_wild, p_note, counter))
        if r.random() < 0.3:
            out.append('\n' * r.randint(1, 3))
    if r.random() < p_note * 0.5:
        out.append('-- last\n')
    return ''.join(out)


def main():
    seed, count, mode, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    r = random.Random(seed)
    cases = [case(r, mode) for _ in range(count)]
    with open(path, 'w') as f:
        for c in cases:
            f.write(c + '###\n')


main()
