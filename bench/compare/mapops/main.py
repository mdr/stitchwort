import sys

# A mix of operations on an ordered map of Nat keys to Nat values, driven by a
# Park-Miller linear congruential generator. Each step draws x; the key is
# x % KEYS and the operation is (x // KEYS) % 10: 0-3 insert, 4-6 lookup,
# 7-8 update (insertWith: add to the existing value, else insert), 9 remove.
# The answer is the final size and a checksum of the lookups and of the final
# map folded in key order. Python's `dict` is a hash map, not an ordered one;
# the stdlib has no ordered map, so the final fold sorts the keys once.

KEYS = 200000
MODULUS = 2147483647
CHECK = 1000000007


class Rng:
    def __init__(self, seed):
        self.state = seed

    def next(self):
        self.state = self.state * 48271 % MODULUS
        return self.state


def run(steps):
    rng = Rng(1)
    table = {}
    check = 0
    for step in range(steps):
        draw = rng.next()
        key = draw % KEYS
        op = draw // KEYS % 10
        value = step % 1000
        if op < 4:
            table[key] = value
        elif op < 7:
            found = table.get(key)
            if found is not None:
                check = (check + found + 1) % CHECK
        elif op < 9:
            table[key] = table.get(key, 0) + value
        else:
            table.pop(key, None)
    for key in sorted(table):
        check = (check * 31 + key * 7 + table[key]) % CHECK
    return len(table), check


steps = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
size, check = run(steps)
print(f"{size} {check}")
