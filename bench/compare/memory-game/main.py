import sys

# Part 1 is turn 2020 and part 2 the turn given as the argument (default
# 30,000,000), of the elves' memory game: the starting numbers, then each
# turn says how long ago the previous number was last spoken before (0 if new).


def number_spoken(starting, turns):
    seen = {number: turn for turn, number in enumerate(starting[:-1], start=1)}
    last = starting[-1]
    for turn in range(len(starting), turns):
        before = seen.get(last)
        seen[last] = turn
        last = 0 if before is None else turn - before
    return last


starting = [int(n) for n in sys.stdin.read().strip().split(",")]
turns = int(sys.argv[1]) if len(sys.argv) > 1 else 30000000
print(f"Part 1: {number_spoken(starting, 2020)}")
print(f"Part 2: {number_spoken(starting, turns)}")
