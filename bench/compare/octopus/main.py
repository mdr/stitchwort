import sys

# 2021 day 11: octopuses in a grid, each with an energy level. In a step
# every octopus gains 1, and each above 9 flashes, giving 1 more to each of
# the eight around it. The flashers are worked out in rounds: an octopus
# flashes once its level, plus 1, plus the flashers around it so far, is
# above 9, and the rounds go on until one adds nobody. Part 1 counts the
# flashes in 100 steps; part 2 finds the first step in which all flash.

SYNC_LIMIT = 10000


class Cavern:
    def __init__(self, levels):
        self.levels = levels
        self.height = len(levels)
        self.width = len(levels[0])

    def flashers(self):
        # Padded by a border of non-flashers, so the neighbours need no check.
        flashed = [[False] * (self.width + 2) for _ in range(self.height + 2)]
        for _ in range(self.height * self.width):
            next_flashed = [[False] * (self.width + 2) for _ in range(self.height + 2)]
            for row in range(self.height):
                for column in range(self.width):
                    next_flashed[row + 1][column + 1] = (
                        self.energy(flashed, row, column) > 9
                    )
            if next_flashed == flashed:
                break
            flashed = next_flashed
        return flashed

    def energy(self, flashed, row, column):
        around = 0
        for next_row in range(row, row + 3):
            for next_column in range(column, column + 3):
                if flashed[next_row][next_column]:
                    around += 1
        if flashed[row + 1][column + 1]:
            around -= 1
        return self.levels[row][column] + 1 + around

    def step(self):
        flashed = self.flashers()
        return Cavern(
            [
                [
                    0
                    if flashed[row + 1][column + 1]
                    else self.energy(flashed, row, column)
                    for column in range(self.width)
                ]
                for row in range(self.height)
            ]
        )

    def zeros(self):
        return sum(level == 0 for row in self.levels for level in row)

    def all_zero(self):
        return all(level == 0 for row in self.levels for level in row)


cavern = Cavern([[int(c) for c in line] for line in sys.stdin.read().split()])

current = cavern
flashes = 0
for _ in range(100):
    current = current.step()
    flashes += current.zeros()
print(f"Part 1: {flashes}")

current = cavern
first_sync = None
for number in range(1, SYNC_LIMIT + 1):
    current = current.step()
    if current.all_zero():
        first_sync = number
        break
if first_sync is None:
    sys.exit(f"no step within {SYNC_LIMIT} has every octopus flash")
print(f"Part 2: {first_sync}")
