import heapq
import sys

# 2021 day 15: the lowest total risk from the top left to the bottom right
# of a cave of risk levels, over the given map (part 1) and over the map
# tiled five times each way, each tile one higher per tile away (part 2).
# Dijkstra's search with a heap as the queue and a dict of the lowest cost
# found so far.


class RiskMap:
    def __init__(self, height, width, level):
        self.height = height
        self.width = width
        self.level = level

    def lowest_risk(self):
        target = (self.height - 1, self.width - 1)
        cost = {(0, 0): 0}
        queue = [(0, 0, 0)]
        while queue:
            risk, row, column = heapq.heappop(queue)
            if (row, column) == target:
                return risk
            if risk > cost[(row, column)]:
                continue
            for next_row, next_column in (
                (row - 1, column),
                (row + 1, column),
                (row, column - 1),
                (row, column + 1),
            ):
                if 0 <= next_row < self.height and 0 <= next_column < self.width:
                    new_risk = risk + self.level(next_row, next_column)
                    if new_risk < cost.get((next_row, next_column), new_risk + 1):
                        cost[(next_row, next_column)] = new_risk
                        heapq.heappush(queue, (new_risk, next_row, next_column))
        return 0


def wrap(level):
    return level - 9 if level > 9 else level


rows = [[int(c) for c in line] for line in sys.stdin.read().split()]
height = len(rows)
width = len(rows[0])

small = RiskMap(height, width, lambda row, column: rows[row][column])
tiled = RiskMap(
    5 * height,
    5 * width,
    lambda row, column: wrap(
        rows[row % height][column % width] + row // height + column // width
    ),
)
print(f"Part 1: {small.lowest_risk()}")
print(f"Part 2: {tiled.lowest_risk()}")
