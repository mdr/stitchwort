import heapq
import sys

# 2024 day 9: a disk map of alternating file and free-space lengths. Part 1
# moves file blocks one at a time from the end into the leftmost free block;
# part 2 moves whole files, highest number first, into the leftmost free
# span to their left that fits. The answer is the checksum: each block's
# position times its file's number, added up.

FREE = None


def blocks_of(lengths):
    blocks = []
    for index, length in enumerate(lengths):
        blocks.extend([index // 2 if index % 2 == 0 else FREE] * length)
    return blocks


def compact_blocks(blocks):
    files = [block for block in blocks if block is not FREE]
    moving = files[::-1]
    count = len(files)
    compacted = []
    taken = 0
    for block in blocks[:count]:
        if block is FREE:
            compacted.append(moving[taken])
            taken += 1
        else:
            compacted.append(block)
    compacted.extend([FREE] * (len(blocks) - count))
    return compacted


def checksum(blocks):
    return sum(position * block for position, block in enumerate(blocks) if block is not FREE)


def layout(lengths):
    """The files as (id, start, length) and the free spans as (start, length)."""
    files = []
    spans = []
    position = 0
    for index, length in enumerate(lengths):
        if index % 2 == 0:
            files.append((index // 2, position, length))
        else:
            spans.append((position, length))
        position += length
    return files, spans


def join_touching(spans):
    joined = []
    for start, length in spans:
        if joined and joined[-1][0] + joined[-1][1] == start:
            joined[-1] = (joined[-1][0], joined[-1][1] + length)
        else:
            joined.append((start, length))
    return joined


class FreeSpace:
    """The free spans' starts, by length: each length has a heap of starts."""

    def __init__(self, spans):
        self.starts = {}
        for start, length in spans:
            self.add(start, length)

    def add(self, start, length):
        if length > 0:
            heapq.heappush(self.starts.setdefault(length, []), start)

    def leftmost_fit(self, length, before):
        """Pops the leftmost span at least `length` long that starts before `before`."""
        best = None
        for span_length, starts in self.starts.items():
            if span_length >= length and starts:
                if best is None or starts[0] < self.starts[best][0]:
                    best = span_length
        if best is None or self.starts[best][0] >= before:
            return None
        return heapq.heappop(self.starts[best]), best

    def move_file(self, file_id, start, length):
        fit = self.leftmost_fit(length, start)
        if fit is None:
            return start
        span_start, span_length = fit
        self.add(span_start + length, span_length - length)
        return span_start


def compact_files(lengths):
    files, spans = layout(lengths)
    free = FreeSpace(join_touching(spans))
    moved = []
    for file_id, start, length in reversed(files):
        moved.append((file_id, free.move_file(file_id, start, length), length))
    return moved


lengths = [int(digit) for digit in sys.stdin.read().strip()]
print(f"Part 1: {checksum(compact_blocks(blocks_of(lengths)))}")
print(
    "Part 2: "
    f"{sum(file_id * sum(range(start, start + length)) for file_id, start, length in compact_files(lengths))}"
)
