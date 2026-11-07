import sys

# 2024 day 3: corrupted memory with instructions such as mul(44,46) among
# noise. Part 1 adds the products of every well-formed mul; part 2 also
# obeys do() and don't(), which turn the muls after them on and off. The
# memory is scanned a position at a time: at each, try to read an
# instruction exactly (no spaces, one to three digits), and on failure move
# on one character.


def short_number(memory, position):
    """The number of one to three digits at `position` and where it ends."""
    end = position
    while end < len(memory) and end - position < 3 and memory[end] in "0123456789":
        end += 1
    if end == position:
        return None
    return int(memory[position:end]), end


def instruction(memory, position):
    """The instruction at `position` and where it ends, or None."""
    if memory.startswith("mul(", position):
        left = short_number(memory, position + 4)
        if left is not None and memory.startswith(",", left[1]):
            right = short_number(memory, left[1] + 1)
            if right is not None and memory.startswith(")", right[1]):
                return ("mul", left[0], right[0]), right[1] + 1
        return None
    if memory.startswith("do()", position):
        return ("do",), position + 4
    if memory.startswith("don't()", position):
        return ("dont",), position + 7
    return None


def instructions(memory):
    found = []
    position = 0
    while position < len(memory):
        read = instruction(memory, position)
        if read is None:
            position += 1
        else:
            found.append(read[0])
            position = read[1]
    return found


program = instructions(sys.stdin.read())

part1 = sum(i[1] * i[2] for i in program if i[0] == "mul")
print(f"Part 1: {part1}")

enabled = True
total = 0
for i in program:
    if i[0] == "mul":
        if enabled:
            total += i[1] * i[2]
    else:
        enabled = i[0] == "do"
print(f"Part 2: {total}")
