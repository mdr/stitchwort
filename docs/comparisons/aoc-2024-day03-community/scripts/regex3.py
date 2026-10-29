"""The regex solution most of the megathread wrote, as a reference, and its variants.

Usage: python3 -I regex3.py INPUT [REPEAT]

Prints both parts with `\\d{1,3}` and with `\\d+` (the two are the same on
the real input if no `mul` has a longer number), the split trick's part 2,
and the time for the regex parts on the input repeated REPEAT times.
"""
import re
import sys
import time

text = open(sys.argv[1]).read() * (int(sys.argv[2]) if len(sys.argv) > 2 else 1)


def parts(pattern):
    p1 = p2 = 0
    on = True
    for m in re.finditer(pattern, text):
        if m.group(0) == "do()":
            on = True
        elif m.group(0) == "don't()":
            on = False
        else:
            n = int(m.group(1)) * int(m.group(2))
            p1 += n
            p2 += n if on else 0
    return p1, p2


t = time.perf_counter()
bounded = parts(r"mul\((\d{1,3}),(\d{1,3})\)|do\(\)|don't\(\)")
dt = time.perf_counter() - t
print("{1,3}", bounded, f"{dt*1000:.1f} ms")
print("\\d+  ", parts(r"mul\((\d+),(\d+)\)|do\(\)|don't\(\)"))
print("longer numbers in a mul:", len(re.findall(r"mul\(\d{4,},|,\d{4,}\)", text)))
kept = "".join([chunk.split("do()", 1)[1] if i and "do()" in chunk else ("" if i else chunk)
                for i, chunk in enumerate(text.split("don't()"))])
print("split trick part 2:", sum(int(a) * int(b) for a, b in re.findall(r"mul\((\d{1,3}),(\d{1,3})\)", kept)))
