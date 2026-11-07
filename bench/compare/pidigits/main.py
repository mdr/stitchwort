import sys


def digits(count):
    numer, accum, denom, k = 1, 0, 1, 0
    found = []
    while len(found) < count:
        k += 1
        step = 2 * k + 1
        accum = (accum + numer * 2) * step
        numer *= k
        denom *= step
        if numer > accum:
            continue
        digit = (numer * 3 + accum) // denom
        if digit != (numer * 4 + accum) // denom:
            continue
        found.append(digit)
        accum = (accum - denom * digit) * 10
        numer *= 10
    return found


count = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
found = digits(count)
for start in range(0, len(found), 10):
    row = found[start : start + 10]
    print("".join(map(str, row)) + "\t:" + str(start + len(row)))
