import sys

# 2024 day 7: calibration equations ("3267: 81 40 27"). Part 1 adds up the
# test values of the equations that some choice of + and * between the
# numbers, evaluated left to right, makes true; part 2 also allows
# concatenation. The last operator is undone from the target: subtract,
# divide or strip digits, leaving what the earlier numbers must make.


def place_value(number):
    return 10 ** len(str(number))


def can_make(operators, numbers, count, target):
    """Whether the first `count` numbers can make `target`."""
    if count == 1:
        return target == numbers[0]
    last = numbers[count - 1]
    earlier = count - 1
    for operator in operators:
        if operator == "+":
            if last <= target and can_make(operators, numbers, earlier, target - last):
                return True
        elif operator == "*":
            if last != 0:
                if target % last == 0 and can_make(operators, numbers, earlier, target // last):
                    return True
            elif target == 0:
                return True
        else:
            place = place_value(last)
            if target % place == last and can_make(operators, numbers, earlier, target // place):
                return True
    return False


def calibration_result(operators, equations):
    return sum(
        test_value
        for test_value, numbers in equations
        if can_make(operators, numbers, len(numbers), test_value)
    )


equations = []
for line in sys.stdin.read().splitlines():
    test_value, numbers = line.split(":")
    equations.append((int(test_value), [int(n) for n in numbers.split()]))

print(f"Part 1: {calibration_result('+*', equations)}")
print(f"Part 2: {calibration_result('+*|', equations)}")
