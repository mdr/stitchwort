-- expect-error: E-ATTRIBUTE
def double: Nat → Nat := (@[js.name "x"] n) => n + n
