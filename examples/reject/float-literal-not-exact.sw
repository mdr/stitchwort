-- expect-error: E-FLOAT-LITERAL
-- A whole literal reads as exact, so one that isn't a double is refused,
-- with the two nearest; `9007199254740993.0` asks for rounding.
import Std (Float)

def between: Float := 9007199254740993

def negativeBetween: Float := -9007199254740993
