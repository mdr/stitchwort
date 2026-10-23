-- expect-error: E-FLOAT-LITERAL
-- A literal that would be an infinity is refused: write `Float.infinity`.
import Std (Float)

def huge: Float := 1e400

def negativeHuge: Float := -1e400
