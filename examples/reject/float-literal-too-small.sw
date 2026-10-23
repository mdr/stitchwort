-- expect-error: E-FLOAT-LITERAL
-- A literal that isn't zero but rounds to zero is refused, negative or not.
import Std (Float)

def tiny: Float := 1e-400

def negativeTiny: Float := -1e-400
