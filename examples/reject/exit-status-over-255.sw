-- expect-error: E-AUTO-FALSE
-- An exit status is 0 to 255: a larger number means different things on
-- different systems, so it is refused when the program is checked.
import Std (ExitStatus, IO)

def main(): {IO} ExitStatus := ExitStatus.of 300
