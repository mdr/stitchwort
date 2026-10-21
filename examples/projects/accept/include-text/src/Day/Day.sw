-- The path is relative to this file (src/Day/), and may go up to the
-- project folder and into `inputs/`.
namespace Day

def input: Text := include "../../inputs/numbers.txt"

def beside: Text := include "note.txt"

def numbers: List Text := (include "../../inputs/numbers.txt").lines

test "the whole text" := input == "10\n20\n30\n"
test "its lines" := numbers == ["10", "20", "30"]
test "a file beside this one" := beside == "hello\n"
test "unicode survives" := (include "../../inputs/unicode.txt").toList == ['h', 'é', '€']
