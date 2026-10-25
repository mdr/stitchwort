-- Calls it by dot, from another namespace, through an import: on a
-- parameter, and on a variable bound inside a type.
namespace Checks
import Shop (..)

def viaDot (bank: Bank): Nat := bank.total 1

def sameTotal: Prop := (bank: Bank) → bank.total 1 = bank.total 1

test "alias dot call" := viaDot [1, 2] == 4
