-- Definitions with defaults, one depending on an earlier parameter.
namespace Layout
import Std (Nat, Text)

def padding (text: Text) (width: Nat := text.length + 2): Nat := width - text.length

def label (name: Text) (suffix: Text := ":"): Text := name ++ suffix

def columns (count: Nat) (gap: Nat := 1): Nat := count + gap * (count - 1)
