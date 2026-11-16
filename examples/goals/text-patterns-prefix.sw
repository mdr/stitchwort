-- Goals in a prefix pattern's arm: on a `Text`, `rest` is listed as a text
-- and the text matched is shown as the pattern, `"--" ++ rest`, not as the
-- characters it was split into. On a `List Char`, `rest` is the list.
import Std (Nat, Text)

theorem startAndRest ∀ (t: Text): t = t := match t with
  | "--" ++ rest => ?
  | _ => byComputing

-- A `let` that shadows `rest` leaves the text matched as `"ab" ++ rest✝`.
theorem shadowed ∀ (t: Text): t = t := match t with
  | "ab" ++ rest => (let rest := 1; ?)
  | _ => byComputing

def size: Text → Nat
  | "-" ++ letters if letters.length > 1 => ?
  | _ => 0

def lookahead: List Char → Nat
  | "->" ++ rest => ?
  | _ => 0
