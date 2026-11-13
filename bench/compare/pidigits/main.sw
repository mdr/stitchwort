-- The Benchmarks Game's pidigits: the first N digits of pi (default 10,000;
-- `-- 30` for a small run), by the unbounded spigot with big `Nat`s, in the
-- layout of the game's output: ten digits a line, then a tab and the count.
import Std (Fail, Int, IO, List, Nat, Text)

--| `accum` goes negative after a digit is taken, so the state is `Int`.
type Spigot = { numer: Int, accum: Int, denom: Int }

--| The digits found so far, newest first, given `fuel` more terms of the
--| series to try and `wanted` more digits to find; `k` terms are taken.
def digitsFrom (fuel: Nat) (k: Nat) (wanted: Nat) (spigot: Spigot) (found: List Nat): List Nat := match fuel with
  | Zero => found
  | Succ rest =>
    if wanted == 0 then found
    else
      let next := k + 1
      let step := (2 * next + 1).toInt
      let accum := (spigot.accum + spigot.numer * 2) * step
      let numer := spigot.numer * next.toInt
      let denom := spigot.denom * step
      if numer > accum then digitsFrom rest next wanted { numer = numer, accum = accum, denom = denom } found
      else
        let digit := (numer * 3 + accum) / denom
        if digit != (numer * 4 + accum) / denom then digitsFrom rest next wanted { numer = numer, accum = accum, denom = denom } found
        else digitsFrom rest next (wanted - 1) { numer = numer * 10, accum = (accum - denom * digit) * 10, denom = denom } [digit.toNat, ..found]

def Spigot.start: Spigot := { numer = 1, accum = 0, denom = 1 }

def line (count: Nat) (row: List Nat): Text :=
  "${Text.joinWith (row.map Nat.toText) ""}\t:${count}"

def main(): {IO, Fail} () :=
  let count := match IO.args() with
    | [] => 10000
    | [text] => Fail.need text.toNat "expected no arguments, or a number of digits"
    | _ => Fail.fail "expected no arguments, or a number of digits"
  let digits := (digitsFrom (6 * count + 100) 0 count Spigot.start []).reverse
  let rows := digits.chunksOf 10
  List.foldLeft rows 0 (shown row =>
    let total := shown + row.length
    IO.print (line total row)
    total)
  ()
