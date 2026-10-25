-- `Result a e` at the JS boundary (docs/proposals/errors.md §3.6): an
-- ordinary data type with parameters, so it crosses as
-- `{ $tag: "Ok"; value: A } | { $tag: "Err"; error: E }`, and a TypeScript
-- caller checks `r.$tag === "Err"`. An export can't perform `Fail`, but it
-- can handle it and return the `Result`.
--
-- run: parseRange "11-22"
-- run: parseRange "22-11"
-- run: parseRange "11-x"
-- run: parseRange "bad"
-- run: size (Ok ({ from = 3, to = 7 }))
-- run: size (Err "no range")
-- run: sizes ["1-2", "3-5"]
-- run: sizes ["1-2", " 3 - 5 ", "x"]

import Std (Fail, List, Nat, Result, Text)
import Std.Fail (fail, ensure)

type Range = { from: Nat, to: Nat }

-- "11-22" is `{ from = 11, to = 22 }`; spaces around either number are allowed.
def Range.read (t: Text): {Fail} Range :=
  match Text.split t '-' with
    | [a, b] =>
      let from := a.toNatOrFail
      let to := b.toNatOrFail
      ensure (from <= to) "the range '${t}' ends before it starts"
      { from, to }
    | _ => fail "expected a range like 11-22, got '${t}'"

export def parseRange (t: Text): Result Range Text := Fail.toResult (() => Range.read t)

-- A `Result` as an argument, too.
export def size: Result Range Text -> Result Nat Text
  | Ok r => Ok (r.to - r.from + 1)
  | Err m => Err m

export def sizes (ts: List Text): Result (List Nat) Text :=
  Fail.toResult (() => ts.map (t =>
    let r := Range.read t
    r.to - r.from + 1))
