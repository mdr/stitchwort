-- expect-error: E-TYPE-MISMATCH
-- The text pattern fixes `x`'s type to `Text` only inside the first
-- lambda. The second lambda's parameter reuses `x`'s slot in the context,
-- and its mismatch has nothing to do with the pattern, so it gets no label.
def m: Nat :=
  let p := (fun x => match x with | "a" => 1 | _ => 0, fun (y: Text) => y + 1)
  0
