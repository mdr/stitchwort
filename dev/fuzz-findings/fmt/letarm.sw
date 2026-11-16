def inArm (o: Option Nat): Nat := match o with
  | Some k => let j := k +
-- c
 1; j * 2
