-- expect-error: E-INSTANCE-AMBIGUOUS
-- A diamond (docs/proposals/interfaces.md §5.8 (c)): `Both a` contains a
-- `Left a` and a `Right a`, and each of those contains a `Root a`. With a
-- `Both a` in scope there are two routes to a `Root a`, `d.left.root` and
-- `d.right.root`, and nothing in `Both`'s type says they're equal. The
-- accepted neighbour passes one route by name: `viaLeft` in
-- examples/accept/interfaces-by-name.sw.

interface Root (a: Type) =
  { name: a → Text }

interface Left (a: Type) =
  { root: Root a, left: a → Text }

interface Right (a: Type) =
  { root: Root a, right: a → Text }

interface Both (a: Type) =
  { left: Left a, right: Right a }

def named [auto d: Both a] (x: a): Text := Root.name x
