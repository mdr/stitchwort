# mapops

A mix of operations on an ordered map from Nat keys to Nat values, one million
steps. Each step draws `x` from a Park-Miller generator (`x * 48271 mod
2^31-1`, seed 1); the key is `x % 200000` and `(x / 200000) % 10` picks the
operation: 0 to 3 insert, 4 to 6 look up (adds the value found, plus one, to
a checksum), 7 and 8 update (add the step's value to the existing one, else
insert it), 9 remove. The answer is the final size and the checksum after
folding the final map in key order: `166073 25450745`.

Each language uses its standard map (D3342):

- **Stitchwort:** std's `Map` (persistent, ordered): `insert`, `get`,
  `insertWith`, `remove`, `foldLeft`.
- **Python:** `dict`, a hash map, not an ordered one; the stdlib has no
  ordered map, so the final fold sorts the keys once (about 166,000 of
  them). A `dict` is the idiomatic choice and is much faster per operation
  than any ordered structure Python could build.
- **Lean:** `Std.TreeMap` (a balanced tree, ordered like Stitchwort's `Map`),
  not `Std.HashMap`. `Lean.RBMap`, the red-black tree the brief named, is
  deprecated in 4.34 in favour of `Std.TreeMap`.

Unlike `rbmap`, the map here is the library's, not a hand-written tree, so it
measures std's `Map` (and its `Quot` wrapper) as application code meets it.
