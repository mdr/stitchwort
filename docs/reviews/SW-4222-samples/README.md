# SW-4222 samples

The ported sample for [the Lean and Rocq comparison](../SW-4222-lean-rocq-comparison.md): 21 slice 1 theorems on
cut-down definitions. Neither file is part of any build or test.

- `Sample.lean`: Lean 4.35.0, core and `Std` only. Check: `nix shell nixpkgs#lean4 -c lean Sample.lean`
  (no output means it checked; about 1.3 s).
- `Sample.v`: Rocq 9.1.1 with Stdlib 9.0.0. Check, with both from Nix:
  `rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib Sample.v`, where `rocq` is from
  `nixpkgs#rocq-core` and `<stdlib>` is the store path of `nixpkgs#rocqPackages.stdlib` (about 0.8 s).
