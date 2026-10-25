# Hand-written native-code experiment

A hand translation of the `Set` insert hot path (`Std.Map.Tree` insert, shape,
rebuild, rotations) into Rust, to bound what native code could buy. Described
in `docs/proposals/native-compilation.md` (section 3, "N1 as built" and
Appendix A). A standalone cargo project: it has its own `[workspace]`, so
workspace builds and tests don't touch it.

## Modes

`setexp <mode> <n>` inserts the keys `(i * 7919) % n` and prints the set size.
Timings go to stderr.

- `uniform`: values are the machine's three-word `Value` enum, compare is an
  indirect call returning an `Ordering` value, and a uniquely owned cell is
  reused in place (as `Unpack`/`CtorReuse` do).
- `ir`: the uniform insert doing what today's IR does (cells freed on the way
  down, `shape` gets clones, `rebuild`'s `Keep` allocates a fresh node).
- `typed`: a `Node` struct with `u64` size and key, unit value erased.
- uninlined: a separate binary, `noinline`, the older `uniform`/`typed` code
  with every helper `#[inline(never)]` (no `ir` mode). Run it the same way:
  `noinline <uniform|typed> <n>`.

## Build and run

```
nix develop -c task native:handwritten
nix develop -c cargo run --release --manifest-path bench/native/handwritten/Cargo.toml --bin setexp -- ir 1000000
```

## Numbers (25 October 2026, from the note)

Inserts only, 1,000,000 keys, mimalloc, rustc 1.99 `opt-level=3`:

| Mode | Inserts |
|---|---:|
| uniform, no inlining (`noinline`) | 0.79-0.87 s |
| uniform | 0.67-0.73 s |
| ir | 1.94 s |
| typed | 0.12 s |

Caveat: measured on a busy machine (load average 24-36 for the `ir` run), so
read them as rough. For comparison the machine took 8.7-9.9 s and Node 3.2 s
on the same inserts.
