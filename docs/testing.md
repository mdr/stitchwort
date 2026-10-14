# Testing

Stitchwort's guarantees are only as good as the compiler's correctness, so the tests have several layers. Each layer catches mistakes the others can't.

| Layer | Where | What it catches |
|---|---|---|
| **Example programs** | `examples/`, run by `crates/cli/tests/examples.rs` | Whether the language behaves as designed, end to end. Rejections must have the expected error code, and error messages are snapshot-tested. This is the main suite, and it's readable without knowing the implementation. |
| **Kernel tests** | `crates/core/tests/kernel.rs` | The kernel on hand-built core terms, including terms the elaborator never produces. The examples can't do this: they only feed the kernel the elaborator's output, and when the elaborator rejects something first, the kernel never runs. |
| **Kernel fuzzing** | `crates/core/tests/fuzz.rs` | That the kernel never panics. Thousands of random, mostly ill-formed terms must each be accepted or rejected with a diagnostic. |
| **Unit tests** | `#[cfg(test)]` modules (lexer, parser, unifier, rendering) | Internal algorithms on cases the examples don't happen to reach: pattern unification's occurs and scope checks, pruning, layout columns, … |
| **Differential tests** | `crates/cli/tests/extract.rs` | That extracted JS agrees with the reference evaluator, on the `-- run:` lines and on 100 random inputs per export. |
| **Coverage** | `cargo llvm-cov --workspace --summary-only` | Which code no test reaches |
| **Mutation testing** | `cargo mutants` | Code that tests reach but don't really *check*. Each mutant is a small deliberate bug, such as replacing a condition with `true`. A "missed" mutant is a bug no test would notice. |

Random tests use fixed seeds, so every run tests the same cases and a failure can always be reproduced.

## Running

```sh
cargo test                                     # everything (needs `node`; the dev shell has it)
cargo insta review                             # after changing an error message
cargo llvm-cov --workspace --summary-only      # coverage per file
cargo mutants --package stitchwort-core --test-workspace=true --jobs 6   # slow: minutes to an hour
nix flake check                                # build, tests, clippy, rustfmt, as CI would
```

## Writing tests

- **For a language feature, start with example programs.** Add an `accept/` example, and for each way it can go wrong, a `reject/` or `soundness/` example declaring the error code it expects. Pair every rejection with a nearby acceptance, so a check can't pass by rejecting everything.
- **For a kernel rule, also add a kernel test on core terms.** Prove that the kernel enforces the rule *by itself*, not just that the elaborator does.
- **The kernel must never panic.** If a malformed term can make it panic, that's a bug: it should be an `E-MALFORMED` error.
- **For a new export shape or codec, add an extraction example.** The random differential test then exercises it automatically.
- **Before trusting a new test, break the code it tests and watch it fail.** `cargo mutants` does this systematically.
