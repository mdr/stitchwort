# SW-2298: why `pidigits` is slow, natively and interpreted

A paper investigation (D3343): code and docs read, nothing built or run.
The question was the harness smoke numbers for `pidigits` at 10,000 digits
on the Mac: interpreter 8.1 s, `build --native` 7.6 s, CPython 5.3 s,
compiled Lean 1.0 s.

Marks: **[source]** with a `file:line` is read from the code; **[inferred]**
is reasoning that a profile should confirm. `num-bigint` paths are in
`~/.cargo/registry/src/index.crates.io-*/num-bigint-0.5.1/src/` (written
`nb/` below).

## Short answer

- Both back ends do big-number arithmetic in the same Rust functions,
  `crates/rt/src/prims.rs`, on `num-bigint` 0.5.1. Native code inlines only
  word-sized `Nat` `+ - *` and word-sized comparisons. Every `Int` operation
  calls the runtime's `sw_prim`, which calls the same `prims::eval`. That
  is why native is barely faster than the interpreter.
- The number sizes make the run almost all bignum work. `denom` is the
  product of `2k+1` over about 33,000 terms, which is about 480,000 bits
  (7,500 64-bit limbs) by the end. The numbers are past `num-bigint`'s
  Burnikel-Ziegler threshold (8,192 bits) after about the first 750 terms
  [inferred, arithmetic below].
- Every operation in the loop is big × small, big ± big, a comparison, or a
  big ÷ big with a quotient below 10. All of these are O(n) in a good
  library, so Karatsuba and Toom don't matter here. The gap is a constant
  factor: copies, allocations and a poor division path.

## Where the time goes, ranked

1. **Division does two full divisions, through Burnikel-Ziegler, for a
   one-digit quotient.**
   - `/` on `Int` is `IntDiv`, which calls `euclid`, which calls `trunc`
     [source] `prims.rs:535`, `prims.rs:288`. `trunc` computes `(a / d,
     a % d)` as two separate `num-bigint` operations [source]
     `prims.rs:282`. Each one runs a full `div_rem` [source] `nb/bigint/division.rs`
     (`Div` → `div_rem`), so each `/` in the program does two divisions
     and throws away half of each result.
   - When the dividend has more than 128 limbs and the divisor more than 64,
     `num-bigint` always uses Burnikel-Ziegler [source]
     `nb/biguint/division.rs:343`. That code pads to a power-of-two block
     size, `1 << ilog2(len)` and possibly doubled [source]
     `nb/biguint/division.rs:328`. It shifts to normalise and recurses
     through `div_two_digit_by_one` and `div_three_halves_by_two`, which
     clone, split (`from_slice`) and concatenate halves at every level
     [source] `nb/biguint/division.rs:228-325`. It also starts by cloning
     both operands (`u.clone()`, `d.clone()`) [source]
     `nb/biguint/division.rs:332-336`.
   - The algorithm is built for balanced division. Here the quotient is one
     limb, and Knuth's algorithm D would finish in about one multiply-subtract
     pass plus the normalising shifts. CPython's `x_divrem` and GMP's
     `mpn_tdiv_qr` both scale with the quotient's length, so they do O(n)
     work here [inferred, from those libraries' published designs; not read
     for this note].
   - The loop has two divisions per term on the main path
     (`bench/compare/pidigits/main.sw:23-24`), so this adds up to 4
     Burnikel-Ziegler runs per term. This is the most likely top cost
     [inferred].

2. **Every big operation copies both operands first.**
   - `int2`, the shared path for `Int` `+ - * / %`, calls
     `big(a.to_bigint(), b.to_bigint())` [source] `prims.rs:274`.
     `to_bigint` clones the `BigInt` out of its `Rc` [source]
     `value.rs:217-221`. The `Nat` operations do the same with
     `to_biguint` [source] `prims.rs:174`, `prims.rs:195`, `value.rs:208-213`.
   - So each big `+` or `*` costs one or two heap allocations and memcpys
     of n limbs before any arithmetic happens. `num-bigint` supports
     `&a * &b` and `&a + &b`, so these copies aren't needed.
   - For big × small, `num-bigint` does take the scalar path (`(_,
     &[digit]) => self * digit`, [source] `nb/biguint/multiplication.rs:479`).
     A one-digit value is stored inline with no allocation [source]
     `nb/big_digit.rs:44-47`. So the cost is the clone of the big side, plus
     the scalar pass.
   - The clone has exact capacity. When the product carries into a new
     limb, `scalar_mul` pushes it [source] `nb/biguint/multiplication.rs:424-440`,
     which reallocates and may copy again. With a small random multiplier
     that happens on most multiplies [inferred].
   - CPython allocates the result once and makes one pass.

3. **Comparisons copy both operands.**
   - `numer > accum` reaches `IntLess`, then `int_cmp` [source]
     `prims.rs:569`, `prims.rs:149-153` (the elaboration chain through
     `Int.less`, `crates/elab/src/std/core/Int.sw:103`, is [inferred]).
   - For any big operand, `int_cmp` does `a.to_bigint().cmp(&b.to_bigint())`:
     two allocations and two n-limb copies for a comparison that usually
     settles on length or the top limb. That makes an O(1) operation O(n),
     once per term.

4. **Every result gets a fresh `Rc` box, and old values are freed.**
   - `Value::int` does `Rc::new(n)` for every big result [source]
     `value.rs:180-185`.
   - Nothing is updated in place. Only array operations "consume" their
     operand [source] `crates/rt/src/ir.rs:343-345`. That flag is what
     makes the lowering move a last-use operand in rather than copy it
     [source] `crates/rt/src/code.rs:667-672`. So `x * k`, where `x` is a
     temporary, still allocates a new result. This is one allocation per
     operation, small next to items 1-3 [inferred].

5. **Native call overhead (minor).**
   - `sw_prim` builds a `Vec<&Value>` on the heap for each call [source]
     `crates/rt/src/native_abi.rs:1557`. It is called on the slow path of
     every `Int` operation, because native inlines only `Nat` `+ - *` and
     `divFuel` [source] `crates/native/src/n1.rs:3896-3960`.
   - This costs nanoseconds a call. It doesn't matter against O(n) bignum
     work, but it does matter for word-sized `Int` code. Native has no
     inline word path for `Int` arithmetic at all, only for `Int`
     comparisons (`n1.rs` `test`).

The 7,500-limb figure comes from this estimate. Each term multiplies the
ratio by about 1/2, so a digit takes about 3.3 terms, and 10,000 digits take
about 33,000 terms. log2 of the product of `2j+1` up to k=33,000 is about
k·log2(2k/e), which is about 480,000 bits [inferred].

**Why Lean is 8× faster:** GMP has assembly limb loops, a division whose
cost scales with the quotient, and in-place `mpz` updates. Lean also
reuses objects whose reference count is 1. **Why CPython beats us
despite 30-bit digits:** it divides with Knuth D once per `//`, compares in
O(1), and doesn't copy inputs [inferred].

## Cheapest fixes, ranked by expected gain

All of these are in `crates/rt/src/prims.rs`, plus `value.rs` for helpers.
Because native calls the same functions, every fix speeds up both back
ends. None of them changes the language.

1. **A small-quotient division path, and one `div_rem` instead of `/` and
   `%`.**
   - In `trunc`, call `a.div_rem(d)` (from `num_integer::Integer`, which
     `num-bigint` implements) once. That halves the division cost right
     away. It is about 5 lines.
   - Then, when `a.bits() - d.bits() < 63`, compute the quotient directly.
     Estimate it from the top 128 bits of `a` and the top 64 of `d`, compute
     `r = a - q·d` with one scalar multiply and one subtract, and correct by
     ±1. This replaces Burnikel-Ziegler with about two O(n) passes. It
     needs a property test against `div_rem` on random and edge-case
     operands: signs, exact powers of 2^64, and `d` with a top limb of 1.
   - Expected: the biggest single win, plausibly 2-4× on `pidigits`
     [inferred].
2. **Arithmetic on references: no operand clones.**
   - Change `int2`, `nat_add`, `nat_sub`, `nat_mul`, `int_cmp`,
     `div_fuel` and `IntModNat` to borrow the `Rc` contents. Use `&**a *
     &**b`, or `&**a * small` when one side is `Value::Int` or `Value::Nat`.
   - Keep `int_cmp` free of allocation: compare signs, then `BigInt::cmp` on
     references, and treat a word-sized value against a big one by sign
     alone, as `nat_cmp` already does. This is valid because each number
     has one form (`value.rs:4-6`).
   - Expected: removes 2 allocations and copies per operation. Perhaps
     1.3-1.8× on top of fix 1 [inferred].
3. **Reuse in place where the operand is uniquely held.**
   - Mark `Int` and `Nat` `+ - *` as consuming, so that the lowering moves
     last-use operands in. That means `PrimOp::consumes`, `ir.rs:343`, plus
     the paths that already handle consuming operations: `machine.rs:1176`,
     `n1.rs:3300` and `native_abi.rs:2023`.
   - In `eval_owned`, use `Rc::try_unwrap` and `+=` / `*=` on the unwrapped
     number.
   - In `pidigits`, the chains of temporaries benefit:
     `(accum + numer*2) * step`, `numer*3 + accum` and `(accum - denom*digit)
     * 10`. Values read from record fields don't, because the record still
     holds them.
   - Watch two things. The consuming path in `machine.rs:1174-1179`
     currently skips the step charge ("an array operation has no number
     cost"), so numbers need their `words`-based charge kept
     (`prims.rs:359`). And it must allocate exactly as before wherever the
     alloc-trace tests pin it.
   - Expected: about 10-25% more [inferred]. This is a medium change.
4. **Switch the backend: only if 1-3 leave a big gap to Lean.**
   - `rug` (GMP) would give near-Lean speed. But it is LGPL and a C build,
     and it complicates the static musl `standalone` archive
     (`crates/standalone`).
   - `malachite` is LGPL too.
   - `dashu-int` and `ibig` are MIT/Apache and pure Rust. Whether their
     division adapts to the quotient's size needs checking before choosing
     one.
   - `num-bigint` types run through `value.rs`, `prims.rs`, `wire.rs`,
     `codec.rs` and the elaborator and core crates, so a switch is a
     cross-crate change. I would not start here.
5. **Native: inline the word-sized `Int` `+ - *` path, and make `sw_prim`'s
   operand list a `SmallVec`.**
   - This does nothing for `pidigits`, but helps every `Int`-heavy AoC day
     under `--native`.
   - It is a separate ticket, the same shape as the `Nat` fast path at
     `n1.rs:3896`.

## What to measure

A later build lane would run these, after building the binaries once (the
release build is cached through kache in a worktree):

```sh
# Baseline and after each fix (about 30 s per runner at 3 runs).
nix develop -c task bench:compare -- --runs 3 pidigits

# Where the native binary spends its time: expect num-bigint division
# (div_rem_burnikel_ziegler and its helpers), memcpy and the allocator
# near the top.
nix develop -c cargo run --release -p stitchwort-cli -- \
  build --native bench/compare/pidigits/main.sw -o "$TMPDIR/pidigits"
nix run nixpkgs#samply -- record "$TMPDIR/pidigits" 10000 > /dev/null

# Cheaper check of the division claim alone: 2,000 digits stays mostly
# below the Burnikel-Ziegler sizes for longer. If the gap to CPython is much
# smaller at 2,000 than at 10,000, division is the cost.
python3 bench/compare/pidigits/main.py 2000 > /dev/null   # time both
"$TMPDIR/pidigits" 2000 > /dev/null
```

What would confirm the ranking:
- The share of samples under `div_rem_burnikel_ziegler` and `div_rem` (item
  1).
- The share under `alloc::raw_vec` / `memcpy` called from
  `Value::to_bigint` (items 2-3).
- `Rc::new` and free from `Value::int` (item 4).

After fix 1, the `pidigits` check (`task bench:compare:check`) still has to
match `expected.txt` byte for byte.

## Tickets to file

| Ticket | Model | Estimate |
|---|---|---|
| Bignum division: one `div_rem` in `trunc`, plus a small-quotient path (quotient < 2^63) with property tests against `num-bigint`; profile `pidigits` before and after | Sonnet | 60 min |
| Bignum operands by reference: no clones in `int2`, `nat_*`, `int_cmp`, `div_fuel`, `IntModNat`; allocation-free `int_cmp` | Sonnet (or DeepSeek: well bounded) | 30 min |
| In-place `Int`/`Nat` `+ - *` on a uniquely held operand (consuming prims, keeping the step charge and alloc-trace expectations) | Sonnet | 60 min |
| Native: inline word-sized `Int` `+ - *` fast path; `SmallVec` operands in `sw_prim` | Sonnet | 45 min |
| (Later, only if needed) Survey of bignum backends (`dashu`, `ibig`, `rug`/GMP, `malachite`): licence, static musl build, division by quotient size, size of the migration | Opus, paper lane | 30 min |

No D questions: none of these changes the language. A move to GMP would be
a licensing and build decision for Matt, so that ticket should raise it if
it gets that far.
