# Which side `+` counts down

*SW-787 (D1770), 29 October 2026. A research note with two prototypes on
branch `worktree-agent-ab2873e951b1e94b8`. Sections 1 to 8 were measured on
`main` at `6d0115d0`, release build, M-series Mac with other lanes running.
D1771 chose (c); §9 is its soundness argument, rewritten after an external
review, and §10 is what was built (SW-787, D1771).*

Labels: **[checked]** I ran it, or read it in the source or tool output;
**[cited]** taken from the linked page; **[inferred]** my reasoning from
checked or cited facts; **[unverified]** from memory, not confirmed.

## 1. The problem

`Nat.add` in `crates/elab/src/std/core/Data.sw` counts down its first
argument **[checked]**:

```
def Nat.add: Nat → Nat → Nat
  | Zero, n => n
  | Succ m, n => Succ (Nat.add m n)
```

So `1 + c` computes to `Succ c`, and `c + 1` doesn't: it stays a stuck call
until something rewrites it. `Nat.mul` counts down its first argument too
(`| Succ m, n => n + Nat.mul m n`) **[checked]**.

Specs and programs write `x + 1` far more often than `1 + x`. Counted with
`grep` over `.sw` files on `main` **[checked]**:

| form | `aoc/src` | std |
|---|---:|---:|
| `x + 1` | 273 | 161 |
| `1 + x` | 20 | 4 |
| `x + 0` | 4 | 22 |
| `0 + x` | 17 | 13 |

The AoC notes report the friction on days 4, 12, 15 and 24
(`aoc/NOTES-2024.md` lines 824, 3567, 4669, 7987) **[checked]**:

- Day 4: every `Ahead` direction needs `rewrite Nat.addZero c,
  Nat.addComm c 1, Nat.addComm c 2, Nat.addComm c 3` before `cases`.
- Day 12: the program was changed to say `Succ position.row` instead of
  `position.row + 1`, so the proofs would compute. The program got worse
  to suit the prover.
- Day 15: `ahead robot direction (i + 1)` needed `Nat.addOne` rewritten in
  at every use.
- Day 24: each bit-by-bit step needed `rewrite (omega: bit + 1 = Succ bit)`.

Elsewhere: `games/rogue/NOTES.md` §2 (`% (most + 1)` needed a proof that
`most + 1 ≠ 0`), and std carries an instance, `Nat.decAddSuccNotZero`,
whose comment says it exists only because `most + 1` doesn't compute
(`core/Arith.sw`) **[checked]**. `docs/core.md` §"Matching on an indexed
family" tells users to declare `Succ n`, not `n + 1`, in an index, because
`n + 1` is stuck (`E-INDEX-STUCK`) **[checked]**.

## 2. How other systems do it

Every claim here is **[cited]** from the linked file at the given tag
(read by a research subagent), unless marked otherwise.

**Lean 4** counts down the **second** argument, the only system here that
does
([Prelude.lean L1887-1890, v4.35.0](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Prelude.lean#L1887-L1890)):

```
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

`Nat.mul` too: `| a, Nat.succ b => Nat.add (Nat.mul a b) a`, the
recursive call on the left (same file, L1908-1911). So `add_succ`,
`add_one` and `add_zero` are `rfl`, and `succ_add` and `zero_add` are
proved by induction
([Nat/Basic.lean L135-153](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/Nat/Basic.lean#L135-L153),
[Core.lean L747](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Core.lean#L747)).

- `n + 1` works as a match pattern because `Nat.add` and `HAdd.hAdd` are
  marked `[match_pattern]` (Prelude.lean L1895-1897).
- Since lean4 PR #3579 (13 March 2024, in v4.8.0), `succ_eq_add_one` is
  `@[simp]`, so `n + 1`, not `Nat.succ n`, is simp's normal form
  ([commit 317adf42](https://github.com/leanprover/lean4/commit/317adf42e92a4dbe07295bc1f0429b61bb8079fe);
  [reference manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/):
  "Using `Nat.succ n` should usually be avoided in favor of `n + 1`").
- The kernel computes `succ`, `add`, `sub`, `mul`, `pow`, `gcd`, `mod`,
  `div`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft` and `shiftRight`
  with GMP, **only when both arguments reduce to literals**; while
  checking definitional equality it tries this only when neither side has
  a free variable
  ([type_checker.cpp L672-703, L1060](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp#L672-L703)).
  So GMP never helps `x + 1` with `x` a variable; the definition does.
- `List.length_append` is not `rfl`: it is proved by induction with
  `simp [ih, Nat.succ_add]`
  ([List/Basic.lean L622-625](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/List/Basic.lean#L622-L625)).
  `Vector` is an `Array` with a size proof, so its index never computes
  ([Vector/Basic.lean L225](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/Vector/Basic.lean#L225)).
  Lean pays the (b) costs of §3 with `simp`.
- No design rationale for the choice was found; the closest is the 2024
  [Zulip thread](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/experiment.20making.20.60succ_eq_add_one.60.20.40.5Bsimp.5D.60.html)
  on the normal form.

**Agda** counts down the **first** argument
([Agda/Builtin/Nat.agda L18-35, v2.8.0.2](https://github.com/agda/agda/blob/v2.8.0.2/src/data/lib/prim/Agda/Builtin/Nat.agda#L18-L35)).
`BUILTIN NATPLUS` uses Haskell integers only for **closed** terms
([built-ins](https://agda.readthedocs.io/en/latest/language/built-ins.html)).
The stdlib proves `+-suc` and `+-identityʳ` by induction
([Properties.agda L543-559](https://github.com/agda/agda-stdlib/blob/v2.4/src/Data/Nat/Properties.agda#L543-L559)),
and `Vec`'s `_++_ : Vec A m → Vec A n → Vec A (m + n)` relies on the
first-argument side
([Vec/Base.agda L108](https://github.com/agda/agda-stdlib/blob/v2.4/src/Data/Vec/Base.agda#L108)).
With `--rewriting`, the manual's own example makes `+` compute on both
sides, which is option (c)
([rewriting](https://agda.readthedocs.io/en/latest/language/rewriting.html)):

```
+zero : m + zero ≡ m
+suc : m + (suc n) ≡ suc (m + n)
{-# REWRITE +zero +suc #-}
```

The manual says rules are safe **only with `--confluence-check`**, and
termination is not checked.

**Rocq** counts down the **first** argument
([Init/Nat.v L47-65, V9.3.0](https://github.com/rocq-prover/rocq/blob/V9.3.0/theories/Corelib/Init/Nat.v#L47-L65));
`plus_n_O` and `plus_n_Sm` are proved by induction
([Peano.v L99-124](https://github.com/rocq-prover/rocq/blob/V9.3.0/theories/Corelib/Init/Peano.v#L99-L124));
`Vector.append` has index `n + p`
([VectorDef.v L190](https://github.com/rocq-prover/stdlib/blob/V9.0.0/theories/Vectors/VectorDef.v#L190)).
Rewrite rules (since 8.20, enabled by `-allow-rewrite-rules`) have the
four-rule both-sides `+` as the manual's example, on a new `Symbol`, not
on `Nat.add`
([rewrite-rules](https://rocq-prover.org/doc/V9.0.0/refman/addendum/rewrite-rules.html)).
The manual calls them "highly experimental": types, confluence and
termination are **not checked**, and enabling them turns off the VM and
native reduction. Binary `positive`, `N` and `Z` are separate types
([BinNums.v](https://github.com/rocq-prover/rocq/blob/V9.3.0/theories/Corelib/Numbers/BinNums.v#L21-L71));
`nat` stays unary.

**Idris 2** counts down the **first** argument; `plusZeroRightNeutral`
and `plusSuccRightSucc` are proved by induction
([Prelude/Types.idr L48-64](https://github.com/idris-lang/Idris2/blob/v0.8.0/libs/prelude/Prelude/Types.idr#L48-L64),
[Data/Nat.idr L454-465](https://github.com/idris-lang/Idris2/blob/v0.8.0/libs/base/Data/Nat.idr#L454-L465)).
`%builtin Natural` makes `Nat` an integer at run time
([builtins](https://idris2.readthedocs.io/en/latest/reference/builtins.html));
that it doesn't change type checking is **[unverified]**.

**Isabelle/HOL** defines `plus_nat` by `primrec` on the **first** argument,
and has both `add_0_right` and `add_Suc_right` as `[simp]` lemmas
([Nat.thy L214-226](https://github.com/isabelle-prover/mirror-isabelle/blob/968581a57388778193d3efa40d940fdbcf4be4f2/src/HOL/Nat.thy#L214-L226)).
HOL has no definitional equality in typing, so the side never blocks a
type **[unverified]** (background knowledge). This is option (e) as a
whole design.

**F\*** (`let nat = x:int{x >= 0}`,
[tutorial](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#boolean-refinement-types))
and **Dafny** (`type nat = n: int | 0 <= n`,
[reference](https://dafny.org/latest/DafnyRef/DafnyRef#5631-type-nat))
make `nat` a subset of `int` and leave arithmetic to the SMT solver, so
there is no recursion side.

**GHC** type-level `+` is a built-in type family that only evaluates
literals; GHC "does not know … the commutativity and associativity of
(+)"
([type literals](https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/type_literals.html#computing-with-type-level-naturals)).
The [ghc-typelits-natnormalise](https://hackage.haskell.org/package/ghc-typelits-natnormalise)
plugin normalises sums of products of literals and variables, then
compares syntactically: option (d), as a plugin to the type checker.

**Papers.** Cockx,
[Type Theory Unchained](https://doi.org/10.4230/LIPIcs.TYPES.2019.2)
(TYPES 2019), is the design of Agda's rewrite rules; Cockx, Tabareau and
Winterhalter, [The Taming of the Rew](https://doi.org/10.1145/3434341)
(POPL 2021), gives the type theory with rewrite rules and the triangle
criterion for confluence that the Rocq manual points to. Allais, McBride
and Boutillier,
[New Equations for Neutral Terms](https://arxiv.org/abs/1304.0809)
(2013), add laws for neutral terms (list monoid, functor and fusion
laws), applied after evaluation gets stuck. They say this is "perfectly
useless for commutativity", and that rules such as `x + suc y ≡ suc (x +
y)` "make neutral terms come unstuck, and so cannot be postponed until
reification": that is, (c) has to be part of evaluation, not a
post-pass, which is what §6 proposes.

**Summary.** Lean alone picks (b). Agda, Rocq, Idris and Isabelle use
(a). Agda and Rocq offer (c) as opt-in rewrite rules, Agda's checked for
confluence on request and Rocq's unchecked. Isabelle is (e) by design.
GHC's plugin is (d). No system makes commutativity definitional in its
kernel.


## 3. What the choice touches here

### Definitional facts

| fact | (a) first arg (today) | (b) second arg (Lean) | (c) both |
|---|---|---|---|
| `0 + n = n` | computes | theorem | computes |
| `n + 0 = n` | theorem (`Nat.addZero`) | computes | computes |
| `Succ m + n = Succ (m + n)` | computes | theorem | computes |
| `m + Succ n = Succ (m + n)` | theorem (`Nat.addSucc`) | computes | computes |
| `x + 1 = Succ x` | theorem (`Nat.addOne`) | computes | computes |
| `x + y = y + x` | theorem | theorem | theorem |
| `(x + y) + z = x + (y + z)` | theorem | theorem | theorem |

All rows are [checked] for (a) and (b) against the definitions in
`Data.sw` on `main` and on the branch; (c) rows are [checked] by running
the prototype in §5 on this file:

```
theorem t1 (x: Nat): x + 1 = Succ x := rfl
theorem t2 (x: Nat): x + 0 = x := rfl
theorem t3 (x: Nat): 0 + x = x := rfl
theorem t4 (m: Nat) (n: Nat): Succ m + n = Succ (m + n) := rfl
theorem t5 (m: Nat) (n: Nat): m + Succ n = Succ (m + n) := rfl
theorem t6 (x: Nat): x + 3 = 3 + x := rfl
theorem t7 (x: Nat) (y: Nat): x + (y + 2) = (x + y) + 2 := rfl
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)
def append: Vec a n → Vec a m → Vec a (n + m)
  | VNil, ys => ys
  | VCons x xs, ys => VCons x (append xs ys)
def appendR: Vec a n → Vec a m → Vec a (m + n)
  | VNil, ys => ys
  | VCons x xs, ys => VCons x (appendR xs ys)
def headPlus: Vec a (n + 1) → a
  | VCons x _ => x
```

On `main` it fails at `t1`, `t2`, `t5`, `t6`, `t7` (`E-REFL`), `appendR`
(`E-TYPE-MISMATCH`) and `headPlus` (`E-INDEX-STUCK`). Under the (c)
prototype every line checks **[checked]**. Under (b), `t3`, `t4` and
`append` would fail instead **[inferred]** from the definition.

### Things that line up with the first argument

Moving to (b) is not free of new friction. Several std definitions put
the recursive part on the left of `+`, which suits (a):

- `List.length (Cons x xs) = Succ (List.length xs)` and `List.append`
  recurses on its first list, so `List.lengthAppend` (`length (xs ++ ys)
  = length xs + length ys`) is `rfl` and one `Eq.cong` under (a). Under (b)
  both of its cases need a lemma (`Nat.zeroAdd`, `Nat.succAdd`)
  **[checked]**: it broke, and the fix is on the branch.
- `List.sum` and `List.sumBy` are `foldLeft` from `0` with `acc + x`
  (`List/Toolkit.sw:80-85`) **[checked]**, so a sum starts `0 + a`. Under
  (a) that computes; under (b) it is stuck. Which side Lean's
  `List.sum` puts the `0` on was not checked **[unverified]**.
- `Vec` append with index `n + m`, in
  `examples/accept/indexed-families.sw`, typechecks only because `+`
  counts down `n`, the first vector's length **[checked]** (the comment
  says so). Under (b) its type must become `Vec a (m + n)`, or the
  definition must recurse on the second vector. std has no `Vec.append`
  **[checked]** (`std/Vec/Vec.sw`).
- Std's division law is written with the quotient on the left of `*`
  (`Succ q * d`); under (b), with `*` also counting down its second
  argument, those goals stop computing **[checked]** (11 of the
  `Nat/Arith.sw` errors). Lean writes the divisor on the left,
  `n % k + k * (n / k) = n` **[unverified]**, which suits its choice.

So each choice favours a set of conventions. (b) favours counters and
indices (`i + 1`); (a) favours structural recursion on lists and the
accumulator-on-the-left fold. Only (c) and (d) stop the choice from
mattering.

### `n + 1` in patterns and indices

Stitchwort has no `n + 1` pattern **[checked]** (no match in std, aoc or
examples; `docs/core.md` §index tells users to write `Succ n`). Under (b)
or (c), an index or a case written `n + 1` computes to `Succ n`, so
`Vec a (n + 1)` can be matched like `Vec a (Succ n)` without new
pattern syntax: unification sees `Succ n` after evaluation. Checked for
(c) by `headPlus` above **[checked]**; for (b) **[inferred]**. A pattern
`n + 1` in a `match` on a `Nat` (Lean's form) would be new syntax under
any option.

### Induction-shaped lemmas

Under (a), proofs by induction go on the left summand; under (b), on the
right. A switch flips them: `addSucc` and `zeroAdd` swap roles with
`succAdd` and `addZero`, `mulSucc` with `succMul`. The prototype's
`core/Arith.sw` shows the shape **[checked]**: every `| Zero, n => … |
Succ m, n => …` proof of an `Add`/`Mul` law becomes `| m, Zero => … | m,
Succ n => …`, and std gains `Nat.zeroAdd`, `Nat.succAdd`, `Nat.zeroMul`,
`Nat.succMul`. `Nat.decAddSuccNotZero` and `Nat.addOne` become `rfl`.

### Runtime and the native backend

At run time `+` and `*` never unfold. The JS backend emits `(m) => (n) =>
m + n` on `bigint` (`crates/js/src/lib.rs:5071`), the Rust runtime folds
`Native::Add` to a literal (`crates/rt/src/opt.rs:809`) **[checked]**. So
the side `+` recurses on doesn't change program speed **[inferred]**.

It matters only while checking, where a number with unknowns is
`Value::NatAdd(k, x)`, "`Succ` applied `k` times to `x`"
(`crates/core/src/native.rs`, module comment) **[checked]**. Under (a),
`add k x` with `k` known becomes `NatAdd(k, x)` in one step; under (b) it
is `add x k`. The prototype for (b) had to swap the argument order in five
places: `native.rs` (the shortcut, `nat_add_term`, `folds_mul`, and which
argument `run` looks at first), `omega.rs` (four quoter cases) and
`ring.rs` (one) **[checked]**. One trap: under (b) with `*` recursing on
its second argument and the recursive call on the right of `+`, `x *
1000000` unfolds a million times, because `+` forces its second argument.
The prototype puts the recursive call on the left (`Nat.mul m n + m`)
**[checked]** (comment in the prototype's `Data.sw`).

### Trust

(a) and (b) are ordinary definitions: the kernel's trust doesn't change.
The natives must still compute exactly what the definition computes
(`native.rs` module comment) **[checked]**, so (b) needs `run_partial`
rewritten for the new side, and `crates/driver/tests/natives.rs` run.

(c) and (d) add equations to the kernel's conversion that aren't the
unfolding of a definition. They are theorems (`Nat.addSucc`,
`Nat.addZero`, and for (d) commutativity and associativity), so they are
consistent (but that alone doesn't make them safe in conversion: §9 has
the argument for (c)), and the kernel must then be trusted to apply them correctly,
and the natives-on and natives-off evaluators must agree on them
(`crates/driver/tests/natives.rs` compares the two on numbers)
**[checked]**. See §5.

### The check cache and content hashes

A change to std or the kernel changes every cache key (the compiler
fingerprint is in every key, `docs/proposals/check-cache.md` §3)
**[checked]**, so either change rechecks everything once. Content hashes
change too: under (b), `Float`'s pinned hashes (`crates/core/src/float.rs`,
`NATIVE_HASHES`) failed, so `Float.add` and the rest weren't bound to their
natives (`E-BUILTIN` "its content hash isn't the pinned one") **[checked]**.
Under (c), with std unchanged, `Float.neg`, `Float.abs` and `Float.sub`
failed the same way **[checked]**: elaborated terms contain values read
back after evaluation, and (c) changes what `x + k` evaluates to
**[inferred]**. Either way the fix is to re-pin (the hash test prints the
new ones), and the `hashes` snapshots change.

## 4. Options

**(a) Keep first-argument recursion.** No migration. The friction in §1
stays. Partial relief from (e).

**(b) Switch to second-argument recursion, as Lean does.** `x + 1`, `x +
0` and every `x + k` compute. `1 + x`, `0 + x` and `Succ m + n` stop
computing. Lemmas about `length`, `sum` and `Vec` append (§3) need a
lemma where they had `rfl`. Ordinary definition: no new kernel trust.
Migration measured in §5.

**(c) Both sides compute.** Keep the definition and add the two missing
equations, `m + Succ n = Succ (m + n)` and `m + 0 = m`, as computation
rules. The four rules (two from the definition, two added) are confluent:
the critical pairs `Zero + Zero`, `Zero + Succ n`, `Succ m + Zero` and
`Succ m + Succ n` each close in one or two steps **[inferred]**, and every
rule makes an argument smaller, so they terminate **[inferred]**. Agda
offers exactly this with `--rewriting`, and Rocq with rewrite rules: both
manuals use this very example (§2).
Everything in §3's table computes except commutativity and associativity.
Costs: the kernel gains a rule that isn't a definition; `+` becomes strict
in its second argument when the first is stuck (it must look at the
second to find a `Succ`).

**(d) Kernel normalisation of `+` on open terms.** Treat `+` on `Nat` as
the kernel already treats `k + x` (`Value::NatAdd`), but extended to a
sum of a literal and a multiset of atoms: `x + 1 + y` and `y + (x + 1)`
would be the same value. Commutativity and associativity become
definitional. Costs: a normal form that isn't a constructor tree, a
new value form the whole kernel (conversion, unification, readback,
pattern matching, `omega`, `ring`) must handle, and the natives-off
evaluator can't match it (it would have to be part of the core's meaning
of `+`, not a shortcut). GHC's natnormalise plugin does this outside a
kernel; Allais, McBride and Boutillier call such laws "perfectly useless
for commutativity" in their setting (§2). None of the provers in §2 makes
commutativity definitional **[inferred]** from §2.

**(e) Tactics only.** A `simp`-like normaliser that rewrites `x + 1` to
`Succ x` (and `0 + x` to `x`) in a goal before `cases` or `rfl`; `omega`
and `ring` already prove the equations. Leaves definitional equality and
pattern matching as they are, so indices like `Vec a (n + 1)` stay stuck.
No kernel change.

**(f) Binary naturals.** Represent `Nat` as binary (Coq's `N`, Agda's
`Data.Nat.Binary`, §2). Stitchwort already stores numbers as `BigUint`
(`Value::Nat`) while keeping the unary meaning **[checked]**, so it has
binary speed without binary proofs. Binary would make `x + 1` worse, not
better, for open terms (carry propagation) **[inferred]**. Not a fix for
this problem.

## 5. Evidence from the prototypes

### (b): `+` and `*` count down their second argument

The previous lane agent's prototype (commit `4114e8d5`) changes
`Nat.add` and `Nat.mul`, rewrites `core/Arith.sw`'s laws for the new side,
adds `Nat.zeroAdd`, `Nat.succAdd`, `Nat.zeroMul`, `Nat.succMul`, and swaps
the argument order in `native.rs`, `omega.rs` and `ring.rs` **[checked]**.

Breakage, counted with a scratch `STITCHWORT_LIBRARY_KEEP_GOING` switch in
`library.rs` that reports a failing library file's errors and goes on
(prototype tooling, to drop) **[checked]**:

- **std**: 173 direct errors in 19 files, and about 100 more
  `E-FAILED-DEPENDENCY` errors in declarations that use a broken one.
  By file: `Nat/Arith` 38, `List/Lemmas` 35, `List/SortLemmas` 33,
  `Int/Int` 17, `Set/Spec` 10, `List/Index` 9, `Map/Spec` 7, `Float/Float`
  5 (the pin failure in §3 and what follows from it), `Nat/Digits` 4, and
  1 or 2 each in `Omega/Sound`, `Nat/IterateRepeat`, `Nat/Divides`,
  `Map/Map`, `Map/ByPosition`, `PrefixSums/BlockSum`, `Mod/Mod`,
  `Int/Lemmas`, `Graph/Search`, `Fin/Fin`. By kind: 98 `E-TYPE-MISMATCH`,
  42 `E-REFL`, 9 `E-REWRITE-NOTHING` (of the first 157). `Float/Theory`
  wasn't measured: with `Float`'s natives unbound, its failed proofs set
  off counterexample searches that multiplied huge numbers for over 8
  minutes before I stopped them (a stack sample showed
  `counterexample::run_fast` → `rt::prims::nat_mul`) **[checked]**.
- **aoc**: 74 direct errors in 22 files, and 16 namespaces (days 6, 7, 8,
  11, 12, 15 to 18, 20 to 23, 2025 days 1 and 2, `Common.Proofs`) not
  checked at all because a std file they use failed. So this count is a
  floor. The largest: 2024 day 4 part 1 (13), 2025 day 7 part 1 (10),
  2025 day 8 part 2 (5) **[checked]**.

The shape of the breakage **[checked]**, from the error messages:

1. Lemmas proved by induction on the left summand: `Nat.leAddCong` (`d + a
   ≤ d + b` by induction on `d`), `ltAddCong`, `leAddCancel`,
   `addSubCancel`. Fix: prove the right-summand form by induction (`a + d
   ≤ b + d`) and get the left form by `Nat.addComm`. On the branch (commit
   `5b1d73c4`); `Nat/Arith`'s errors went from 38 to 28.
2. `Succ q * d` in the division lemmas: now needs `Nat.succMul`. Fixed for
   `leMulRight`; the 11 others are the same.
3. `0 + x` from folds that start at `0` (`List.sumBy`, `List.count`), and
   `Succ (length xs) + length ys` from `lengthAppend`: need `zeroAdd` and
   `succAdd`. Fixed for `lengthAppend`.
4. The good kind: `E-REWRITE-NOTHING` where a rewrite with `Nat.addOne` is
   no longer needed. Fix: delete it.

Projected size **[inferred]**: about 170 proof edits in std and 75 or more
in aoc, most of them one line, and new `*Right` variants of a handful of
order lemmas. The prototype's own diff to `core/Arith.sw` and
`Nat/Arith.sw` is about 150 lines.

### (c): both sides compute, natives on

Commit `46f00a43` puts std, `omega.rs`, `ring.rs` and `native.rs` back as
on `main`, and changes one function: the natives' shortcut for a stuck sum
(`run_partial` in `native.rs`) now also takes `Succ`s off the second
argument, so `add m (k + n)` is `k + add m n` and `add m 0` is `m`
**[checked]**. 18 lines. It runs only with natives on, so it isn't a real
implementation (§6), but it shows what the end state would break.

Breakage **[checked]**:

- **std**: 5 errors outside `Float`, all `E-REWRITE-NOTHING`: a rewrite
  with `Nat.addSucc` or `Nat.addOne` (4 in `List/SortLemmas`, 1 in
  `Graph/Search`) found nothing because the goal had already computed.
  Fixed on the branch by deleting the rewrite (or, in `Graph/Search`,
  rewriting the hypothesis instead of the goal). `Float`: 3 pins failed
  (§3), and then 30 `E-RESOURCE` ("recursed more deeply than allowed") in
  `Float/Theory`. I believe these follow from the pins **[unverified]**:
  the other possible cause is that (c) makes `+` force its second
  argument, and some `Float` model computation is deep there. Re-pinning
  and rerunning would tell.
- **aoc**: 27 direct errors in 14 files, 12 of them `E-REWRITE-NOTHING`
  (rewrites with `Nat.addOne` or `omega: bit + 1 = Succ bit` that are no
  longer needed). After deleting those in day 15 part 1 and day 24's
  `Adder.sw`, both check **[checked]**. Left: day 4 (12 errors: `rfl`
  after `cases` sees `… && True` against `…`, and a `calc` step whose two
  sides now compute to different shapes) and one `E-CASES-BUDGET` in day
  15 part 2, where a case on `Nat.decEq n (Succ n)` now appears that
  `cases` can't close. I didn't find the cause of either **[unverified]**.
- Speed: the whole std, loaded eagerly with no cache, took 4.75 s on
  `main` and about 5 s under (c) outside `Float/Theory` (which failed)
  **[checked]**, one run each.

## 6. What (c) would take for real

The prototype is a shortcut in the natives, so with natives off `x + 1`
is still stuck, and `natives.rs` would catch the two evaluators
disagreeing **[inferred]**. A real (c) puts the two equations in the core's
evaluation of `Nat.add` itself, for both evaluators (the reference
evaluator and the machine), as a declared, checked rule:

1. A kernel rule: when `Nat.add m n` is stuck on `m`, look at `n`; if it
   is `Zero`, the result is `m`; if `Succ n'`, it is `Succ (Nat.add m n')`.
   About as much code as the prototype in each evaluator **[inferred]**.
2. A check, when the rule is registered, that `Nat.add` is the definition
   it was written for (as `Float` pins its definitions) and that
   `Nat.addSucc` and `Nat.addZero` are provable, so the rule is a
   consequence of the definition and not a new axiom. (As built, §10, this
   check is a safety net against binding the rules to the wrong
   definition; the soundness argument is §9.)
3. The `natives.rs` tests extended to stuck sums, on and off.
4. `docs/core.md` and DESIGN.md §13 updated: the trusted base gains one
   rule.
5. Migration: delete the now-unneeded rewrites (about 17 found so far),
   re-pin `Float`, update the hash snapshots.

Rules for `*` (`m * Succ n = m * n + m`) could follow the same way; they
were not prototyped.

## 7. Recommendation

Ranked by end state:

1. **(c), both sides compute.** It is the only option where `x + 1`, `1 +
   x`, `x + 0`, `0 + x`, `length (xs ++ ys)` and `Vec` append all compute,
   so neither specs nor library conventions need to pick a side. The
   prototype breaks almost nothing (§5), and what breaks is mostly
   rewrites that should be deleted. The cost is one kernel rule, which is
   a proved theorem, plus `+` being strict in its second argument while
   checking. It is what Agda (`--rewriting`) and Rocq (rewrite rules)
   offer as an opt-in, with the same example (§2); here it would be one
   fixed rule whose confluence is checked by hand once (§4), not a
   general user feature. Risk: the day 4 and day 15 failures I didn't
   explain; the `Float/Theory` resource errors until re-pinned.
2. **(b), Lean's side.** No kernel change, and it fixes the common case
   (`x + 1`), and it is Lean's choice. But it moves the friction to
   `0 + x` folds, `length` of an append and `Vec` append, and costs about
   250 proof edits. Choose it
   over (c) if no kernel rule is acceptable.
3. **(e), tactics**, as a complement to either: a normaliser before `cases`
   helps with equations that need commutativity or associativity
   (`x + (y + z) = (x + y) + z` with `z` unknown), which no option makes
   compute.
4. **(a)**, today.
5. **(d)**: commutativity in conversion is not worth a new value form in
   the kernel when `omega` and `ring` already prove these equations.

(f) is not a fix for this problem.

## 8. Decisions for Matt

| id | question | recommendation |
|---|---|---|
| D1771 | Which end state for `+`: (a) keep, (b) Lean's side, (c) both sides compute, (d) kernel normalisation? | [(c), with the rule in the core for both evaluators (§6), not as a natives shortcut] |
| D1772 | If (c): also add the matching rules for `*` (`m * Succ n = m * n + m`, `m * 0 = 0`)? | [not now; measure after `+`] |
| D1773 | If (c) is rejected: switch to (b) and migrate std and aoc (about 250 edits)? | [yes; (b) beats (a) on the common case even with its new friction] |
| D1774 | The branch's prototype commits: merge any of them? | [merge only this note (cherry-pick its commits); drop the prototype commits, which are natives-only and carry scratch tooling. The real (c) is a new ticket] |

D1771 was decided for (c), with the rule in the core for both evaluators;
D1772 (rules for `*`) was left for later, as the external review also
advised. §9 is the soundness argument for what was built, rewritten after
the review; §10 is what was built and what it changed.

## 9. Why (c) is sound

This replaces the argument of §3 ("Trust") and §4, which said the rules are
safe because their equations are theorems. That is reassuring but not
enough: an equation that is provable can still, added to conversion, fail
to terminate, break confluence (and so make conversion depend on the order
of steps), or break subject reduction. Agda checks confluence of rewrite
rules separately and says termination is not checked
([rewriting](https://agda.readthedocs.io/en/latest/language/rewriting.html))
**[cited]**; Cockx, Tabareau and Winterhalter,
[The Taming of the Rew](https://doi.org/10.1145/3434341) (POPL 2021), treat
the extension of a type theory's computation with rewrite rules as the
problem, with conditions for subject reduction and confluence
**[cited]** (the paper's abstract and §1; the details below that rely on it
are marked). So the argument has four parts: typing, confluence,
termination, and that the evaluator computes the normal forms of the
extended relation.

### 9.1 Two things called "the rules"

**The rewrite relation** `→` is the kernel's reduction (β; ι, a `case` on a
constructor; δ, unfolding a definition; the natives, each of which is a
sequence of those steps, §3 "Trust") extended with four rules on the head
`Nat.add` (written `+`):

```
R1  Zero + n     → n
R2  Succ m + n   → Succ (m + n)
R3  m + Zero     → m
R4  m + Succ n   → Succ (m + n)
```

R1 and R2 are not new: they are what δ and ι do to `Nat.add` (its case
tree splits its first argument and nothing else, `std/core/Data.sw`)
**[checked]**, and the kernel never shows a half-unfolded `Nat.add` (a
stuck call stays folded, `value.rs` `stuck_tree`) **[checked]**, so for
`Nat.add` "δ then ι" and "R1 or R2" are the same step. R3 and R4 are new.
The relation overlaps: `Succ m + Succ n` can take R2 or R4.

**The evaluator** is deterministic. Both kernel evaluators (the machine,
`value.rs`, and the reference, `reference.rs`) run `Nat.add`'s case tree
first (R1, R2, or the natives' shortcut for many R2 steps). Only when the
tree is stuck, because the first argument is neither a number nor a
constructor, do they look at the second argument
(`nat_add::stuck`): a number `k` (or `Zero`, or `Succ`s around a number)
gives `k + m`; `k + n'` with `k > 0` gives `k + (m + n')`, with `m + n'`
left as a stuck call; anything else leaves `m + n` stuck **[checked]**. That
is R4 taken `k` times and then R3 or nothing, done in one step, the way the
natives take R2 `k` times in one step. So the evaluator gives R1 and R2
priority and uses R3 and R4 only when the first argument is neutral; every
step it takes is a sequence of `→` steps.

The arguments below are about `→`; §9.5 connects them to the evaluator.

### 9.2 Assumptions

Each claim below depends on some of these; they are stated once here.

- **A1 (the core).** Without R3 and R4, the kernel's reduction is
  confluent and strongly normalising on well-typed terms, has subject
  reduction, and its type theory is consistent. This is what the rest of
  the kernel already assumes (DESIGN.md §13); none of it is proved for
  Stitchwort.
- **A2 (a model).** The core has a model in which `Nat` is the natural
  numbers, `Zero` and `Succ` are zero and successor, and each definition
  denotes the function its equations define. (The set-theoretic model of
  a predicative type theory with inductive types; assumed, not built.)
- **A3 (what's folded).** A call the evaluator leaves folded by name
  (dictionaries, theorems, `k * x` with `x` a variable, a definition stuck
  on a `Quot.lift` leaf) and that has type `Nat` never unfolds to `Zero`, a
  `Succ` or a number. Checked by reading **[checked]**: theorems must have
  a propositional type (`E-NOT-A-PROP`, tried); dictionaries are records;
  `k * x` unfolds to `x + (k - 1) * x`, stuck on `x` (`native::folds_mul`);
  a call folded on a lift leaf is stuck there. Opaque definitions are
  treated as variables, by design, in both the relation and the evaluator.
- **A4 (the code).** `nat_add.rs`, and the two call sites in `value.rs`
  and `reference.rs`, implement R3 and R4 as described in §9.1, and only
  for the library's `Nat.add`. This is trusted, as the natives are; the
  tests in §10 check it on many inputs, not for all.

### 9.3 Typing

R3 and R4 are typed rewrite rules: in any context where the left side is
well typed, `m` and `n` have type `Nat` (the type of `Nat.add`), and both
sides have type `Nat`. `Nat` has no parameters or indices, so no rule
changes a type, and an instance of a rule under any substitution of `m` and
`n` is again well typed. The rules are first-order (no λ, no applied
variable), left-linear (each variable occurs once on the left), on
constructor patterns, and non-duplicating (each variable occurs at most once
on the right) **[checked]** against the four rules above. With A1, a step
by R3 or R4 replaces a term of type `Nat` by one of type `Nat` in the same
context, so subject reduction is kept **[inferred]**: the rules leave every
type alone, which is the easy case of the Taming of the Rew's conditions
**[inferred]**, not checked against the paper's statement.

**Consistency.** The equations of R3 and R4 hold in the model of A2:
`m + 0 = m` and `m + (n + 1) = (m + n) + 1` for all natural numbers. They
are also derivable in the core without the rules: they are the theorems
`Nat.addZero` and `Nat.addSucc`, proved by induction on `m` from the
definition (`std/core/Arith.sw`) **[checked]**. So adding them to
conversion identifies only terms that the model of A2 already identifies;
under A2 the extended theory has the same model, and is consistent
**[inferred]**. This is the part of the old argument that stands; it is not
enough alone, which is why §9.4 and §9.5 follow.

### 9.4 Confluence

**Where the rules can overlap.** An overlap needs a term that is a redex of
two rules at once, at the root or with one redex inside the other's left
side at a non-variable position. The left sides of R1 to R4 are
`Nat.add p q` with `p`, `q` each a variable, `Zero` or `Succ` of a
variable. Their non-variable positions are the root and the constructor
arguments. A constructor applied to a variable is not a redex of any rule
of `→` (no rule's left side is headed by a constructor; a number is a
value). So overlaps are at the root only, between rules whose left side is
headed by `Nat.add`. `Nat.add` is rigid: a constant, never the result of a
substitution, so β never produces a new `Nat.add` head that wasn't there
(β can only substitute into the arguments, which the rules match by
variables, constructors, or not at all), and no other definition's δ or ι
step has a left side headed by `Nat.add`. The natives' steps are sequences
of R1/R2 steps and steps of other definitions (§3 "Trust"). So the only
overlaps of the whole relation that involve R3 or R4 are those among R1 to
R4 **[inferred]**, the point the review made. R1 against R2, and R3 against
R4, are on different constructors and don't overlap.

**The four critical pairs**, each joined:

| term | one rule | the other | joined at |
|---|---|---|---|
| `Zero + Zero` | R1: `Zero` | R3: `Zero` | `Zero` |
| `Zero + Succ n` | R1: `Succ n` | R4: `Succ (Zero + n)` →R1 `Succ n` | `Succ n` |
| `Succ m + Zero` | R2: `Succ (m + Zero)` →R3 `Succ m` | R3: `Succ m` | `Succ m` |
| `Succ m + Succ n` | R2: `Succ (m + Succ n)` →R4 `Succ (Succ (m + n))` | R4: `Succ (Succ m + n)` →R2 `Succ (Succ (m + n))` | `Succ (Succ (m + n))` |

**[checked]**, by hand, and by the test `the_critical_pairs_join` in
`crates/driver/tests/nat_add_rule.rs`, which evaluates each term and both
reducts with both evaluators, natives on and off, with `m` and `n`
variables, `0`, `4` or `3 + x`, and checks that all three are convertible
and that the two evaluators give the same normal form (64 combinations
each).

**Confluence of R1 to R4.** They form a left-linear first-order rewrite
system whose critical pairs all join, so it is locally confluent (the
critical pair lemma, Knuth and Bendix; Huet 1980), and, being terminating
(§9.5), confluent (Newman's lemma) **[inferred]** from these standard
results (from memory, **[unverified]** as citations).

**Confluence with the rest of the kernel.** For λ-calculus extended with
left-linear first-order (algebraic) rules, confluence of the rules alone
gives confluence of the combination: Müller, "Confluence of the lambda
calculus with left-linear algebraic rewriting", Information Processing
Letters 41 (1992) **[unverified]**, from memory. Stitchwort's core has
more than β (ι, δ, `J`, quotients, the other trusted rules), so that
theorem doesn't apply as stated. What carries over is its reason, which
holds here: no step of the rest of `→` overlaps R3 or R4 (above), and none
of them duplicates or erases a subterm in a way that breaks a left-linear
pattern, since R3 and R4 match only `Nat` constructors and variables. The
Taming of the Rew's triangle criterion is the general check for this
situation (Agda's `--confluence-check` implements it, with this very
example, §2) **[cited]**; for two fixed rules a generic checker is out of
proportion, as the review said, and the critical pairs are checked by the
test instead. So: confluence of the extended relation is argued, with A1
and the overlap analysis, not proved **[inferred]**.

### 9.5 Termination, and the evaluator's normal forms

**R1 to R4 terminate.** Interpret terms in the positive integers: a
variable or other neutral term as any value `≥ 1`, `Zero` as 1, `Succ x` as
`x + 1`, and `m + n` (the rule head) as `2m + 2n`. Each interpretation is
strictly increasing in each argument, and each rule strictly decreases the
value of its left side **[checked]** by arithmetic:

| rule | left | right |
|---|---|---|
| R1 | `2 + 2n` | `n` |
| R2 | `2m + 2n + 2` | `2m + 2n + 1` |
| R3 | `2m + 2` | `m` |
| R4 | `2m + 2n + 2` | `2m + 2n + 1` |

So every rewrite sequence of R1 to R4 is finite (a polynomial
interpretation, Lankford 1979, **[unverified]** as a citation). In words:
R2 and R4 replace a sum by a sum of proper subterms under a `Succ`, and R1
and R3 remove the sum.

**The whole core with them.** That the core of A1 stays strongly
normalising with R3 and R4 added is a different claim, and it is **expected,
not proved**. It is expected because the rules are first-order,
non-duplicating, type-preserving and terminating on their own, and results
of that shape exist for simpler systems (Breazu-Tannen and Gallier,
"Polymorphic rewriting conserves algebraic strong normalization", 1989/1991,
for System F with algebraic rules **[unverified]**, from memory). The Taming
of the Rew assumes normalisation for its decidability results rather than
proving it **[unverified]** (read in the paper's introduction by the
research subagent of §2, not checked again). No such theorem covers
Stitchwort's core (inductive families, large elimination, quotients).

**The evaluator computes `→`-normal forms.** Every evaluator step is a
sequence of `→` steps (§9.1), so what the evaluator identifies is
`→`-convertible. Conversely, a value the evaluator returns has no R1 to R4
redex: a stuck `m + n` has `m` neither a number nor a constructor (else R1
or R2 would have run) and `n` neither (else R3 or R4 would have), up to
A3 for folded calls. So, with confluence, two terms are convertible exactly
when the evaluator gives them the same normal form **[inferred]**: checking
only the first argument first is complete, because if it is a constructor
R1 or R2 applies, and if it is neutral only R3 or R4 can apply at the root,
which the evaluator then tries. Once both are neutral, `x + y` has no step,
and stopping is right. The evaluator also does bounded extra work: R4 is
taken in one step for any `k`, and the stuck `m + n'` it leaves is built
directly, not evaluated again.

## 10. As built

On branch `worktree-agent-ad5f0d8aae673e382` (SW-787, D1771). Everything
here is **[checked]** on that branch, against `main` at `23ffe28f`.

**Kernel** (`crates/core`). `nat_add.rs`: `stuck` (R3 and R4 for a call
stuck on its first argument), `critical_pairs` (the four, as terms, for the
test), `register` (the binding), `NAT_ADD_HASH`. The machine applies it in
`stuck_tree` (`value.rs`), where every case tree that can't step ends; the
reference evaluator in `unfold` (`reference.rs`), after the case tree;
the natives' `Nat.add` shortcut (`native.rs` `run_partial`), after taking
`k` off the first argument, so natives on and off agree. The rule sits in
`Builtins::nat_add_rule`, not with the natives, and `disable_natives`
doesn't touch it. The WebAssembly kernel is the same crate compiled to
WebAssembly (`crates/web`), so there's nothing separate there.

**Binding.** `register` runs when the prelude binds `Nat.addSucc`
(`registry.rs` names `Nat.addZero` and `Nat.addSucc`). If `Nat.add` has
another content hash than the pinned one (which covers `Nat`), the rules
stay off and `+` is its definition alone, as compact text falls back to
constructors for another `List`; a test fails for the library's own
(`nat_add_is_the_pinned_declaration`), printing the new hash. (Refusing
the prelude instead, as `Float` does, broke a test that loads a prelude
with a renamed `Succ` field to check the JS representation's fallback;
this is a choice, flagged for review.) With the pinned hash, both theorems
must be final theorems with the types `(n: Nat) → n + 0 = n` and `(n: Nat)
→ (m: Nat) → n + Succ m = Succ (n + m)`, else `E-BUILTIN`. The theorem
check is a safety net against binding the rules to the wrong definition;
the argument is §9.

**Tests.** `crates/driver/tests/nat_add_rule.rs`: the pinned hash; the
critical pairs (§9.4); stuck sums (`x + 0`, `x + 1`, `x + 3 = 3 + x`,
`x + Succ y`, `x + (y + 2) = (x + y) + 2`, `(2 + x) + (3 + y)`, `0 + x`)
the same with both evaluators, natives on and off, and `x + y = y + x` and
`x + 1 = 1 + y` still not convertible; a copy of `Nat.add` gets no rules.
`crates/driver/tests/natives.rs`: the natives' shortcuts against the
definitions now include sums stuck on either side against `Succ` chains.
`examples/accept/plus-both-sides.sw`: the facts of §3 by `rfl`, `Vec a
(n + 1)` declared and matched, `Vec` append with index `n + m` and `m + n`.
`examples/reject/plus-comm-by-rfl.sw`: `n + m = m + n` by `rfl` is still
`E-REFL`.

**Elaborator** (`crates/elab`). Nothing mirrors the kernel's `+` except
through values, so most of it needed nothing. Changed: `omega` recognises
`min` and `max` after they've computed with shared `Succ`s (`min (x + 1)
(y + 1)` is now `if Nat.leq x y then Succ x else Succ y`) and reads `k *
t` whose last `t + 0` is `t`; `E-INDEX-STUCK`'s note for a stuck sum says
both sides must be unknown (the old note told users to declare `Succ n`
instead of `n + 1`). `ring` and the unifier needed no change.

**Library and programs.** In std: `Nat.decAddSuccNotZero` deleted (it
existed only because `most + 1` was stuck); the prototype's five rewrites in
`List/SortLemmas` and `Graph/Search`, and three in `Float/Theory`; `Float`'s model and theory write the
significand on the right of `*` (below); `Float.neg`, `abs`, `sub`, `add`
and `toInt` re-pinned. In aoc, the prototype's deletions (2024 days 4, 15 and 24), then 23
errors on the first full run, all fixed (2024 days 4, 14 and 15; 2025 days
1, 2, 4 and 6).
Examples that used `x + 0` or `x + Succ y` to demonstrate `rewrite` use
`x * 1` and `x * Succ y`; rejects that relied on `n + 1` being stuck use
`n + m`; `reject/index-declared-plus-one.sw` is gone (its declaration is
now accepted). `games/rogue`: `lcg` and `Dice.upTo` are opaque (below).
The guide's induction example is `n * 1 = n`.

**The failures the prototype left unexplained** (§5). None was an artefact
of the prototype running in one evaluator; all three persist with the rule
in both, and each is a consequence of (c):

1. *30 `E-RESOURCE` in `Float/Theory`*, and one in `Float.toIntFrom`.
   Not the pins: after re-pinning they stayed. `Float.Model.units` and
   `Float.Theory.magUnits` were `(f + 2^52) * pow2 (e - 1)`. R4 turns
   `f + 2^52` into `2^52 + f`, and `*` recurses on its first argument, so
   evaluating that product with `pow2 (e - 1)` unknown unfolds `*` 2^52
   times. Minimal case: `theorem t (e f: Nat): (f + 4503599627370496) *
   Nat.pow 2 e = (f + 4503599627370496) * Nat.pow 2 e := rfl` is
   `E-RESOURCE` ("while unfolding `Nat.mul`") under (c) and checks on
   `main`, where `(4503599627370496 + f) * Nat.pow 2 e` fails the same way.
   Fix: `pow2 (e - 1) * (f + 2^52)` in the model and the theorem
   statements (proofs adjusted; one `omega` needed a `ring` fact for `P *
   Succ x`), and `Float.toIntFrom` passes `m - (e - 1) * 2^52`, which
   stays stuck, instead of `m - e * 2^52 + 2^52`.
2. *2024 day 4, 12 errors.* `List.range (height grid + 3)` now computes
   its first three elements (`h + 3` is `3 + h`, and `List.rangeFrom`
   counts down its first argument), so a sum over it is `f 0 + f 1 + f 2
   + …` with three instances already computed. `rewrite each _ _` rewrote
   the instance under the binder and not those, so `rfl` compared what
   `spells` computes to (a `&&` chain ending `&& True`, from its recursion
   over the four letters) with `readsXmas`'s (no `True`): the `… && True`
   against `…` of §5. The `calc` step failed the same way: the lemma's
   `_ _` functions couldn't be unified against the computed sums. Fix:
   rewrite pointwise with `List.sumByCong`, give the functions to
   `List.sumByNestedAdd`, and finish `part1Correct` with `omega` over the
   direction lemmas (rewriting there ran out of budget comparing the
   computed sums).
3. *2024 day 15 part 2, `E-CASES-BUDGET`.* `gather`'s fuel `2 *
   warehouse.boxes.size + 1` is now `Succ (size + size)`, so `cases`
   unfolds `gather` a step and splits on what's inside: neighbouring map
   lookups and coordinate comparisons, among them `Nat.decEq n (Succ n)`
   (from `column + 1`), whose `Yes` case it can't refute. On `main` the
   fuel `… + 1` was stuck and `cases` split on the whole `gather …` call.
   Shown by making `cases` fail on a probe theorem: on `main` the open case
   has `gather … (Map.size … + (Map.size … + 0) + 1)`, under (c) 23 splits
   with `gather … (Map.size … + Map.size …)`. Fix: split by hand on
   `gather` (`match … with | Some group => rfl | None => rfl`).

**Other consequences found** while migrating, of three kinds:

- *A constant summand moves out where recursion sees it.* Besides `Float`:
  `games/rogue`'s `lcg seed` is `(seed * 1103515245 + 12345) % 2^31`;
  `+ 12345` moves out, and reading back `%`'s fuel recursion under its
  stuck `if`s unrolls 12345 levels (`E-RESOURCE`, "too large to show").
  `lcg` and `Dice.upTo` are opaque for checking now (one `unfolding` where a
  proof needs the body). `examples/goals/counterexample-out-of-steps.sw`
  stated `countDown (n + 100000000) = 1`, which now counts down 10^8 while
  checking (63 s); it uses `Nat.max n 100000000`. On `main` the same
  happened to anyone who wrote the constant first.
- *Goals compute further.* A `match` that replaced `Nat.leq d (Succ a)`
  now finds it inside `(a + 1) % d` (2025 day 1); `rewrite` finds nothing
  where the goal already computed (the `E-REWRITE-NOTHING`s); `x + 1`
  prints as `Succ x` and `x + k` as `k + x` in messages.
- *Unification that relied on a stuck shape.* `List.memBetween h` with `h:
  x ∈ List.between 2 n` no longer infers its implicit `lo` and `hi`:
  `List.between ?lo ?hi` unfolds to `rangeFrom (?hi + 1 - ?lo) ?lo`, and
  `?hi + 1` is now `Succ ?hi`, a different shape from the computed `n - 1`
  (2025 day 2; fixed by naming them). Likewise `x + ?d` no longer unifies
  with a computed `Succ (x + t)` (rogue). A unifier rule inverting R4 would
  recover these; not done.

**Measured** (release build, other lanes running, so rough):

| | `main` | (c) |
|---|---:|---:|
| whole std, loaded eagerly, no cache | 4.6 to 4.9 s | 4.7 to 4.8 s |
| `aoc`, `stitchwort check --no-cache` | 37.0 s, 52.7 s | 37.1 s, 49.6 s |
| bench `--no-time`, `check-closed-*` steps | 1,054,829 | 1,059,555 (+0.5%) |
| bench `--no-time`, `examples` steps | 3,126,066,165 | 3,127,056,213 (+0.03%) |

No bench count regressed beyond that. The `check-closed-*` steps are
mostly the prelude's; that the 0.5% is the two theorems' types checked at
binding is **[inferred]**, not measured apart.

**Not done.** Rules for `*` (D1772). Printing `k + x` as `x + k`, which
would match how people write it. The unifier rule inverting R4.
