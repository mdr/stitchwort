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
**[cited]** (read in full for §9.4, which quotes it with page numbers). So
the argument has four parts: typing, confluence,
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
- **A1′ (the core's triangle property).** Without R3 and R4, the kernel's
  parallel reduction has the triangle property (the Taming of the Rew,
  Definition 4.1), for a `ρ` that contracts every visible β, ι and δ redex.
  This is stronger than A1's confluence and is what §9.4 needs in its
  place; it is proved for PCUIC in MetaCoq, not for Stitchwort's core
  (quotients, `J`, the natives). Assumed, not proved.

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
context. That is the Taming of the Rew's rule validity (Fig. 5, p. 0:14):
for every extension `∆` of the context, every `T` and every instance `σ`,
if the left side under `σ` has type `T` then so does the right side.
Stitchwort has no cumulativity (docs/core.md, "Universes"), so a left side
of type `T` has `T` convertible to `Nat`, and the right side has type
`Nat`, hence `T` **[inferred]**; the same holds for R5 and A1 to A3 of
§9.4. Subject reduction then follows as in the paper's Lemma 6.6 (p. 0:17),
which uses validity for a rewrite step and confluence (§9.4, for
injectivity of `Π`) for β and ι **[inferred]**: Stitchwort's own proof of
subject reduction for the core is A1's assumption, not a theorem.

**Consistency.** The equations of R3 and R4 hold in the model of A2:
`m + 0 = m` and `m + (n + 1) = (m + n) + 1` for all natural numbers. They
are also derivable in the core without the rules: they are the theorems
`Nat.addZero` and `Nat.addSucc`, proved by induction on `m` from the
definition (`std/core/Arith.sw`) **[checked]**. So adding them to
conversion identifies only terms that the model of A2 already identifies;
under A2 the extended theory has the same model, and is consistent
**[inferred]**. This is the part of the old argument that stands; it is not
enough alone, which is why §9.4 and §9.5 follow. The Taming of the Rew
reaches the same conclusion by another route: its Lemma 6.8 (p. 0:18, "This
lemma has not been formalized") gives consistency when each rewrite block
has an instantiation, a witness for each symbol and a proof of each rule's
equation, and it says of this very example that "the consistency of the
theory directly follow[s] from the fact that each rewrite rule already holds
propositionally for the standard plus function". Here the instantiation is
the library's `Nat.add`, with `rfl` for R1 and R2, `Nat.addZero` and
`Nat.addSucc` for R3 and R4, and their composites for R5 and A1 to A3
**[inferred]**.

### 9.4 Confluence

The argument rests on Cockx, Tabareau and Winterhalter,
[The Taming of the Rew](https://doi.org/10.1145/3434341) (POPL 2021), read
in full for this section (the HAL copy, hal-02901011v2; page numbers below
are that copy's, `0:N`). Its running example is these four rules. Quotes
are exact; what Stitchwort adds to them is marked.

**What the paper proves.** Parallel reduction `⇛` contracts any set of
redexes at once; `→ ⊆ ⇛ ⊆ →*` (§4.1, Eq. 1, p. 0:9). Then:

- *Definition 4.1 (Triangle property)* (p. 0:9): "Parallel reduction of a
  rewriting system satisfies the triangle property when for every term t,
  we have t ⇛ ρ(t), and for every u such that t ⇛ u, we also have
  u ⇛ ρ(t)."
- *Lemma 4.2 (Confluence of Parallel Reduction)* (p. 0:9, formalised in
  MetaCoq): "When parallel reduction satisfies the triangle property, then
  the rewrite system is globally confluent." No termination is needed: "we
  seek a modular and decidable check for confluence, that does not rely on
  termination" (§4, p. 0:8).
- *Definition 6.2* (p. 0:15) fixes `ρ≻` for a total order `≻` on the
  rules: if `u` matches a rule's left side, take "the first rule for which
  the left-hand side matches (w.r.t. to ≻)", with `ρ≻` applied to the
  matched subterms; β and ι redexes are contracted the same way; otherwise
  `ρ≻` goes into every direct subterm.
- *Definition 6.3 (triangle criterion)* (p. 0:16): (1) for every instance
  `u = lσ` of a rule `l → r` whose first matching rule is `l' → r'` with
  `u = l'τ`, "rσ ⇛ r′(ρ≻τ)"; (2) no rule's left side, applied to more
  arguments, is an instance of another's ("eval (l | S)σ = l′τ implies
  S = •").
- *Theorem 6.4 (Confluence)* (p. 0:17, formalised): "If there exists an
  order ≻ on R such that (R, ≻) satisfies the triangle criterion, then RTT
  is confluent." Subject reduction (Lemma 6.6, p. 0:17) follows from
  confluence and the rules' validity.
- *Theorem 7.3* (pp. 0:19-0:20) reduces the criterion to a finite check:
  if the set of left sides, ordered by `≻`, is "closed under unification"
  (Definition 7.2, p. 0:19: "for every pair of patterns p, q ∈ C such that
  p unifies with q with most general unifier σ , we also have pσ ∈ C, and
  pσ ≻ p"), all rules for a
  symbol take the same number of arguments, and "for every rewrite rule
  ∆ ⋉ p _ r ∈ R and every parallel reduction step R ⊢ p ⇛ u we have
  R ⊢ u ⇛ r", then the triangle criterion holds. Auxiliary rules added to
  close the left sides under unification "are always instances of existing
  rewrite rules and thus need not be considered by the reduction
  algorithm" (Algorithm 7.4, p. 0:20).

*Example 4.3* (pp. 0:9-0:10) is R1 to R4: "Consider a rewrite system with
symbols 0, suc, and +, and rules 0 + n _ n, m + 0 _ m, (suc m) + n _
suc (m + n), and m + (suc n) _ suc (m + n)." With "the first rule that
matches", "the triangle property is not satisfied: we have ρ((suc m) +
(suc n)) = suc (m+(suc n)), but we also have (suc m)+(suc n) ⇛ suc ((suc
m)+n) ̸⇛ suc (m+(suc n)). To satisfy the triangle property, we extend the
rewrite system with an additional 'parallel rewrite rule' (suc m) +
(suc n) _ suc (suc (m + n))." *Example 7.5* (p. 0:20) runs Algorithm 7.4
on the same rules: it adds the unifiers `0 + 0 → 0`, `0 + suc n → suc n`,
`suc m + 0 → suc m` and `suc m + suc n`, finds the check fails at the
last, and with the parallel rule "we have ρ≻((suc m) + (suc n)) = suc
(suc (m + n)) … thus making the final check succeed." In Stitchwort's
names:

```
R5  Succ m + Succ n → Succ (Succ (m + n))      (the parallel rule)
A1  Zero + Zero     → Zero                     (unifier of R1, R3)
A2  Zero + Succ n   → Succ n                   (unifier of R1, R4)
A3  Succ m + Zero   → Succ m                   (unifier of R2, R3)
```

ordered R5, A1, A2, A3 before R1 to R4 (more specific first, as
Algorithm 7.4 asks).

**The check of Theorem 7.3, for R1 to R5 and A1 to A3** **[checked]** by
hand. Every left side is `Nat.add` of two patterns, so the arity condition
holds. The left sides are closed under unification: the pairs that
overlap are R1/R3 (A1), R1/R4 (A2), R2/R3 (A3) and R2/R4 (R5's left
side); R1/R2 and R3/R4 are on different constructors; each of R5 and A1
to A3 unifies with a rule only to give itself. A left side `p` has no
redex below the root (its arguments are variables, `Zero`, or `Succ` of a
variable), so the `u` with `p ⇛ u` are `p` and the right sides of the
rules that match `p`:

| left side | `u` with `p ⇛ u` (other than `p` and the rule's own right side) | `u ⇛` right side |
|---|---|---|
| R1 to R4 | none: no other rule matches a left side with a variable where the other rule has a constructor | |
| A1 `Zero + Zero` | `Zero` (R1, R3) | `Zero` |
| A2 `Zero + Succ n` | `Succ n` (R1); `Succ (Zero + n)` (R4) | `Succ n`, by R1 under `Succ` |
| A3 `Succ m + Zero` | `Succ (m + Zero)` (R2); `Succ m` (R3) | `Succ m`, by R3 under `Succ` |
| R5 `Succ m + Succ n` | `Succ (m + Succ n)` (R2); `Succ (Succ m + n)` (R4) | `Succ (Succ (m + n))`, by R4 or R2 under `Succ` |

So R1 to R5 satisfy the triangle criterion, and by Lemma 4.2 their
reduction is confluent, whether or not it terminates. These are the same
joins as the old critical-pair table (whose rows were A1, A2, A3 and R5's
left side), with one difference that matters: each join is one parallel
step, which is what makes termination unnecessary. The test
`the_critical_pairs_join` in `crates/driver/tests/nat_add_rule.rs`
evaluates each overlap and both reducts with both evaluators, natives on
and off, with `m` and `n` variables, `0`, `4` or `3 + x`, and checks that
all three are convertible and that the two evaluators agree (64
combinations each).

**R5 is not a new rule of Stitchwort's.** Its two sides are joined by two
steps that are already there (R2 then R4, or R4 then R2), so `→` with R5
and `→` without it have the same `→*`, the same conversion, and confluence
of one is confluence of the other **[inferred]**: R5 is part of the proof,
not of the kernel. (The paper says that of A1 to A3 because they are
instances of rules; R5 is not an instance, but it is derivable, which is
what confluence needs.) The evaluator reaches
R5's right side anyway: `Succ m + Succ n` runs `Nat.add`'s case tree (R2),
then `m + Succ n` is stuck on `m` and `nat_add::stuck` takes R4. **[checked]**
by `the_parallel_rule_is_reached` (`nat_add_rule.rs`): `Succ m + Succ n`,
`Succ (m + Succ n)` and `Succ (Succ m + n)` are each convertible with
`Succ (Succ (m + n))`, with both evaluators, natives on and off, for the
same 16 instances. Up to representation: with `m` and `n` variables the
sum's value is `Value::NatAdd(2, m + n)` (the compact "`Succ` twice
around"), while `Succ (Succ (m + n))` written as constructors stays two
`Value::Ctor`s (`native::ctor` compacts only a `Succ` of a number or of a
`NatAdd`, §10.2), so their quoted terms differ (`2 + (m + n)` against
`Succ (Succ (m + n))`) and conversion identifies them. And by `stitchwort
check` on `rfl` proofs: `Succ m + Succ n = Succ (Succ (m + n))`, `Succ (m
+ Succ n) = Succ (Succ (m + n))`, `Succ (Succ m + n) = Succ (Succ (m +
n))` and `Succ (3 + x) + Succ n = Succ (Succ ((3 + x) + n))` check, and
the control `Succ m + Succ n = Succ (Succ (n + m))` fails with "computing
the left side gives `m + n + 2`" **[checked]**.

**What transfers to Stitchwort, and what doesn't.** The paper's theorems
are about RTT, PCUIC with rewrite blocks (§5, p. 0:11; the formalisation
"features general inductive types and co-inductive types, a cumulative
hierarchy of predicative universes, an impredicative universe and a let-in
construct", §6, p. 0:15). Its conditions, against Stitchwort:

- *Left-linear rules on constructor patterns* (Fig. 5, p. 0:14: "Pattern
  variables are required to occur linearly"; patterns are variables,
  symbols, `N`, `zero`, `suc p` and pairs, Fig. 2, p. 0:11). R1 to R5 are
  left-linear and match only `Zero`, `Succ` and variables **[checked]**.
- *Rule validity: the rules preserve typing* (Fig. 5, p. 0:14). §9.3.
- *Rules only on a fresh symbol, declared in the same block* (§3, p. 0:7:
  "Rewrite rules should only rewrite applications of 'fresh' (i.e.,
  postulated) symbols, not pre-existing symbols like → or Box"; §4.2, p.
  0:10: blocks must be "two-by-two orthogonal"). `Nat.add` is a definition,
  not a postulate. What carries over: the kernel never shows a
  half-unfolded `Nat.add` (§9.1), so its δ and ι steps are exactly R1 and
  R2, and the relation is the one RTT would have for a symbol `Nat.add`
  with the block R1 to R4, instantiated by the library's definition. The
  paper names this as the way rewrite rules are used in Agda: "the user
  would first define a function using regular means (i.e. pattern
  matching), then prove certain equalities about the function, and finally
  register these equalities as rewrite rules. The confluence checker will
  then take into account both the 'native' rewrite rules implicit in the
  definition by pattern matching, and the explicitly declared rewrite
  rules" (§7.3, p. 0:22); Agda's `--confluence-check` checks the triangle
  criterion (§7.3, p. 0:22, and footnote 6: since Agda 2.6.2). That is the
  paper's description of an implementation, not a theorem. The reason for
  the restriction in §3, that rewriting a type former such as `→` or `Box`
  breaks injectivity of type constructors, doesn't arise: `Nat.add` returns
  a `Nat` and no rule's right side is a type **[inferred]**.
- *Orthogonality to the rest of the reduction.* No other step of the
  kernel overlaps R1 to R5: their left sides are `Nat.add p q` with `p`, `q`
  each a variable, `Zero` or `Succ` of a variable; a constructor applied to
  a variable is not a redex of any rule (no rule's left side is headed by a
  constructor; a number is a value), so overlaps are at the root only;
  `Nat.add` is rigid, a constant that β never produces as a new head; and no
  other definition's δ or ι step has a left side headed by `Nat.add`. The
  natives' steps are sequences of R1/R2 steps and steps of other
  definitions (§3 "Trust"), reading a number `k` as `Succ` `k` times around
  `Zero` and a `NatAdd(k, x)` as `Succ` `k` times around `x` **[inferred]**.
- *The base theory's own triangle property.* Theorem 6.4's proof shows
  that parallel reduction of the base theory with the blocks has the
  triangle property; for PCUIC the base part is MetaCoq's (§4.1, p. 0:9:
  "This has for instance been formally proven for CIC in the MetaCoq
  project"). Stitchwort's core is not PCUIC: it has quotients, `J`, the
  natives and the other trusted rules, and no one has shown its parallel
  reduction has the triangle property. So Stitchwort needs **A1′**: the
  core's reduction without R3 and R4 has a parallel reduction with the
  triangle property, for a `ρ` that contracts every visible β, ι and δ
  redex. This is stronger than A1's confluence, and is assumed, not proved.

So: **R1 to R5 satisfy the triangle criterion [checked]; that their
reduction is confluent without termination is the paper's Lemma 4.2 and
Theorem 6.4 [cited, checked against the text]; that the whole kernel's
reduction with R3 and R4 is confluent is argued from A1′ and the
orthogonality above, not proved [inferred].** What the paper does not
cover: rules on a defined symbol (only as Agda practice, §7.3), quotients,
the natives, and Stitchwort's core itself.

**What this replaces.** The old argument got confluence of R1 to R4 from
local confluence and Newman's lemma, which needs the termination of §9.5,
and confluence with the rest of the kernel by analogy to a theorem about
λ-calculus with algebraic rules; both citations were from memory and are
dropped. The paper cites van Oostrom's modularity theorem (§4.2, p. 0:10;
§8, p. 0:25: "combining two left-linear higher-order rewrite systems is
confluent if the systems are individually confluent and weakly orthogonal
… this result does not apply directly to our setting because of the
presence of inductive types"), which is why it proves its own (Theorem 6.7,
p. 0:17). Termination is still needed, but only in §9.5, for the
evaluator to be a decision procedure; confluence no longer depends on it.

**A third rule** (for `*`, D1772, or any other) would need, in this order:
it is left-linear on constructor patterns and variables, on a rigid head
whose δ and ι steps are its own case tree; its equation is a theorem of
the library (consistency, §9.3); it preserves typing (§9.3); the
unifiers of its left side with the head's existing rules, and any parallel
rule, are added until Theorem 7.3's one-step check passes; no other
kernel step has a left side headed by its head; the evaluator reaches each
added rule's right side (a test like `the_parallel_rule_is_reached`); and
both evaluators agree on it.

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
of the Rew neither assumes nor proves it for confluence and subject
reduction ("without relying on weak or strong normalization", §1, p. 0:2).
For deciding conversion it says weak normalisation is "the most obvious
requirement" (§6.5, p. 0:18), and without it proves only partial
correctness: "If algorithmic conversion terminates on inputs u and v, then
its answer is true if and only if R ⊢ u = v" (Theorem 6.10, p. 0:19, "not
been formalized"), for a comparison of weak-head normal forms with two
stated properties; checking termination is future work (§9, p. 0:25)
**[checked]** against the text. Since §9.4 no longer uses termination,
this section is only about the evaluator being a decision procedure. No such theorem covers
Stitchwort's core (inductive families, large elimination, quotients).

**The evaluator computes `→`-normal forms.** Every evaluator step is a
sequence of `→` steps (§9.1), so what the evaluator identifies is
`→`-convertible. Conversely, a value the evaluator returns has no R1 to R4
redex: a stuck `m + n` has `m` neither a number nor a constructor (else R1
or R2 would have run) and `n` neither (else R3 or R4 would have), up to
A3 for folded calls. So, with confluence, two terms are convertible exactly
when the evaluator gives them the same normal form, reading a
`NatAdd(k, x)` as `k` `Succ`s around `x` (the two representations of §9.4,
which the evaluators' conversion identifies) **[inferred]**: checking
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
  with a computed `Succ (x + t)` (rogue). Both are inferred again since
  SW-896 (§10.1); the first needed more than a rule for `+`.

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

**Not done.** Rules for `*` (D1772). (Printing `k + x` as `x + k` and the
unifier rule inverting R4 are built: §10.2 and §10.1.)

### 10.1 The unifier: sums stuck on an unknown (SW-896)

On branch `worktree-agent-a736c6643c901c9a2` (SW-896, D1977), against
`main` at `47e1425f`; **[checked]** there unless marked.

**The rule** (`crates/elab/src/unify.rs`, `plus_rule`, `stuck_sum`,
`plus_rule_with`). R4 and R2 read backwards. When one side of a
unification problem is `a + ?m` (or `?m + a`), stuck, with

- (U1) `a` mentioning no unknown (read back with at most 4096 nodes, else
  the rule doesn't apply),
- (U2) `?m` unsolved, not frozen, and applied to distinct variables,

and the other side is `k + t` with `k > 0` (a value with `k` `Succ`s
outside it), then:

- if `t` is convertible to `a`: `?m := k` (R4 `k` times, then R3);
- else, if `t` doesn't mention `?m` (U3): `?m := x₁ … xₙ => k + ?m' x₁ … xₙ`
  for a new `?m'`, and the problem goes on as `a + ?m' ≟ t` (`?m' + a ≟ t`).

Otherwise the rule does nothing and unification goes on as before. It is
tried before numbers are compared by their `k + x` forms, and again on the
base those leave (`Succ (x + ?d)` against `Succ (Succ x)`). The rules must
be bound (`Builtins::nat_add_rule`); for another `Nat.add` it is off.

**Why it chooses nothing a solution could avoid.** Take any solution, `?m
:= S`, of `a + ?m ≟ k + t` (every unknown solved). By (U1) `a` is the same
value under it, and `a` is neither a number nor a constructor: the sum
was stuck, and the evaluator tries R1, R2 and the natives' shortcut on `a`
before anything else (§10, *Kernel*). By (U2) `S` is `x₁ … xₙ => B`, and
`?m x₁ … xₙ` is `B`. By cases on `B`'s value: `Zero` gives `a + B ≡ a`,
which isn't headed by `Succ`; a value stuck on something gives the stuck
call `a + B`, likewise; so `B ≡ Succ B₁` and `a + B ≡ Succ (a + B₁)` (R4),
and `a + B₁ ≡ (k - 1) + t`. After `k` steps, `B ≡ k + Bₖ` with `a + Bₖ ≡
t`: the solution is `?m' := x₁ … xₙ => Bₖ`. So the rule loses no solution
(it is complete for this problem), and when `t ≡ a` the only `Bₖ` is
`Zero` by the same cases, which is `?m := k`. For `?m + a` the argument is
the same with R2 and R1 (a stuck `?m + a` means R3 and R4 didn't apply, so
`a` is no number or `Succ` either). This uses confluence (§9.4): a value
has one normal form, so "headed by `Succ`" is a property of the value.

**Soundness** doesn't depend on the argument above: a solution is still a
term the kernel re-checks, and `?m := k + ?m'` with `a + ?m' ≟ t` solved is
`a + (k + B') ≡ k + (a + B') ≡ k + t` by R4, so the original problem holds.

**What the conditions rule out, and why.**

- *`a` mentions an unknown* (`(?c + x) + ?d ≟ 3 + x`, or `?c + ?d ≟ Succ
  x`). `a` may then become a `Succ` (`?c := Succ ?c'`), and a solution
  that puts the `Succ` there instead is missed; committing would be
  incomplete, so the rule waits (the comparison fails as before, or a
  later one solves `?c`).
- *`?m` not applied to distinct variables* (`?m (Succ z)`). A solution can
  then be `y => y`, which isn't `y => Succ …`; the ordinary fallback
  (`first_order` in `unify.rs`) is left to it.
- *`t` mentions `?m`* (`x + ?d ≟ Succ ?d`). Peeling would never end
  (`?d := Succ ?d'`, then `x + ?d' ≟ Succ (Succ ?d')`, …); there is no
  finite solution anyway.
- *Termination.* Each step takes `k ≥ 1` `Succ`s off the other side and
  leaves `t`, which has none outside, so the rule fires at most once on a
  path through `t`'s outer layer; deeper `Succ`s are under a different
  head and reached only by comparing parts, which are smaller.

**What it doesn't do.**

- `a + ?m ≟ a` alone, with nothing to peel, is left alone, though `?m :=
  Zero` is its one solution. With it, `rewrite Nat.powAdd 10 k _` in 2025
  day 2's `multiplierSucc` found `Nat.pow 10 k` as `Nat.pow 10 (k + 0)`
  (`rewrite` finds occurrences by unification) and failed with
  `E-REWRITE-MOTIVE`, where it had found `Nat.pow 10 (k + k * i)`.
  Before (c) no sum matched a bare `k`; what the rule does match (`k + ?x`
  against `k + 3` or `Succ (k + t)`) is what matched as written then.
  `examples/reject/plus-unknown-against-itself.sw`.
- `a + ?m ≟ 0`, or against a stuck call, a variable, another sum: as
  before (`examples/reject/plus-unknown-against-zero.sw`).
- `*`, `-` and the other operations: nothing.

**`List.memBetween` needed something else** (`unify.rs`, `run` and
`blocked`). Its problem isn't a stuck sum. `List.between ?lo ?hi` unfolds
to `List.rangeFrom (Succ ?hi - ?lo) ?lo`, and `-` counts down its second
argument, so the first argument is stuck on `?lo`; `h`'s type is
`List.rangeFrom (n - 1) 2` (or `List.rangeFrom n 1` for `between 1 n`).
The arguments are compared first to first, so `Succ ?hi - ?lo` met `n - 1`
(the spines `Succ ?hi` and `n` differ) or `n` before `?lo := 2` was known,
and failed. On `main` before (c) it worked by shape alone: `?hi + 1` and
`n + 1` were both stuck, and `n + 1 - 2` stuck on `n + 1`. The fix is
general: a pair that fails while one side is a definition stuck on an
unknown (an argument an unsolved unknown, or `k +` one, or such a call,
three calls deep at most) is put aside and compared again after the rest
of the work list, read back and evaluated afresh, if anything was solved
meanwhile; if nothing was, it fails. Two calls of the same definition
stuck so are compared argument by argument as a nested run, so the calls
(not some argument pair inside them) are what is put aside. With `?lo :=
2`, `Succ ?hi - 2` computes to `?hi - 1`, which unifies with `n - 1`.

That is sound for the same reason (it only orders comparisons; every pair
is still unified, and the kernel checks), and it terminates: a pair put
aside is retried only after the trail of solutions has grown, and each
retry is a budget step. What it changes: a unification that fails because
of a blocked pair now does the rest of its work list before failing, and
keeps the solutions that made (solutions of a failed unification were
already kept; taking back either the put-aside pair's or the rest's broke
`std/List/Lemmas.sw`'s `List.appendNotEq`, whose `rewrite <- DecEq.sound _
_ made` relies on them, **[checked]**: both variants tried). Not covered:
a pair stuck on an unknown that is solved only after this unification
returns (the elaborator's own postponing, of lambdas and rows, is
separate), and calls stuck more than three deep.

**Reverted explicit arguments.** 2025 day 2 `Templates.sw` (`match
List.memBetween lengthChosen, List.memBetween copyCountChosen`) and rogue
`Rules.sw` `actAllDamage` (`outcome.add monster _ _`), each checked with
`--no-cache`, and each rejected by `main`'s binary (`E-TYPE-MISMATCH`,
`E-OMEGA`). Those are the only two SW-787 introduced for this (the lane's
diff of `aoc/` and `games/`; `git grep memBetween`); the rest of its
changes there were rewrites and proofs, not implicits.

**Tests.** `examples/accept/plus-unknown-summand.sw` (every case fails on
`main`'s binary): `x + ?d` against `Succ (x + 3)`, `Succ (x + t)`, `?d + x`
against `Succ (t + x)`, `Succ (x + ?d)` against `x + 3`, and
`List.memBetween h` under a `match` for `between 2 n` and `between 1 n`.
`examples/reject/plus-unknown-against-{zero,itself}.sw`.
`crates/driver/tests/nat_add_rule.rs`
`the_unifier_peels_succs_off_a_sum_stuck_on_an_unknown`: two solved, and
each condition's counterexample (`t` mentions `?d`, both summands unknown,
`a` mentions an unknown, `0`, `a` alone) still `E-REFL`.

**Measured.** `aoc`, `stitchwort check --no-cache`, user CPU time,
alternating runs, other lanes running: this branch 36.95, 36.71, 41.91 s;
`main`'s binary (on the same `aoc` with `main`'s `Templates.sw`) 36.44,
41.45, 37.03 s. No difference beyond the noise.

### 10.2 Printing sums (SW-895)

**Printing sums (as built, SW-895, D1977).** Printing `k + x` as `x + k`, once
under "Not done", is built, for display only. The rule: a value
`Value::NatAdd(k, x)` (`k ≥ 1` `Succ`s around an `x` that isn't a number)
is printed `x + k`, `x + 1` included; a `Value::Ctor` `Succ` is printed
`Succ x`; a number is printed as the number. Evaluation decides which a
term becomes, and it already keeps the two apart: `+` on either side (R2 by
the natives' shortcut, R4 by `nat_add::stuck`) returns a `NatAdd`, and so
does `Succ` of a `NatAdd` (`native::ctor`) and a native taking shared
`Succ`s off one (`x + 5 - 2` is `x + 3`); but `native::ctor` only compacts
`Succ` of a number or a `NatAdd`, so `Succ x` written in the source, and a
pattern's `Succ m` that a `match` or `cases` puts in a goal, stay
constructors. So `x + 1` and `1 + x` print as `x + 1`; `x + 3` and `3 + x`
as `x + 3`; `Succ (x + 2)` as `x + 3`; `x + (y + 2)` as `x + y + 2`; `Succ
x` and `Succ (Succ x)` as written. Where it can't follow the source: which
side the number was on isn't recorded (R2 and R4 give the same value), so
`3 + x` written prints `x + 3`, and so does `Succ k * 1`, which is `1 + k *
1` by `*`'s definition (`k * 1 + 1 = Succ k` in the guide); and a sum that
passes through an elaborated term, which the kernel's readback writes with
`Succ x` for `k = 1` (a rewritten hypothesis, an inferred type in `:t`),
comes back as a constructor and prints `Succ x` (`reject/rewrite-at-
mismatch.sw`: the goal `a + 1 = 5` against the rewritten `Succ b = 5`).
Larger `k` survive, as `k + x` terms evaluate back to `NatAdd`.

Where: `native::nat_add_shown` (`crates/core/src/native.rs`) builds the
printed term, used by the readback's `NatAdd` step for the two printing
modes, `Readback::Shown` (`quote_shown`: messages, goals, hover) and the
new `Readback::UnfoldedShown` (`quote_unfolded_shown`: `pretty::value`,
used by the REPL's `:t` and the JavaScript export's type text, and the
elaborator's "computing … gives" and "they first differ at" notes);
`quote` and `quote_folded`, which build the terms the kernel checks,
hashes and caches, still use `native::nat_add_term` and give the same
terms as before (`nat_add_rule.rs`, `stuck_sums_are_printed_as_written`,
checks both). The alternative the ticket named, keeping the sum as a
glued call (`Value::Call`) as written, would have recorded which side
the number was on, but `Nat.add` is a native and natives never glue
(`value::glues`): gluing it would change the values every comparison, the
unifier, `cases`, `omega` and `ring` see (each matches on `NatAdd`), so it
isn't display only.
