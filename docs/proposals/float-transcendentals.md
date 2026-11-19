# Proposal: `exp`, `log`, `cos` and friends, when JavaScript doesn't say what they return

**Status:** for Matt's decisions (SW-3783), 17 November 2026. A research and design note: nothing
here changes the compiler. Written against commit `7e96e99e4`. The decisions are
[at the end](#9-decisions-for-matt), unnumbered, each with a recommendation.

Labels: **[read]** (I read the primary source this session: the specification, the source file, the
commit message, the paper's text), **[cited]** (from an abstract, a talk's slides or a search
summary, not the full source), **[checked]** (read in this repository), **[inferred]** (my
reasoning), **[unverified]** (I believe it but didn't confirm it). No Stitchwort build or test was
run, and no benchmark of my own: every speed figure is someone else's measurement, with its source.

## One-page summary

**The problem.** A Stitchwort theorem is supposed to be about the code that runs in the browser.
For `+`, `-`, `*`, `/` and square root that works, because JavaScript's standard says exactly what
they return, bit for bit. For `exp`, `log`, `cos`, `sin`, `pow` and about twenty others it doesn't.
The standard says only that each returns "an implementation-approximated Number value": some
approximation, with no stated accuracy. So:

- Nothing can be proved about `Math.exp` from the standard. Not that it is within some distance of
  the true value, not that it is increasing, not even that `Math.exp(x) ≤ 1` when `x ≤ 0`.
- Browsers really do differ, and change. Firefox uses one library (fdlibm) for `exp`, Safari uses
  Apple's, and Chrome's engine swapped its whole maths library between May and November 2026.
  Chrome's own measurement of its old `Math.exp` found it gave the best possible answer on about
  80% of inputs; the new one on 100%. So the old and new Chrome disagree in the last digit on
  roughly one input in five.
- Whereabouts wants both proofs about scoring (which uses `exp`) and replays that give the same
  bits on the server (Node) and in every browser.

**What others do.** Everyone who needs the same answer everywhere stops calling the platform's
function and ships their own, written with only the exactly-specified operations. Java did this in
1998 (`StrictMath`: "the same results as certain published algorithms"). WebAssembly left these
functions out on purpose so that programs bring their own. Deterministic game engines and
blockchains do the same, or ban floats. Proof assistants split two ways: Lean leaves `Float.exp`
opaque and proves nothing about it; Rocq's interval library and HOL Light write the function in
the logic and prove an error bound for it. Nobody verified trusts the platform's `exp`.

There is good news on speed. It used to be thought that the best possible answer every time
("correctly rounded") was too slow. It isn't any more: the CORE-MATH project's correctly rounded
`exp` costs 18 processor cycles against 13 for the standard Linux library, and when Chrome's
engine switched to a correctly rounded library its `Math.exp` got *faster* (311 million calls a
second, up from 248 million).

**The change proposed.** Std's `Float.exp`, `log`, `cos` and the rest are ordinary Stitchwort
functions, written with `+`, `*`, `/` and bit operations. The exported JavaScript runs that
function; it never calls `Math.exp`. The function's definition *is* its meaning, in the checker, in
Node and in every browser. This is Java's `StrictMath` position. `Float.sqrt` is the exception: the
standard defines `Math.sqrt` exactly, so it can use the browser's.

A program that would rather have the browser's own `Math.cos` (for a hint band's width, say) keeps
today's route: the export takes the function as an argument, and what the proofs assume about it is
written as a hypothesis. Std adds no axioms about browsers.

**What it should do.**

- Theorems about `exp` are theorems about the code that runs, with nothing new to trust.
- Results are bit-identical on client and server, so replays agree.
- `byComputing` and tests can evaluate `exp`, because the checker has a definition to run.
- The cost is speed: our `exp` runs as compiled JavaScript, not the engine's C++. Nobody has
  measured that for this design, and I didn't either (estimated: within a small factor of
  `Math.exp`, because the engine's own function is the same kind of arithmetic). The first stage is
  to measure it, before anything is built.

**What Matt decides:** whether std's functions are our own definitions (recommended: yes); whether
they aim to be correctly rounded (recommended: yes, subject to the speed measurement); whether std
ever states axioms about a browser's function (recommended: no); and whether `Float.sqrt` goes in
now on the browser's `Math.sqrt` (recommended: yes).

---

## 1. The facts, checked

### 1.1 What ECMA-262 says

From the current draft at tc39.es/ecma262, section 21.3.2, "Function Properties of the Math Object"
[read, 17 Nov 2026]:

> The behaviour of the functions acos, acosh, asin, asinh, atan, atanh, atan2, cbrt, cos, cosh, exp,
> expm1, hypot, log, log1p, log2, log10, pow, random, sin, sinh, tan, and tanh is not precisely
> specified here except to require specific results for certain argument values that represent
> boundary cases of interest. For other argument values, these functions are intended to compute
> approximations to the results of familiar mathematical functions, but some latitude is allowed in
> the choice of approximation algorithms. The general intent is that an implementer should be able
> to use the same mathematical library for ECMAScript on a given hardware platform that is
> available to C programmers on that platform.
>
> Although the choice of algorithms is left to the implementation, it is recommended (but not
> specified by this standard) that implementations use the approximation algorithms for IEEE
> 754-2019 arithmetic contained in fdlibm …

- `Math.exp`: NaN and +∞ return themselves, ±0 returns 1, −∞ returns +0, and otherwise "Return an
  implementation-approximated Number value representing the exponential function of ℝ(n)" [read].
  `Math.cos` is the same shape: NaN for a non-finite argument, 1 for ±0 [read].
- `Math.pow` is `Number::exponentiate`, which also returns an implementation-approximated value
  outside its special cases [read].
- `Math.hypot` and `Math.cbrt` are implementation-approximated too [read].
- **`Math.sqrt` is exact:** "Return 𝔽(the square root of ℝ(n))" [read]. `𝔽` rounds to the nearest
  double, so this is the correctly rounded square root.
- There is **no accuracy bound** anywhere in the section, and no promise of monotonicity, symmetry
  or range [read].
- JavaScript has no fused multiply-add: `Math.fma` does not appear in the section [read]. This
  matters in section 5: fast correctly rounded code in C leans on it.

The brief's facts were right. One addition: `Math.pow` is specified through
`Number::exponentiate`, not in 21.3.2 itself.

### 1.2 Engines differ, and change

**V8 (Chrome, Node).** `src/base/ieee754.cc` on `main` today calls LLVM's libc for nearly
everything: `double exp(double x) { return LIBC_NAMESPACE::shared::exp(x); }`, and the same for
`cos`, `sin`, `tan`, `log`, `log2`, `log10`, `log1p`, `expm1`, `cbrt`, `acos`, `asin`, `atan`,
`atan2`, `cosh`, `sinh`, `tanh` and `pow` [read: github.com/v8/v8, `src/base/ieee754.cc`]. That is
new. The file's history [read: the commit list and messages on GitHub]:

| Date | Commit | What changed |
|---|---|---|
| 2019-10-23 | `b12ba06edf` | "stop using imprecise fdlibm pow": back to the system's `pow` |
| 2022-11-30 | `4588fe544f` | sin and cos may come from glibc instead of fdlibm (a build flag, on in Chromium) |
| 2024-11-19 | `55e89435d5` | "Use std::pow instead of our custom implementation" |
| 2026-05-08 to 05-20 | `96ce1682b7` … `43f04a52f2` | `cbrt`, `log`*, `tan`, `cos`/`sin`, `acos`/`asin`, `exp`/`expm1`, `pow`, `atan`/`atan2` moved to LLVM's libc |
| 2026-10-30 | `92ca3c4eef`, `71a27db3fb` | `cosh`, `sinh`, `tanh` moved to LLVM's libc |

The commit messages carry measurements from the author's benchmark (`nico/js-math-bench`), where
"% CR" is the share of test inputs given the correctly rounded answer [read]:

| Function | Before: max error, % CR, calls/s | After: max error, % CR, calls/s |
|---|---|---|
| `Math.exp` (`e5bb55463b`) | 1.00 ulp, 80.3%, 248.2M | 0.00, 100.0%, 311.2M |
| `Math.log` (`08be4445f6`) | 1.00 ulp, 80.7%, 241.1M | 0.00, 100.0%, 263.6M |
| `Math.cos`, fdlibm path (`7c1d2c3724`) | 1.00 ulp, 81.6%, 126.1M | 0.00, 100.0%, 230.3M |
| `Math.pow`, non-default path (`716d3e3363`) | 1.00 ulp, 93.1%, 58.0M | 1.00 ulp, 94.2%, 140.7M |

Three things follow.

- The old and new `Math.exp` disagree on about one input in five of that benchmark. Any replay
  that went through `Math.exp` breaks across that Chrome or Node upgrade.
- Even the new V8 is not correctly rounded throughout: "LLVM libm's pow() is not yet exact!" [read,
  `716d3e3363`], and V8's default `pow` is the C++ library's `std::pow`, so it varies by platform.
- The same commit message reports that production Chromium's `Math.sin` (the glibc path) had a
  **maximum error of 1063 ulp** on that benchmark, tracked as crbug.com/511271840 [read,
  `7c1d2c3724`; I did not open the bug]. An axiom "the browser's `sin` is within 1 ulp" would have
  been false of shipping Chrome.

Which Chrome and Node releases carry the May and October 2026 changes is [unverified].

**SpiderMonkey (Firefox).** `js/src/jsmath.cpp` calls fdlibm for `exp`, `log`, `acos`, `asin`,
`atan`, `atan2`, the hyperbolics and others (`return fdlibm_exp(x);`), and for `sin`, `cos` and
`tan` calls either fdlibm or the platform's `std::sin`/`std::cos`, chosen by a preference
(`use_fdlibm_for_sin_cos_tan`) [read: github.com/mozilla/gecko-dev, `js/src/jsmath.cpp`]. The
preference came from a 2021 change made against fingerprinting: Firefox "chooses to use the local,
platform-supplied math library" for sin, cos and tan, which let sites tell operating systems apart
by the last digits; the same post measures fdlibm within 3% of the platform on macOS and Linux
and 27% to 73% slower on Windows benchmarks [read: Tom Ritter, "Intent to Implement: Use fdlibm
for Math.cos, Math.sin, and Math.tan…", dev-platform, 23 July 2021,
groups.google.com/a/mozilla.org/g/dev-platform/c/0dxAO-JsoXI].

**JavaScriptCore (Safari).** `MathObject.cpp` routes `Math.cos`, `Math.exp` and `Math.log` through
its own `Math::` namespace, and `MathCommon.cpp` holds an fdlibm-derived `pow` [read:
github.com/WebKit/WebKit]. That the rest call the platform's C library (Apple's, on a Mac) is from
a 2020 write-up, which says V8 and SpiderMonkey use slightly different ports of fdlibm and
JavaScriptCore uses the C library for most operations [cited: Tom MacWright, "Math keeps
changing", macwright.com/2020/02/14/math-keeps-changing]; I did not trace it in the source
[unverified].

**How far apart the underlying libraries are.** Zimmermann and others keep a comparison of maths
libraries' largest *known* errors, in ulps (units in the last place; 0.5 is perfect). From the
August 2026 edition, double precision [read: Gladman, Innocente, Mather, Ozaki and Zimmermann,
"Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision",
members.loria.fr/PZimmermann/papers/accuracy.pdf, Table 3]:

| | GNU libc 2.44 | Apple 26.5.2 | LLVM libc 22.1.8 | MSVC 2026 | FreeBSD 15.1 (fdlibm family) |
|---|---|---|---|---|---|
| `exp` | 0.511 | 0.521 | 0.500 | 1.50 | 0.949 |
| `log` | 0.520 | 0.508 | 0.500 | 0.577 | 0.946 |
| `cos` | 0.516 | 0.948 | 0.500 | 0.897 | 0.834 |
| `tan` | 0.619 | 3.53 | 0.500 | 1.32 | 1.02 |
| `pow` | 0.523 | 0.757 | Inf (a bug) | 0.505 | 636 |

The paper's summary: "All LLVM functions except atan, atan2, and pow seem to be correctly rounded"
and "current mathematical libraries do not provide correct rounding … Thus, users might get
different results with different libraries, or different versions of the same library" [read].
These figures are lower bounds found by search, not proofs.

So the claim "engines differ in the last bit and change between versions" is confirmed, and is
too mild: the differences are frequent (about 20% of inputs between an fdlibm engine and a
correctly rounded one), and now and then large (a `tan` 3.5 ulp out, a `sin` 1063 ulp out, a `pow`
with an infinite error).

### 1.3 Stitchwort today

- `Float` is a record around a double's 64 bits, with one NaN [checked: `docs/core.md`, "Float"].
- `Float.add` and `sub` are definitions through `Float.Model` (exact, then round), with proved
  laws. `mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt` and `ofNat` are bodyless
  primitives the kernel computes with Rust's `f64` under `FLOAT_CONTRACT` [checked: `docs/core.md`;
  `DESIGN.md`'s trusted-base table; `crates/core/src/float.rs:71`]. The accepted plan is for those
  to become definitions too (float-laws.md §10, stages 3 and 4) [checked].
- `Float.toText` is a primitive "with no rule at all: the kernel never computes it, and each
  runtime supplies its meaning … which must be a pure function of the double (D688)" [checked:
  `docs/core.md`].
- The float note already ruled these functions out of stage 1, for this reason: Rust says of its
  own `f64::exp` that its "precision … is non-deterministic", and JS says
  "implementation-approximated" [checked: `docs/proposals/float.md` §3.6]. It also says "`sqrt` is
  correctly rounded in both, so it can join later without a decision" [checked].
- A program can already take a function as an export's argument, and state what it assumes about
  it as hypotheses: the "operations record" of float.md §6.2 (D689) [checked].

The Rust point closes one door. `mul` works as a kernel primitive because Rust's `*` and JS's `*`
are the same exactly-specified operation. There is no such shared `exp`: the kernel cannot "just
call `f64::exp`" as it calls `f64` multiplication, because that isn't one function either.

### 1.4 What Whereabouts needs

From `/Users/matt/repos/mdr/whereabouts/docs/stitchwort-candidates.md` [read]:

- **Hint bands** divide by `cos(lat)` only to size a longitude band. The note itself says the
  theorems "can take any width in (0, 120] as an input. Then nothing needs trigonometry."
- **Scoring** uses a kernel `Σ w_c · 2^−(d/(s_c·r))²` and wants `0 ≤ score ≤ 1000` and properness.
  The bounds need only that each kernel value is in [0, 1]; properness "rests on Gaussian mixtures
  being positive definite on the sphere", which is real analysis, "probably best assumed at first".
  The note offers the same two choices this one studies: "pass `exp` in and assume its properties,
  or for Stitchwort to own an `exp` approximation with a proven error bound."
- **Replays**: "Any port must give the same results bit for bit, because replays depend on them."
  The note says this of the seeded shuffle; the brief extends it to scores.

## 2. Prior art

### 2.1 Correctly rounded libraries

"Correctly rounded" means the function returns the double nearest the true value, every time. It
is the only specification that doesn't depend on an algorithm, and it is what `+` and `sqrt`
already have. The obstacle is the *table maker's dilemma*: a true value can lie so close to the
halfway point between two doubles that an approximation must be very precise to tell which side it
is on, and nobody knows in advance how precise without searching for the worst cases.

- **IEEE 754-2019** lists these functions in clause 9.2, "Recommended correctly rounded functions":
  recommended, not required. "The IEEE 754 standard, even in its latest 2019 revision, does not
  require correctly rounded mathematical functions, it only recommends them" [read: the accuracy
  paper above; the clause title is from a glibc mailing-list post about the 2008 edition, cited].
  I did not read the standard itself (it is paywalled).
- **CRlibm** (Lyon, 2000s) was the first correctly rounded double-precision library with proofs,
  its error bounds machine-checked with Gappa [cited]. It is slow and no longer maintained: its
  `pow` takes 211 cycles against glibc's 43 [read: Zimmermann, "CORE-MATH: progress report", 2023
  slides, members.loria.fr/PZimmermann/talks/core-math-fpbench2023.pdf].
- **CORE-MATH** (Inria; Sibidanov, Zimmermann and others; MIT licence) provides correctly rounded
  single, double and extended functions meant for other libraries to adopt, including double
  `exp`, `exp2`, `log`, `cos`, `sin` and `pow` [read: core-math.gitlabpages.inria.fr].
  - Speed: double `exp` 18 cycles, against GNU libc 13 and Intel 23 (2023, AMD EPYC 7282; the 2022
    version took 32). Double `pow` 66 cycles against GNU libc 43 [read: the 2023 slides].
  - How sure: "For univariate binary32 functions it is checked by exhaustive search. For bivariate
    functions or larger formats it is checked only with respect to known hard-to-round cases"
    [read: the project page]. Some functions have paper proofs; a formal Coq proof of `pow` was
    started, and part of `log`'s argument reduction is formally proved [read: the 2023 slides].
  - Adoption: GNU libc 2.43 uses its code for seven double functions and many single ones [read:
    the project page]. An integration can go wrong: glibc 2.44's `sinh` "yields huge errors … due
    to a bug in the integration from the CORE-MATH code" [read: the accuracy paper].
- **RLIBM** (Rutgers; Lim and Nagarakatte) generates polynomials that hit the correctly rounded
  *result* directly, by linear programming against an oracle. It covers 32-bit floats, where every
  input can be checked, in all rounding modes, and reports being faster than mainstream libraries
  [cited: arXiv 2104.04043, 2108.06756]. It doesn't reach doubles.
- **LLVM libc** aims at correct rounding for doubles and, per section 1.2, is now what V8 runs.

The summary of the state of the art, from the accuracy paper: "at least for single precision and
most double precision functions, it is known how to get correct rounding … at very low cost, and
reference implementations exist that outperform current libraries" [read].

### 2.2 Java: a loose contract with stated bounds, and a strict twin

Java has both designs side by side, which makes it the closest precedent.

- `StrictMath`: "the definitions of some of the numeric functions in this package require that
  they produce the same results as certain published algorithms … fdlibm. These algorithms, which
  are written in the C programming language, are then to be understood to be transliterated into
  Java and executed with all floating-point and integer operations following the rules of Java
  arithmetic" [read: Java 21 API, `java.lang.StrictMath`]. The algorithm is the specification.
  Bit-identical everywhere; not correctly rounded.
- `Math`: "all implementations of the equivalent functions of class Math are not defined to return
  the bit-for-bit same results. This relaxation permits better-performing implementations where
  strict reproducibility is not required." Its contract is an error bound plus a shape:
  `Math.exp` and `Math.cos` say "The computed result must be within 1 ulp of the exact result.
  Results must be semi-monotonic." And: "it is impractical for many floating-point methods to be
  correctly rounded" [read: Java 21 API, `java.lang.Math`]. `Math.sqrt` is exact.

Java could write the loose contract because Java owns its implementations. Stitchwort doesn't own
the browsers', and JavaScript's standard has no such contract to lean on.

### 2.3 Verified systems

| System | What it does with `exp` and friends | Source |
|---|---|---|
| **Lean 4** | `Float` has been a structure over a model since 4.33, and `Float.sqrt` is defined through the model. `Float.exp`, `log` and `cos` are still `@[extern]` `opaque`: compiled to C's `exp`, not reducible in the kernel, with no theorems | [read: lean-lang.org/doc/api, `Init.Data.Float`; release notes 4.33.0, cited] |
| **Rocq primitive floats, Flocq** | The primitives are `+ - * /`, `sqrt` and a few bit operations, each tied to Flocq's model by an axiom (float-laws.md §4.1). No transcendental primitive. Flocq is a theory of formats and rounding over the reals; it doesn't implement `exp` | [checked: float-laws.md §4.1, §4.3]; the absence is [inferred] from those lists |
| **CoqInterval** | Proves real-number inequalities by interval arithmetic. Its `exp` is written in Rocq. In 2024 it was replaced by "an actual floating-point function defined in the logic of the Coq proof assistant", a faithful double `exp` with tables and bit manipulation, fully verified, 20× faster than the previous one | [read: abstract of Faissole, Geneau de Lamarlière and Melquiond, "End-To-End Formal Verification of a Fast and Accurate Floating-Point Approximation", ITP 2024, doi 10.4230/LIPIcs.ITP.2024.14] |
| **Gappa** | Bounds rounding errors in straight-line float code and emits proofs Rocq can check. It is the tool CRlibm's and CoqInterval's proofs use for the "polynomial evaluated in floats" step; it has no notion of `exp` itself | [cited]; the last clause [unverified] |
| **HOL Light** (Harrison) | A machine-checked proof of Tang's table-driven `exp` algorithm: the result is within 0.54 ulp of the true value (0.77 if subnormal), tighter than Tang's own analysis | [cited: abstract of Harrison, "Floating point verification in HOL Light: the exponential function", UCAM-CL-TR-428, 1997; Formal Methods in System Design 16, 2000] |
| **Isabelle** | The IEEE formalisation (AFP `IEEE_Floating_Point`) covers the basic operations; no transcendental functions | [unverified] |
| **CompCert** | Proves that compilation preserves IEEE semantics for the basic operations. Maths-library calls are external calls: "calls to the standard library are just calls to external functions", about which it "makes no assumption". Only `fabs`, `sqrt`, and per-target `fmax`/`fmin`/fused multiply-add are built in | [cited: Monniaux and Boulmé, "The Trusted Computing Base of the CompCert Verified Compiler", arXiv 2201.10280; read: CompCert manual, chapter 6] |
| **CakeML** | 64-bit doubles with the basic operations, `sqrt` and fused multiply-add as primitives. Elementary functions come from separate work that generates and verifies approximations (Dandelion, libmGen) | [cited: Becker's posts and thesis]; that there are no transcendental primitives is [unverified] |
| **FPTaylor, Rosa, Daisy** | Error-bound tools: they bound the rounding error of an expression against the real-number ideal. For library calls they *assume* an error for the library ("assuming libm library function implementations"); Daisy can instead generate a polynomial with a certified bound (through Metalibm) and reports it 2.9% to 17.6% faster than libm on one example, by being less accurate | [read: Darulova and Volkova, "Sound Approximation of Programs with Elementary Functions", CAV 2019, arXiv 1811.10274]; the exact assumed bound is [unverified] |
| **WebAssembly** | Left out on purpose: "WebAssembly doesn't include its own math functions like sin, cos, exp, pow, and so on. WebAssembly's strategy for such functions is to allow them to be implemented as library routines in WebAssembly itself". Its remaining float nondeterminism is NaN bits, which the deterministic profile removes | [read: WebAssembly/design `FAQ.md` and `Rationale.md`; spec appendix "Profiles"] |

The pattern: **no verified system proves anything about a platform's transcendental function.**
Those that prove something (CoqInterval, HOL Light, CRlibm) write the function themselves, in or
next to the logic, and prove an error bound for that code. Those that call the platform's (Lean,
CompCert) say nothing about the result.

### 2.4 Deterministic replay

- **Lockstep games** send only inputs and need every machine to compute the same state. The
  standard advice: floats are deterministic only with one compiler, one instruction set and no
  platform maths library; otherwise use fixed-point [cited: Glenn Fiedler, "Floating Point
  Determinism" and "Deterministic Lockstep", gafferongames.com; a GDC 2024 talk on cross-platform
  determinism that recommends fixed-point].
- **Rapier** (a Rust physics engine) offers cross-platform determinism as a feature
  (`enhanced-determinism`) that swaps the platform's functions for a software library, and asks
  callers to take their own trigonometry from the same place [cited: rapier.rs, "Determinism"].
- **Blockchains** need every validator to agree. CosmWasm "on purpose does not implement
  floating-point Wasm instructions" at all [cited: book.cosmwasm.com]; the EVM has no floats
  [unverified, common knowledge].

Again the pattern is one of two: ship your own function built from exact operations, or avoid
floats.

## 3. The options

Each option is judged on four things: what a theorem then says about the running code, speed, the
same bits across engines, and what is added to the trusted base.

### (a) Our own correctly rounded function, which is the definition

`Float.exp` is a Stitchwort function that returns the nearest double to the true value. Exported
JS runs it.

- **Proofs.** Sound for the running code with nothing new trusted: the code that runs is the code
  the theorems are about. Proving that it *is* correctly rounded is a research project (CORE-MATH's
  own double functions are "checked only with respect to known hard-to-round cases"), but that
  proof is not needed for soundness. Only "the definition is the meaning" is.
- **Speed.** In C, near parity: 18 cycles against 13, and faster than fdlibm in V8's measurement.
  In JavaScript, unmeasured. Two things are missing there: fused multiply-add, and 128-bit
  integers for the rare slow path [inferred from 1.1 and CORE-MATH's sources' use of both; not
  measured].
- **Same bits everywhere.** Yes, and more: the same bits as any other correctly rounded library
  (LLVM's, CORE-MATH), so a Rust or C server could agree with it without running Stitchwort.
- **Trusted base.** Unchanged.

### (b) The host's function as an opaque primitive, with axioms about its accuracy

`Float.exp` has no body; std states axioms (within 1 ulp, increasing, `exp 0 = 1`).

- **Proofs.** The logic stays consistent, since some function does satisfy the axioms. But the
  theorems are about that imagined function. They are about the running code only if every engine
  the code ever meets satisfies every axiom, which the standard doesn't promise and section 1.2
  shows is false in practice (`sin` 1063 ulp out in Chrome; `tan` 3.5 ulp out in Apple's library).
  This is the one option where a Stitchwort theorem can be false of the program as run, silently.
- **Speed.** Full native speed.
- **Same bits.** No. Replays break across browsers and across upgrades.
- **Trusted base.** New axioms in std, about software nobody here controls. `byComputing` cannot
  evaluate anything that reaches `exp`.

### (c) Quantify over any function that meets a stated bound

No std function at all: code takes `exp` as a parameter, and theorems read "for every `exp` that
is within such-and-such, …". This exists today (float.md §6.2, D689).

- **Proofs.** Honest: the assumption is on the page, at the export, and can be read in the
  theorem. It carries the same real-world risk as (b), but the logic and std stay clean, and the
  theorem can be instantiated with *any* function, including a std definition from option (a),
  whose hypotheses can then be proved rather than assumed.
- **Definitional equality and `byComputing`.** A parameter is a variable, so nothing reduces
  through it: no closed computation, no test by evaluation, unless the test supplies an instance.
  Conversion is otherwise untouched. One subtlety: a function parameter models the host as a pure
  function. If an engine's tiers disagreed with each other, even that would be too strong, and the
  fully honest model is an ability (an effect) with a relation for a specification. I know of no
  current engine bug of that kind [unverified], and I don't recommend going that far.
- **Speed.** Full native speed. **Same bits.** No.
- **Trusted base.** Unchanged.

### (d) Check the host's result at run time

Call `Math.exp`, then test the answer against a cheap certified bound; fall back if it fails.

- For `sqrt`-like functions a check is cheap (multiply back). For `exp` there is no cheap check:
  deciding whether `y` is within 1 ulp of `e^x` costs as much as computing `e^x` to that accuracy
  [inferred]. So the check is our own `exp` plus a comparison, slower than option (a) alone, and
  still not the same bits everywhere.
- One degenerate case is useful, and needs nothing from Stitchwort: **clamp**. If the score is
  written `clamp 0 1000 (…)`, then `0 ≤ score ≤ 1000` holds for any `exp` whatever. Whereabouts
  already clamps region scores at 0. That buys range theorems and nothing else.

### (e) Correctly rounded by specification, `Math.*` where the engine is known to match

The definition is (a)'s. On an engine whose `Math.exp` is correctly rounded, the runtime calls it
instead, as a *native*: Stitchwort's existing notion of a faster implementation that must give
exactly what the definition gives.

- **Proofs.** Sound exactly when the engine's function equals the definition on every input.
  Today that is known for no engine. V8's new `exp`, `log`, `sin` and `cos` *seem* correctly
  rounded by testing; its `pow` and `atan` are not; Firefox's and Safari's are not. Nobody promises
  it stays so, and a correctly rounded library can be integrated wrongly (glibc 2.44's `sinh`).
- **Same bits.** Only while every engine keeps matching. One that drifts breaks replays silently.
- **When it becomes right.** If ECMA-262 ever *requires* correct rounding for a function, that
  function moves into `sqrt`'s category and this option is simply correct for it. I found no TC39
  proposal to do so [searched; none found]. Option (a) is the only definition that leaves this door
  open: a correctly rounded definition can later be served by a correctly rounded engine without
  changing any result.

### (f) Our own function with a fixed algorithm and a proved error bound, not correctly rounded

Java's `StrictMath`, HOL Light's `exp`, CoqInterval's `exp`: pick an algorithm (an fdlibm-style
one, say), make it the definition, and prove "within 1 ulp" rather than "nearest".

- Everything said of (a) holds: sound, deterministic, nothing new trusted.
- It is simpler to write and to prove a bound for. Its fast path is the whole function, so its
  speed is predictable. The price is that its meaning is "whatever this algorithm returns": it can
  never be swapped for an engine's function or a better algorithm without changing results, and it
  agrees bit for bit with nothing else in the world.

### (g) Ship someone else's library, compiled to WebAssembly

Compile CORE-MATH or LLVM's libc to a Wasm module and call it from the exported JS. WebAssembly's
arithmetic is deterministic apart from NaN bits, so this gives the same bits everywhere and
near-native speed [inferred]. But the function is then C code outside the logic: the checker can't
compute it, nothing can be proved about it, and the kernel would need its own matching copy. It is
option (b) with determinism. I mention it because it is the cheapest route to bit-identical
replays alone, for a program that wants no theorems about `exp`.

### Side by side

| | Theorems hold of the running code | Speed | Same bits across engines | New trust |
|---|---|---|---|---|
| (a) own, correctly rounded | yes | compiled JS; unmeasured | yes, and with other correctly rounded libraries | none |
| (b) opaque + axioms | only if every engine obeys the axioms; known false cases | native | no | axioms about browsers |
| (c) quantify over implementations | yes, under a visible hypothesis | native | no | none |
| (d) run-time check | yes | slower than (a) | no | none |
| (e) (a) plus `Math.*` as a native | only where the engine provably matches: nowhere today | native where used | only while engines match | an equality with each engine |
| (f) own, fixed algorithm, bounded | yes | compiled JS; unmeasured | yes | none |
| (g) a C library as Wasm | nothing provable | near native | yes | the library, twice |

## 4. What the kernel and the checker compute

There are three existing ways a float operation can stand in the kernel [checked: `docs/core.md`]:

1. **A definition** (`add`, `sub`). The checker computes it through its body. A native may replace
   it while a program runs, and must give exactly the same result.
2. **A primitive with a rule** (`mul`, `div`, …). The kernel computes it with Rust's `f64`, trusted
   under `FLOAT_CONTRACT`, on the grounds that Rust and JS specify the same exact operation.
3. **A primitive with no rule** (`toText`). The kernel never computes it. Each runtime supplies it.

Where can `exp` go?

- **Not 2.** There is no single exact `exp` that Rust and JS share (section 1.3). A rule would
  have to name one particular algorithm, at which point it is a definition written in Rust instead
  of Stitchwort, trusted instead of checked. Position 1 is that, without the trust.
- **3 is option (b) without the axioms.** It is honest as far as it goes: `Float.Host.exp 1.0`
  would be stuck in the checker, total when run, and nothing could be proved about it. `toText`
  is acceptable there because programs need the text at run time, not theorems about it. A score
  is the opposite: the theorems are the point. Position 3 also needs "a pure function of the
  double" (D688), which is true of an engine's `exp` only one engine version at a time.
- **1 is options (a) and (f).** `byComputing` works: slowly while `add` goes through the model
  and fast once a run-time native exists, as for every float operation today.

**Can the checker compute a defined version while the runtime calls the host?** That is the native
arrangement, and it is sound exactly when the host equals the definition on every input. A proof
by computation, say a test that a particular score is `873.25`, is a statement about the
definition. If the browser's `exp` differs in the last bit on some input, the running program can
return `873.2500000000001` and the theorem is false of it. So:

- under (a) or (f) with the runtime running the definition: sound, by construction;
- under (e): sound only for an engine whose function is correctly rounded on every input, which
  can't be established today;
- under (b), (c), (d) and (g): there is no definition to compute, so the question doesn't arise,
  and nothing about closed values can be proved.

`toText` is not a counterexample. The kernel never computes it, so no theorem by computation
depends on what a host returns.

**Cost in the checker (estimated, not measured).** A closed `add` in checking costs "a few
milliseconds" through the model (float-laws.md §0, measured there on a stand-in); `mul` is a Rust
primitive today and fast. An `exp` is a table lookup and some tens of additions and
multiplications, so on the order of 0.1 s per closed `exp` inside a proof. That is fine for a
handful of values in a lemma and useless for a 6,000-cell score; tests and programs run with
natives and are not affected.

## 5. Determinism against speed

Only (a), (f) and (g) give client and server the same bits. All three do it the same way: the
program carries its own function and uses nothing from the platform but exact operations. The
cost is whatever our function loses to the engine's.

What is known about that cost:

- The engine's own function is the same kind of code. Until May 2026 V8's `Math.exp` *was* fdlibm,
  a few dozen floating-point operations in C++, at 248 million calls a second [read]. Firefox's
  still is [read].
- V8 once shipped its `sin`, `cos` and `tan` as fdlibm translated into JavaScript, so that calls
  could be inlined into generated code, before moving to fdlibm in C++ [cited: V8's
  `third_party/fdlibm/README.v8`, 2014; MacWright 2020]. So "maths library in JS" has been
  production-grade in a browser.
- Firefox measured fdlibm against platform libraries at ±3% on macOS and Linux and 27% to 73%
  slower on Windows [read, section 1.2]. That is C against C, but it bounds how much an older
  algorithm loses to a tuned one.
- A correctly rounded algorithm costs a little more than a plain one in C (18 against 13 cycles)
  and has an occasional slow path.

What is not known, and what I couldn't find measured anywhere: how Stitchwort's *extracted* JS for
such a function compares with `Math.exp` in each engine. Three things could hurt: `Float` values
boxed or bit-converted where a JIT wants bare numbers; table lookups; and, for a correctly rounded
algorithm, emulating fused multiply-add with a dozen plain operations. My estimate is 2× to 5×
slower than `Math.exp` for (f) and somewhat worse for (a) [inferred, low confidence]. Whether that
matters depends on the program: Whereabouts' kernel sums are a double loop over up to 6,000 cells
with a distance cut-off, so `exp` is on its hot path.

This is the number the design turns on, so stage 0 below measures it before anything is built.

## 6. Recommendation

**End state: std's transcendental functions are Stitchwort definitions, aiming to be correctly
rounded; `sqrt` uses the host; the host's other functions stay outside std.** In detail:

1. **`Float.exp`, `exp2`, `log`, `log2`, `sin`, `cos`, `atan2`, `pow` and the rest are definitions
   in std**, written over the exactly-specified operations. Exported JS runs the definition and
   never calls `Math.*` for them. The kernel computes them through the definition. Options (a)/(f).
   This is the only family where theorems, tests by computation and replays all hold together, and
   it adds nothing to the trusted base.

2. **They aim to be correctly rounded** (option (a) rather than (f)), provided stage 0 finds the
   speed acceptable. The reasons are all about the end state:
   - "the nearest double to the true value" is the only meaning that doesn't name an algorithm,
     so the algorithm can be improved later without changing a single result or replay;
   - it agrees bit for bit with other correctly rounded libraries, which is where V8, glibc and
     the IEEE recommendation are heading, so a non-Stitchwort server could match it;
   - it keeps option (e) open: if a standard ever requires correct rounding, `Math.exp` becomes a
     legitimate native and the speed comes back for free.

   Correct rounding would at first be established by testing against CORE-MATH's hard cases and
   MPFR, not by proof, and documented that way. Soundness doesn't wait for it: a definition that
   turned out not to be correctly rounded on some input would be a quality bug, not a false
   theorem.

   If stage 0 shows a correctly rounded `exp` is too slow in JS and a fixed-algorithm one is fine,
   take (f) and say so plainly in the docs: "deterministic, within 1 ulp, not correctly rounded".

3. **`Float.sqrt` is a definition with a native, like `mul`**: the kernel computes it through
   `Float.Model.sqrtBits` (an exact integer square root, rounded once), and runs use `Math.sqrt` and
   Rust's `sqrt`, both exact by their specifications (done, SW-3788).

4. **No axioms about engines, and no opaque host functions in std** (not (b), not a
   `Float.Host`). A program that wants the browser's `Math.cos` passes it in at the export and
   states what it relies on, as today (option (c)). Std helps in one way: it defines the usual
   hypotheses once (a record such as "`f` is within `k` ulp of std's function on this interval",
   "`f` is non-decreasing"), and std's own function satisfies them, so a theorem proved against the
   hypotheses applies to the deterministic function with no assumption left.

5. **Not (d) or (g)** as language features. Clamping is a program's own choice, and worth
   recommending to Whereabouts for its range theorems whatever else happens.

**What theorems can say, and when.** Stitchwort has no real numbers yet (float-laws.md, D1365),
so "within 1 ulp of `e^x`" can't even be stated today. Laws come in two tiers:

- *Float-only facts*, provable with what exists: no NaN from a finite argument, `exp 0 = 1`,
  `0 ≤ exp x`, `exp x ≤ 1` for `x ≤ 0`, `cos` in [−1, 1], symmetry of `cos`. These are what
  `0 ≤ score ≤ 1000` needs.
- *Accuracy and monotonicity*, which need a specification of the true function: either real
  numbers, or enclosures by exact rationals (the series for `e^x` with an explicit remainder). That
  is its own piece of work, and Whereabouts' properness theorem needs real analysis regardless.

**For Whereabouts.** Hint bands need nothing (take the width as an input), or use std's `cos`.
Scoring uses std's `exp2` or `exp`: the bounds follow from the float-only facts, and server and
every browser compute the same score to the bit. Scores will differ in the last digits from
today's TypeScript, which calls the engine.

## 7. A staged path

Each stage is one lane. Times are not estimated here; the orchestrator estimates from past lanes.

0. **Measure first** (no std change). Hand-write two `exp`s in plain JS, one fdlibm-style and one
   correctly rounded in CORE-MATH's style without fused multiply-add, and time both against
   `Math.exp` in Node, Chrome, Firefox and Safari, alone and inside a Whereabouts-shaped kernel
   sum. Then the same two written in Stitchwort and extracted, to see what extraction costs. Stop
   rule: a recommendation between (a) and (f), or a report that neither is within 5× of `Math.exp`
   on the kernel sum, in which case this note's recommendation is reopened. The benchmark is a JS
   microbenchmark, not one of the project's suites, but it is still a measurement lane and needs
   the orchestrator's say on where it runs.
1. **`Float.sqrt`** as a definition with a native, with the four-path comparison tests the other
   operations have (done, SW-3788).
2. **`Float.exp`, `exp2` and `log` as definitions**, with: bit-identity across the kernel, the Rust
   runtime, Node and a browser on a shared edge set; comparison with CORE-MATH's worst-case files
   and MPFR; the float-only laws; guide and `docs/syntax.md` entries. This unblocks the Whereabouts
   scoring pilot's bounds.
3. **`sin`, `cos`, then `atan2`, `pow`** as programs ask. Trigonometric argument reduction for
   huge arguments is the hard part; a first version may be stated for a bounded domain.
4. **The accuracy theory**: a specification of the true functions (rational enclosures or reals),
   then proved bounds and monotonicity. Depends on `mul` and `div` being definitions (float-laws.md
   stages 3 and 4).
5. **Std's hypothesis records for host functions**, when a second program wants to pass one in.
6. **Natives from the host, per function**, only if and when ECMA-262 requires correct rounding
   for it. Nothing to do until then.

## 8. Risks and open points

- **The speed estimate may be wrong.** That is what stage 0 is for.
- **Correct rounding in JS may be awkward** without fused multiply-add and wide integers. The slow
  path can use exact `Nat` arithmetic, as `Float.Model` does; it is rare, so it affects the worst
  case, not the average. [inferred]
- **Constant tables** (64 to 128 doubles) need to be cheap in the kernel and in extracted JS.
- **Result changes are breaking for stored replays.** Once Whereabouts stores replays, any change
  to a function's results invalidates them. Correct rounding makes results final; a fixed
  algorithm makes them final only by never touching it. This is the strongest practical argument
  for (a) over (f).
- **What I didn't verify** is marked in the text: which Chrome and Node releases carry V8's new
  library; JavaScriptCore's use of the platform library beyond the files I read; Isabelle's and
  CakeML's exact primitive lists; the text of IEEE 754-2019 clause 9.2; Chromium bug 511271840
  itself.

## 9. Decisions for Matt

Unnumbered; the orchestrator numbers them.

**Are std's `exp`, `log`, `cos` and friends our own definitions, the same bits everywhere, rather
than the browser's `Math.*`?**
- Yes: definitions in std; exported JS runs them. Theorems, tests and replays all hold; slower
  than the engine's by an amount stage 0 measures. **[Recommended]**
- No: opaque host functions, as `Float.toText` is. Full speed; nothing provable about them;
  results differ by browser and version.

**Should those definitions aim to be correctly rounded?**
- Yes, if stage 0 finds it within reach in JS: the meaning names no algorithm, results never need
  to change, and a host function can serve it if a standard ever requires the same. Established by
  testing first, proof later. **[Recommended]**
- No: a fixed fdlibm-style algorithm with a 1 ulp bound (Java's `StrictMath`). Simpler and more
  predictable; its results are tied to that algorithm for good.

**May std state axioms about what a browser's `Math` function returns (an ulp bound,
monotonicity)?**
- No. The standard promises none of it, and real engines have broken such bounds. Programs that
  want the host's function pass it in with their assumptions visible. **[Recommended]**
- Yes, a small audited set. Fast and convenient; the one option under which a theorem can be
  silently false of the running program.

**Add `Float.sqrt` now, on the host's `Math.sqrt`?**
- Yes: JavaScript and Rust both define it exactly, so it is the same kind of primitive as `mul`.
  float.md already says it "can join later without a decision"; listed here for completeness.
  **[Recommended]**
- Wait until a program asks.

**Run stage 0 (the speed measurement) before any std work?**
- Yes. The choice between correctly rounded and fixed-algorithm, and the confidence in the whole
  recommendation, rest on one number nobody has. **[Recommended]**
- No: build `exp` first and measure it afterwards.

## Sources

Specifications and source code, read 17 November 2026:

- ECMA-262 draft, §21.3.2 and `Number::exponentiate`: https://tc39.es/ecma262/multipage/numbers-and-dates.html, https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html
- V8, `src/base/ieee754.cc` and its history: https://github.com/v8/v8/blob/main/src/base/ieee754.cc; commits `b12ba06edf`, `4588fe544f`, `55e89435d5`, `08be4445f6`, `7c1d2c3724`, `e5bb55463b`, `716d3e3363`, `8787f0842a`, `92ca3c4eef`, `fe66319256`
- SpiderMonkey, `js/src/jsmath.cpp`: https://github.com/mozilla/gecko-dev/blob/master/js/src/jsmath.cpp
- JavaScriptCore, `runtime/MathObject.cpp`, `runtime/MathCommon.cpp`: https://github.com/WebKit/WebKit/tree/main/Source/JavaScriptCore/runtime
- Tom Ritter, "Intent to Implement: Use fdlibm for Math.cos, Math.sin, and Math.tan to prevent math-based fingerprinting", 23 July 2021: https://groups.google.com/a/mozilla.org/g/dev-platform/c/0dxAO-JsoXI
- Java 21 API, `java.lang.Math` and `java.lang.StrictMath`: https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Math.html, https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/StrictMath.html
- WebAssembly design `FAQ.md` and `Rationale.md`: https://github.com/WebAssembly/design; spec appendix "Profiles": https://webassembly.github.io/spec/core/appendix/profiles.html
- Lean API, `Init.Data.Float`: https://lean-lang.org/doc/api/Init/Data/Float/Float.html
- CompCert manual, chapter 6: https://compcert.org/man/manual006.html

Papers, talks and project pages:

- Gladman, Innocente, Mather, Ozaki, Zimmermann, "Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision", August 2026 [read: introduction, Table 3 and its discussion]: https://members.loria.fr/PZimmermann/papers/accuracy.pdf
- CORE-MATH project page [read]: https://core-math.gitlabpages.inria.fr/
- Zimmermann, "CORE-MATH: progress report", 2023 [read: the slides]: https://members.loria.fr/PZimmermann/talks/core-math-fpbench2023.pdf
- Faissole, Geneau de Lamarlière, Melquiond, "End-To-End Formal Verification of a Fast and Accurate Floating-Point Approximation", ITP 2024 [abstract]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.14
- Harrison, "Floating point verification in HOL Light: the exponential function", UCAM-CL-TR-428, 1997 [abstract]: https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-428.html
- Darulova, Volkova, "Sound Approximation of Programs with Elementary Functions", CAV 2019 [read]: https://arxiv.org/abs/1811.10274
- Lim, Nagarakatte, RLIBM-32 and RLIBM-ALL [abstracts]: https://arxiv.org/abs/2104.04043, https://arxiv.org/abs/2108.06756
- Monniaux, Boulmé, "The Trusted Computing Base of the CompCert Verified Compiler" [search summary]: https://arxiv.org/abs/2201.10280
- Tom MacWright, "Math keeps changing", 2020 [search summary]: https://macwright.com/2020/02/14/math-keeps-changing
- Glenn Fiedler, "Floating Point Determinism" [search summary]: https://gafferongames.com/post/floating_point_determinism/
- Rapier, "Determinism" [search summary]: https://rapier.rs/docs/user_guides/rust/determinism/
- CosmWasm book, "Floating point types" [search summary]: https://book.cosmwasm.com/basics/fp-types.html

In this repository: `docs/core.md` ("Float"), `DESIGN.md` (§12, the trusted-base table),
`docs/proposals/float.md` (§3.6, §6.2), `docs/proposals/float-laws.md` (§0, §4, §10, §11),
`crates/core/src/float.rs`. The customer's note:
`/Users/matt/repos/mdr/whereabouts/docs/stitchwort-candidates.md`.
