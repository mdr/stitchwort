# The toy formatter's engine in Lean 4 (SW-3513)

The toy formatter (`tools/toyfmt`) was deleted on 22 Nov 2026 (D3715); the
Stitchwort sources this port was measured against are in git history
before that date, and the `measure.py sw` command below no longer runs.

The measured port that
[toy-proof-complexity.md §5](../../docs/proposals/toy-proof-complexity.md)
asks for: the toy's layout engine (`Toy/Doc/Doc.sw`,
`Print.sw`) and the live core of its proof ("`print` is a reading" and
"every reading's words are the document's words") in core Lean 4.35.0,
without Mathlib, twice: once without a simplifier and once with
everything core Lean has. The results and what they mean are in §5.1 of
that note; this file says what is here and how to check it.

| Folder | What |
|---|---|
| `program/Toy/` | `Doc.lean` and `Print.lean`, ported function for function; `Text.lean`, a stand-in for Stitchwort's `Text`; `Tests.lean`, the toy's twelve engine tests as `#guard`s |
| `plain/Toy/Proofs/` | Version (i): terms, `rw`, `omega`, `cases`, `induction`, `obtain` and anonymous constructors, with `show`, `unfold` and `split` to steer. No `simp`, `grind` or `aesop` |
| `idiomatic/Toy/Proofs/` | Version (ii): anything in core Lean (`simp`, `grind`, `fun_induction`) |
| `check.sh` | Checks the program, the tests and the proofs, and prints the axioms of the two top theorems |
| `measure.py` | The counts below, the same way for both languages |

## Checking

    nix shell nixpkgs#lean4 nixpkgs#bc -c ./check.sh            # both versions
    nix shell nixpkgs#lean4 nixpkgs#bc -c ./check.sh plain      # one

It needs no `lake` and writes compiled files to a temporary folder. A
failed `#guard`, a proof that doesn't check or a `sorry` stops it.
Neither version has a `sorry`.

## Measuring

    python3 measure.py sw --roots printIsReading,readingWords \
      ../../tools/toyfmt/src/Toy/Doc/{Readings,Words,Proofs}.sw
    python3 measure.py lean plain/Toy/Proofs/{Readings,Words}.lean
    python3 measure.py lean idiomatic/Toy/Proofs/{Readings,Words}.lean

For Stitchwort it counts only what the two top theorems rest on: all of
`Readings.sw` and `Words.sw` (48 theorems) and 11 of the 42 theorems of
`Proofs.sw`, the step budget that `readingWords` needs.

## Results (16 November 2026, toy at `toy-v1` as tidied by SW-3490)

| | Stitchwort, live core | Lean (i) plain | Lean (ii) idiomatic |
|---|---|---|---|
| Proof-file lines | 886 | 841 (95%) | 469 (53%) |
| Non-blank characters | 32,104 | 25,430 (79%) | 16,985 (53%) |
| Theorems | 59 | 53 | 48 |
| Definitions used only by the proofs | 21 | 21 | 21 |
| Proof lines (after the statement) | 492 | 515 (105%) | 176 (36%) |
| Proof non-blank characters | 17,184 | 12,607 (73%) | 5,134 (30%) |
| Everything but the proofs, characters | 14,920 | 12,823 | 11,851 |
| Median proof, lines | 3 | 4 | 2 |
| Largest proof, lines | 65 (`stepWords`) | 83 (`stepWords`) | 17 (`stepWords`) |
| Check time, proofs only | not measured | 1.3 s | 2.1 s |
| Lane minutes | | about 6 | about 3, with (i) already written |
| Axioms of the top theorems | | `propext`, `Quot.sound` | those and `Classical.choice` |

Percentages are of the Stitchwort column. The program and its tests
check in 1.5 s and took about 4 lane minutes. Line counts follow each
language's layout (Stitchwort's formatter gives each hypothesis its own
line; the Lean files put several on one), so the character rows are the
steadier comparison.

## The top statements, side by side

Stitchwort (`Readings.sw`):

    theorem printIsReading ∀ (doc: Doc) (width: Nat):
        ∃ (final: Printer) => Reads (Printer.start width) (3 * doc.size + 3) [Print 0 Break doc] final
          ∧ print doc width = final.flushSuffixes.out.reverse.joinWith ""

Lean (both versions, `Readings.lean`):

    theorem printIsReading (doc : Doc) (width : Nat) :
        ∃ final : Printer, Reads (Printer.start width) (3 * doc.size + 3) [Print 0 Break doc] final
          ∧ print doc width = Text.join final.flushSuffixes.out.reverse

Stitchwort (`Words.sw`):

    theorem readingWords ∀ (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer)
        (reads: Reads printer fuel stack final)
        (uniform: StackUniform stack)
        (enough: stackCost stack ≤ fuel):
        final.words = printer.words ++ stackWords stack

Lean (both versions, `Words.lean`):

    theorem readingWords (printer : Printer) (fuel : Nat) (stack : List Cmd) (final : Printer)
        (reads : Reads printer fuel stack final)
        (uniform : StackUniform stack)
        (enough : stackCost stack ≤ fuel) :
        final.words = printer.words ++ stackWords stack

The definitions the statements stand on (`IsOption`, `StepsTo`, `Reads`,
`isLayout`, `wordsOf`, `Printer.words`, `Doc.words`, `Uniform`,
`SameWords`, `StackUniform`, `stackWords`, `Doc.steps`, `stackCost`) are
copied clause for clause, and are the same text in both Lean versions.

## Where the port differs from the toy

- **`Text` is a list of characters**, as Stitchwort's is. Lean's `String`
  is a byte array: `isLayout " " = true` is not provable by `decide` or
  `rfl` on it, and core has no lemmas for `String.all`. `Text.lean` (26
  lines) is counted with neither the program nor the proofs.
- **Definitions come bottom-up** in `Print.lean`, since Lean wants each
  before its use; the functions are otherwise the toy's, clause for
  clause. The program files leave out the toy's doc comments.
- **`readingLighter` is proved directly.** The toy proves it for fifteen
  node kinds by quoting `stepLighter`, the same fact about the real
  printer, which brings in `stepLighter`, `ifPairBound`, `chooseSteps`
  and `ifStepsBound` (88 lines). The Lean versions don't need those four.
- **Hindsight.** Both versions were written with the Stitchwort proof
  open, lemma for lemma; version (ii) also had version (i). The lane
  minutes measure transcription, not discovery.
