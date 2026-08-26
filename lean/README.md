# Lean formalization

Formalizes the paper `../universal-words.tex`.  Checked with Lean 4 (toolchain in
`lean-toolchain`) against Mathlib revision `ae26804842dd`.

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (do this first)
lake build
```

The committed `lake-manifest.json` pins Mathlib and its transitive dependencies
to exact commits. The development uses targeted Mathlib imports rather than
`import Mathlib` (`Basic.lean` carries the shared header), which makes a
warm-cache check of the whole chain take ~25 s rather than ~2 min.

| File | Paper |
| --- | --- |
| `UniversalWords/Basic.lean` | §2: `md`, `cy`, `δ`; Lemma 2.1; the root lemma 2.2; the factorization core; `m(r,s)` and `L` |
| `UniversalWords/ClassicalInputs.lean` | **statements** (as named `Prop`s, nothing assumed): Herzog–Kaplan–Lev, Boccara, Rosser–Schoenfeld window mass |
| `UniversalWords/Analytic.lean` | **statements**: RS π-bounds, Brun–Titchmarsh, Vinogradov, the Halberstam–Richert sieve; `r₂`, `r₃`, the singular series |
| `UniversalWords/CountingLemmas.lean` | proved: `r₂`/`r₃` combinatorics, bad-triple fibering, Markov |
| `UniversalWords/SeriesBounds.lean` | proved: telescoping replacements for every Euler-product numeric |
| `UniversalWords/Averaging.lean` | proved: **Lemma 6.4** from the Brun–Titchmarsh statement alone |
| `UniversalWords/GoodPrime.lean` | proved: **Proposition 6.5** from the five analytic statements |
| `UniversalWords/Windows.lean` | §2.4: Lemma 2.3, prime windows avoiding `rs` |
| `UniversalWords/Cases.lean` | §4 (Proposition 4.1) and §6 (Lemma 6.2) |
| `UniversalWords/Dense.lean` | §5 (Proposition 5.1) and its dyadic window argument |
| `UniversalWords/Main.lean` | §3 reductions, §7 assembly, **`kourovka_10_32_conditional`** |
| `UniversalWords/Unconditional.lean` | the **only** file with axioms: assumes the eight statements, derives `kourovka_10_32` |
| `UniversalWords/LowerBound.lean` | §8: Proposition 8.1, both halves — no axioms beyond Mathlib |

## What is proved and what is assumed

The development is **parameterized by its classical inputs**. The eight
published theorems it relies on are stated as named propositions
(`RSWindowMassStatement`, `HKLStatement`, `BoccaraStatement`,
`PiUpperStatement`, `PiLowerStatement`, `BrunTitchmarshStatement`,
`VinogradovStatement`, `SieveR2Statement`), each documented with its source,
and the principal theorem is the fully-proved implication

```
kourovka_10_32_conditional :
  RSWindowMassStatement → HKLStatement → BoccaraStatement →
  PiUpperStatement → PiLowerStatement → BrunTitchmarshStatement →
  VinogradovStatement → SieveR2Statement →
  ∃ C N₀, ∀ r s, … (the Main Theorem)
```

`#print axioms` (run by `UniversalWords.lean`) certifies:

```
kourovka_10_32_conditional : [propext, Classical.choice, Quot.sound]
exists_good_prime          : [propext, Classical.choice, Quot.sound]
averaging                  : [propext, Classical.choice, Quot.sound]
not_universal, L_eq_theta  : [propext, Classical.choice, Quot.sound]
```

— that is, the conditional main theorem, the paper's entire analysis
(Lemma 6.4 and Proposition 6.5), and §8 are all proved **using only Lean's
three standard axioms**.

`Unconditional.lean` — imported by nothing else — assumes the eight statements
as axioms and derives the unconditional `kourovka_10_32`, whose `#print axioms`
lists exactly those eight. Every one is a published theorem; the sources are
documented beside the statement definitions.

The one deliberately unformalized step remains Corollary 8.2's use of
`θ(n) < n` infinitely often, so the paper's *optimality* conclusion — though
its construction (Proposition 8.1) is fully verified — is not machine-checked.

There are no `sorry`s.

## The comparison surface (Challenge / Solution)

For mechanical comparison (following the
[leanprover/comparator](https://github.com/leanprover/comparator) conventions),
the two principal theorems are restated in a small self-contained audit file:

- `Challenge.lean` — imports Mathlib only; defines the notions used
  (`md`, `cy`, `delta`, `m(r,s)`, `L`, prime windows, `r₂`, `r₃`, the singular
  series), states the eight classical inputs verbatim, and states the two
  compared theorems with deliberate holes:
  `Kourovka1032.kourovka_10_32_conditional` and `Kourovka1032.not_universal`.
- `Solution.lean` — redeclares the same environment and proves both theorems
  by instantiating this development; both proofs depend only on
  `[propext, Classical.choice, Quot.sound]`.
- `comparator.json` — names the two modules, the two compared theorems, and
  the permitted (standard) axioms.
- `formalization.yaml` — structured metadata: provenance, sources,
  classification, automation disclosure, fidelity notes, and the
  paper-to-Lean alignment table.

## A note on the local check script

`check.sh` type-checks the modules incrementally against an already-built Mathlib
elsewhere on the machine (set `MATHLIB_PROJECT`).  It is what was used during
development; the `lake build` route above is the portable one, and was not
exercised from a cold cache.
