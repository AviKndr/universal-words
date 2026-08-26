# Lean formalization

Formalizes the paper `../universal-words.tex`.  Checked with Lean 4 (toolchain in
`lean-toolchain`) against Mathlib revision `ae26804842dd`.

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (do this first)
lake build
```

The development uses targeted Mathlib imports rather than `import Mathlib`
(`Basic.lean` carries the shared header), which makes a warm-cache check of the
whole chain take ~25 s rather than ~2 min.

| File | Paper |
| --- | --- |
| `UniversalWords/Basic.lean` | §2: `md`, `cy`, `δ`; Lemma 2.1; the root lemma 2.2; the factorization core; `m(r,s)` and `L` |
| `UniversalWords/ClassicalInputs.lean` | **axioms**: Herzog–Kaplan–Lev, Boccara, Rosser–Schoenfeld (θ-window form) |
| `UniversalWords/Analytic.lean` | **axioms**: RS π-bounds, Brun–Titchmarsh, Vinogradov, the Halberstam–Richert sieve |
| `UniversalWords/CountingLemmas.lean` | proved: `r₂`/`r₃` combinatorics, bad-triple fibering, Markov |
| `UniversalWords/SeriesBounds.lean` | proved: telescoping replacements for every Euler-product numeric |
| `UniversalWords/Averaging.lean` | proved: **Lemma 6.4** (the singular-series average) from Brun–Titchmarsh alone |
| `UniversalWords/GoodPrime.lean` | proved: **Proposition 6.5** from the analytic axioms |
| `UniversalWords/Windows.lean` | §2.4: Lemma 2.3, prime windows avoiding `rs` |
| `UniversalWords/Cases.lean` | §4 (Proposition 4.1) and §6 (Lemma 6.2) |
| `UniversalWords/Dense.lean` | §5 (Proposition 5.1) and its dyadic window argument |
| `UniversalWords/Main.lean` | §3 reductions, §7 assembly, **`kourovka_10_32`** |
| `UniversalWords/LowerBound.lean` | §8: Proposition 8.1, both halves — **no axioms beyond Mathlib** |

## What is proved and what is assumed

`#print axioms` (run by `UniversalWords.lean`) reports:

```
'UniversalWords.kourovka_10_32' depends on axioms:
  [propext, Classical.choice, Quot.sound,          -- Lean's standard three
   UniversalWords.boccara_three,                   -- Boccara 1982
   UniversalWords.brun_titchmarsh,                 -- Montgomery–Vaughan 1973
   UniversalWords.hkl,                             -- Herzog–Kaplan–Lev 2004
   UniversalWords.pi_lower, UniversalWords.pi_upper,  -- Rosser–Schoenfeld 1962
   UniversalWords.rs_window_mass,                  -- Rosser–Schoenfeld 1962/1975
   UniversalWords.sieve_r2,                        -- Halberstam–Richert 1974
   UniversalWords.vinogradov]                      -- Vinogradov 1937
'UniversalWords.exists_good_prime' (= the paper's Proposition 6.5) depends on:
  [standard three, brun_titchmarsh, pi_lower, pi_upper, sieve_r2, vinogradov]
'UniversalWords.averaging' (= the paper's Lemma 6.4) depends on:
  [standard three, brun_titchmarsh]
'UniversalWords.not_universal', 'UniversalWords.L_eq_theta' (§8):
  [standard three only]
```

**Every axiom is a published theorem**, quoted in the form the paper uses and
documented with its source in `ClassicalInputs.lean` / `Analytic.lean`.  In
particular the paper's own analysis — Lemma 6.4's singular-series averaging and
Proposition 6.5's assembly, previously assumed — is now machine-checked: the
Euler-product numerics are replaced by exact telescoping sums, the non-reduced
Brun–Titchmarsh classes are shown to be empty (window primes exceed `√n`), and
the numeric budget closes with the constants chosen inside the proof from the
axioms' existential constants.

So the honest reading is now:

> the entire argument of the paper — combinatorial and analytic — is
> machine-checked, conditional only on eight published theorems of the
> literature.

There are no `sorry`s.

## A note on the local check script

`check.sh` type-checks the modules incrementally against an already-built Mathlib
elsewhere on the machine (set `MATHLIB_PROJECT`).  It is what was used during
development; the `lake build` route above is the portable one, and was not
exercised from a cold cache.
