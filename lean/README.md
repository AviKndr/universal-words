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
| `UniversalWords/Basic.lean` | §2: `md`, `cy`, `δ`; Lemma 2.1; the root lemma 2.2; the factorization core |
| `UniversalWords/ClassicalInputs.lean` | the four **axioms** — see below |
| `UniversalWords/Windows.lean` | §2.4: Lemma 2.3, prime windows avoiding `rs` |
| `UniversalWords/Cases.lean` | §4 (Proposition 4.1) and §6 (Lemma 6.2) |
| `UniversalWords/Dense.lean` | §5 (Proposition 5.1) and its dyadic window argument |
| `UniversalWords/Main.lean` | §3 reductions, §7 assembly, **`kourovka_10_32`** |
| `UniversalWords/LowerBound.lean` | §8 optimality — **no axioms beyond Mathlib** |

## What is proved and what is assumed

`#print axioms` (run by `UniversalWords.lean`) reports:

```
'UniversalWords.kourovka_10_32' depends on axioms:
  [propext, Classical.choice, Quot.sound,          -- Lean's standard three
   UniversalWords.boccara_three,                   -- Boccara 1982
   UniversalWords.exists_good_prime,               -- the paper's own Prop. 6.5
   UniversalWords.hkl,                             -- Herzog–Kaplan–Lev 2004
   UniversalWords.rs_window_mass]                  -- Rosser–Schoenfeld
'UniversalWords.not_universal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Three of the four assumptions are published theorems quoted in the form the paper
uses.  **The fourth, `exists_good_prime`, is the paper's own Proposition 6.5** —
the analytic heart of §6, proved there from Vinogradov's three-primes theorem, an
upper-bound sieve and Brun–Titchmarsh by averaging the singular series.  That
argument is *not* formalized.  So the honest reading is:

> the combinatorial content of the paper — the case division, all three
> constructions, the reductions, the assembly, and the optimality of the
> logarithmic shape — is machine-checked, conditional on Proposition 6.5 and on
> three published theorems.

Everything else is proved: in particular §5's dyadic window argument (which is
what improves the constant to 4.65) depends on Rosser–Schoenfeld alone, and §8's
Proposition 8.1 depends on nothing beyond Mathlib — both halves of it, the
non-universality (`not_universal`) and the cost identity `log m(r,s) = θ(n)`
(`L_eq_theta`).

**What is not formalized.** Corollary 8.2 — the step from Proposition 8.1 to
"the constant cannot be taken to be 1" — needs `θ(n) < n` for infinitely many
`n`, an unconditional but deep oscillation theorem; it is not formalized, so the
*optimality* conclusion is not machine-checked even though the construction
behind it is. And `exists_good_prime` is stated for all nonzero `r, s`, slightly
more generally than the paper's standing assumption (2.1); §6.3 of the paper now
records that Proposition 6.5 and its proof do not use (2.1), which is what
licenses the Lean form.

There are no `sorry`s.

## A note on the local check script

`check.sh` type-checks the modules incrementally against an already-built Mathlib
elsewhere on the machine (set `MATHLIB_PROJECT`).  It is what was used during
development; the `lake build` route above is the portable one, and was not
exercised from a cold cache.
