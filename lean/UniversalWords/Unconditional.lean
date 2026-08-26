/-
The unconditional forms, quarantined.

**This file is the only one in the development that declares axioms.**  Each
axiom below asserts one of the eight named classical statements — every one a
published theorem, with sources documented where the statements are defined in
`ClassicalInputs.lean` and `Analytic.lean`.  Applying the fully-proved
conditional theorems to these axioms recovers the unconditional forms.

Nothing in `Challenge`/`Solution` (the Palomar comparison surface) or in the
conditional development imports this file, so the compared theorems depend only
on Lean's standard axioms; `#print axioms` in `UniversalWords.lean` exhibits
both dependency sets side by side.
-/
import UniversalWords.Main

namespace UniversalWords

/-- Rosser–Schoenfeld window mass (Illinois J. Math. 6 (1962), Thm 9; Math.
Comp. 29 (1975), Corollary to Thm 6), assumed. -/
axiom rs_window_mass : RSWindowMassStatement

/-- Herzog–Kaplan–Lev, Discrete Math. 285 (2004), Theorem 7, assumed. -/
axiom hkl : HKLStatement

/-- Boccara, Discrete Math. 38 (1982), specialised, assumed. -/
axiom boccara_three : BoccaraStatement

/-- Rosser–Schoenfeld π upper bound (1962, eq. (3.6)), assumed. -/
axiom pi_upper : PiUpperStatement

/-- Rosser–Schoenfeld π lower bound (1962, eq. (3.5)), assumed. -/
axiom pi_lower : PiLowerStatement

/-- Montgomery–Vaughan Brun–Titchmarsh (Mathematika 20 (1973), Thm 2), assumed. -/
axiom brun_titchmarsh : BrunTitchmarshStatement

/-- Vinogradov's three-primes count (1937; Vaughan, Thm 3.4), assumed. -/
axiom vinogradov : VinogradovStatement

/-- Halberstam–Richert sieve bound (Sieve Methods, 1974, Thm 3.11), assumed. -/
axiom sieve_r2 : SieveR2Statement

/-- **Main Theorem, unconditional form**: the conditional theorem applied to the
eight assumed classical statements. -/
theorem kourovka_10_32 :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ r s : ℤ, r * s ≠ 0 → (Odd r ∨ Odd s) →
      ∀ n : ℕ, N₀ ≤ n → C * L r s ≤ (n : ℝ) →
        ∀ z : Equiv.Perm (Fin n), ∃ x y : Equiv.Perm (Fin n), x ^ r * y ^ s = z :=
  kourovka_10_32_conditional rs_window_mass hkl boccara_three
    pi_upper pi_lower brun_titchmarsh vinogradov sieve_r2

end UniversalWords
