/-
§2.4 of the paper: prime windows avoiding a prescribed set of primes.

Everything here is *proved* from `rs_window_mass` (the only arithmetic axiom used
in §§4--5).  Lemma 2.3 of the paper is `exists_prime_window_not_dvd`.
-/
import UniversalWords.ClassicalInputs

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

/-- `L r s` is the total log-mass of the primes dividing `rs`. -/
lemma L_eq_sum (r s : ℤ) (h : (r * s) ≠ 0) :
    L r s = ∑ p ∈ (r * s).natAbs.primeFactors, Real.log p := by
  unfold L mrs
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by
    simp only [id_eq, ne_eq, Nat.cast_eq_zero]
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  simp

lemma L_nonneg (r s : ℤ) : 0 ≤ L r s := by
  unfold L
  apply Real.log_nonneg
  have : 1 ≤ mrs r s := by
    unfold mrs
    exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero))
  exact_mod_cast this

/-- **Lemma 2.3.**  A window `(a, b]` whose Chebyshev mass exceeds the mass of the
primes dividing `M` contains a prime not dividing `M`. -/
theorem exists_prime_window_not_dvd (a b : ℝ) (ha : 0 ≤ a) (hb : (11927 : ℝ) < b)
    (hab : a ≤ b) (M : ℕ) (hM : M ≠ 0)
    (hmass : ∑ p ∈ M.primeFactors, Real.log p < 0.985 * b - 1.01624 * a) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p ∣ M) ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  by_contra hcon
  push_neg at hcon
  -- every prime of the window divides `M`
  have hsub : primesIn a b ⊆ M.primeFactors := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_primesIn hp
    have hlt : a < (p : ℝ) := lt_of_mem_primesIn hp
    have hle : (p : ℝ) ≤ b := le_of_mem_primesIn (le_trans ha hab) hp
    have hdvdM : p ∣ M := by
      by_contra hdvd
      exact absurd (hcon p hpp hdvd hlt) (not_lt.mpr hle)
    exact Nat.mem_primeFactors.mpr ⟨hpp, hdvdM, hM⟩
  have hmono : ∑ p ∈ primesIn a b, Real.log p ≤ ∑ p ∈ M.primeFactors, Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have := rs_window_mass a b ha hb hab
  linarith

/-- The form used in §§4--5: a prime in the window not dividing `rs`. -/
theorem exists_prime_window_coprime (r s : ℤ) (hrs : r * s ≠ 0) (a b : ℝ)
    (ha : 0 ≤ a) (hb : (11927 : ℝ) < b) (hab : a ≤ b)
    (hmass : L r s < 0.985 * b - 1.01624 * a) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p ∣ (r * s).natAbs) ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  apply exists_prime_window_not_dvd a b ha hb hab _ (Int.natAbs_ne_zero.mpr hrs)
  rw [← L_eq_sum r s hrs]; exact hmass

/-- A prime not dividing `rs` is coprime to `r` (and, symmetrically, to `s`). -/
lemma coprime_of_not_dvd_mul_left {p : ℕ} {r s : ℤ} (hp : p.Prime)
    (h : ¬ (p ∣ (r * s).natAbs)) : Nat.Coprime p r.natAbs := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  exact h (hdvd.trans (by rw [Int.natAbs_mul]; exact Dvd.intro _ rfl))

lemma coprime_of_not_dvd_mul_right {p : ℕ} {r s : ℤ} (hp : p.Prime)
    (h : ¬ (p ∣ (r * s).natAbs)) : Nat.Coprime p s.natAbs := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  exact h (hdvd.trans (by rw [Int.natAbs_mul]; exact Dvd.intro_left _ rfl))

end UniversalWords
