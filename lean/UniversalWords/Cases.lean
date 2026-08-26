/-
§§4 and 6 of the paper: the even case and the small-support case.

`even_case` (Proposition 4.1) is proved from the window lemma and HKL.
`sparse_case` (Lemma 6.2) is proved from Boccara.  The dense case (Proposition
5.1) is in `Dense.lean`.
-/
import UniversalWords.Windows

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

variable {n : ℕ}

lemma md_le_card (z : Perm (Fin n)) : md z ≤ n := by
  have := Finset.card_le_univ z.support
  simpa [md, Fintype.card_fin] using this

/-- The parity bookkeeping shared by §§4--5: `md + cy ≡ δ (mod 2)`. -/
lemma md_add_cy_mod_two (z : Perm (Fin n)) : (md z + cy z) % 2 = delta z % 2 := by
  have h := md_eq_delta_add_cy z
  omega

/-! ## §4: even targets -/

/-- **Proposition 4.1.**  For `z ≠ 1` even, a single prime `q ∈ (3n/4, n]` not
dividing `rs` gives `z` as a product of two `q`-cycles, hence as `x^r y^s`. -/
theorem even_case (r s : ℤ) (hrs : r * s ≠ 0) (hn : 23856 ≤ n)
    (hL : (4.5 : ℝ) * L r s ≤ (n : ℝ))
    (z : Perm (Fin n)) (hz : z ≠ 1) (heven : Equiv.Perm.sign z = 1) :
    ∃ x y : Perm (Fin n), x ^ r * y ^ s = z := by
  have hn' : (23856 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- the prime `q`
  obtain ⟨q, hq, hqdvd, hqlow, hqhigh⟩ :=
    exists_prime_window_coprime r s hrs (3 * (n : ℝ) / 4) (n : ℝ)
      (by positivity) (by linarith) (by linarith)
      (by have := L_nonneg r s; linarith)
  have hq2 : 2 ≤ q := hq.two_le
  have hqn : q ≤ n := by exact_mod_cast hqhigh
  -- `δ z` is even, so `md + cy` is even
  have hdelta_even : delta z % 2 = 0 := by
    have hno : ¬ Odd (delta z) := by
      rw [odd_delta_iff, heven]; decide
    exact Nat.even_iff.mp (Nat.not_odd_iff_even.mp hno)
  -- HKL hypotheses
  have hmdn : md z ≤ n := md_le_card z
  have hsum : md z + cy z ≤ q + q := by
    have h1 : 2 * cy z ≤ md z := two_mul_cy_le_md z
    have h2 : (3 : ℝ) * n < 4 * q := by linarith
    have h3 : 3 * n < 4 * q := by exact_mod_cast h2
    omega
  obtain ⟨A, B, hAc, hAmd, hBc, hBmd, hzAB⟩ :=
    hkl z hz q q (le_refl q) hq2 hqn hsum
      (by have := md_add_cy_mod_two z; omega) (by omega)
  refine word_of_factorization hzAB ?_ ?_
  · rw [hAc.orderOf, ← md, hAmd]
    exact coprime_of_not_dvd_mul_left hq hqdvd
  · rw [hBc.orderOf, ← md, hBmd]
    exact coprime_of_not_dvd_mul_right hq hqdvd

/-! ## §6: odd targets of small support -/

/-- **Lemma 6.2.**  For odd `z` with `δ z ≥ 3` fitting inside an `N`-point set with
`N = 2q̃`, Boccara's criterion gives `z = A·B` with `A` of type `(q₁,q₂,q₃,1)` and
`B` a full `N`-cycle; the coprimality of the orders then yields the word. -/
theorem sparse_case (r s : ℤ) (hsodd : ¬ (2 ∣ s.natAbs))
    (z : Perm (Fin n)) (hodd : Odd (delta z)) (h3 : 3 ≤ delta z)
    (qt q₁ q₂ q₃ : ℕ) (hqt : qt.Prime) (hqts : ¬ (qt ∣ s.natAbs))
    (hNn : 2 * qt ≤ n) (hmdN : md z ≤ 2 * qt)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hq₃ : q₃.Prime)
    (hd₁ : ¬ (q₁ ∣ (r * s).natAbs)) (hd₂ : ¬ (q₂ ∣ (r * s).natAbs))
    (hd₃ : ¬ (q₃ ∣ (r * s).natAbs))
    (hsum : q₁ + q₂ + q₃ + 1 = 2 * qt) :
    ∃ x y : Perm (Fin n), x ^ r * y ^ s = z := by
  obtain ⟨A, B, hAtype, hBc, hBmd, hzAB⟩ :=
    boccara_three z (2 * qt) q₁ q₂ q₃ hmdN hNn hsum hq₁.two_le hq₂.two_le hq₃.two_le h3 hodd
  refine word_of_factorization hzAB ?_ ?_
  · -- `orderOf A = lcm (q₁,q₂,q₃)`, each coprime to `r`
    apply coprime_orderOf_of_cycleType
    intro l hl
    rw [hAtype] at hl
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact coprime_of_not_dvd_mul_left hq₁ hd₁
    · exact coprime_of_not_dvd_mul_left hq₂ hd₂
    · exact coprime_of_not_dvd_mul_left hq₃ hd₃
  · -- `orderOf B = 2q̃`, coprime to the odd `s` since `q̃ ∤ s`
    rw [hBc.orderOf, ← md, hBmd]
    apply Nat.Coprime.mul_left
    · exact (Nat.prime_two.coprime_iff_not_dvd).mpr hsodd
    · exact (hqt.coprime_iff_not_dvd).mpr hqts

end UniversalWords
