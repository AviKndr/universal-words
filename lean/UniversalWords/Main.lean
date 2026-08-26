/-
§§3 and 7 of the paper: the reductions and the assembly of the Main Theorem.
-/
import UniversalWords.Dense

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

/-! ## §3: the reduction swapping the exponents -/

/-- Lemma 3.1(1): `x^r y^s` is universal on `G` iff `x^s y^r` is. -/
lemma swap_exponents {G : Type*} [Group G] {r s : ℤ}
    (h : ∀ z : G, ∃ x y : G, x ^ s * y ^ r = z) :
    ∀ z : G, ∃ x y : G, x ^ r * y ^ s = z := by
  intro z
  obtain ⟨a, b, hab⟩ := h z⁻¹
  refine ⟨b⁻¹, a⁻¹, ?_⟩
  rw [inv_zpow, inv_zpow, ← mul_inv_rev, hab, inv_inv]

/-! ## §7: assembling the three constructions -/

/-- The universality statement for one degree `n`, all targets, with `s` odd. -/
theorem universal_of_odd_right {n : ℕ} (r s : ℤ) (hrs : r * s ≠ 0)
    (hsodd : ¬ (2 ∣ s.natAbs)) (C_star : ℝ) (N_star : ℕ) (hC : (4.65 : ℝ) ≤ C_star)
    (hgood : ∀ (r s : ℤ), r * s ≠ 0 → ∀ n : ℕ, N_star ≤ n → C_star * L r s ≤ (n : ℝ) →
        ∃ qt q₁ q₂ q₃ : ℕ, qt.Prime ∧ ¬ (qt ∣ s.natAbs) ∧
          ((n : ℝ) + 2) / 4 < (qt : ℝ) ∧ (qt : ℝ) ≤ (n : ℝ) / 2 ∧
          q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
          ¬ (q₁ ∣ (r * s).natAbs) ∧ ¬ (q₂ ∣ (r * s).natAbs) ∧ ¬ (q₃ ∣ (r * s).natAbs) ∧
          q₁ + q₂ + q₃ + 1 = 2 * qt)
    (hn : max 381700 N_star ≤ n) (hL : C_star * L r s ≤ (n : ℝ))
    (z : Perm (Fin n)) :
    ∃ x y : Perm (Fin n), x ^ r * y ^ s = z := by
  have hn1 : 381700 ≤ n := le_trans (le_max_left _ _) hn
  have hnstar : N_star ≤ n := le_trans (le_max_right _ _) hn
  have hLnn := L_nonneg r s
  -- the weaker window hypotheses of §§4--5 follow from the one in §6
  have hL465 : (4.65 : ℝ) * L r s ≤ (n : ℝ) := le_trans (by nlinarith) hL
  have hL45 : (4.5 : ℝ) * L r s ≤ (n : ℝ) := le_trans (by nlinarith) hL465
  by_cases hz1 : z = 1
  · exact ⟨1, 1, by simp [hz1]⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign z) with heven | hoddz
  · -- `z` even and non-trivial: Proposition 4.1
    exact even_case r s hrs (by omega) hL45 z hz1 heven
  · -- `z` odd: `δ z` is odd
    have hodd : Odd (delta z) := (odd_delta_iff z).mpr hoddz
    by_cases hdense : n ≤ 2 * md z
    · -- Proposition 5.1
      exact dense_case r s hrs hsodd (by omega) hL465 z hodd hdense
    · push_neg at hdense
      by_cases hd1 : delta z = 1
      · -- a bare transposition: `y := z`, `x := 1`, since `s` is odd
        have hmd2 : md z ≤ 2 := by have := md_le_two_mul_delta z; omega
        refine word_of_factorization (A := 1) (B := z) (by simp) (by simp [Nat.Coprime]) ?_
        apply coprime_orderOf_of_cycleType
        intro l hl
        have h2 : 2 ≤ l := two_le_of_mem_cycleType hl
        have hle : l ≤ md z := by
          rw [md_eq_sum]
          exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hl
        have hl2 : l = 2 := by omega
        rw [hl2]
        exact (Nat.prime_two.coprime_iff_not_dvd).mpr hsodd
      · -- Lemma 6.2, on the `2q̃`-point set supplied by Proposition 6.5
        have hd3 : 3 ≤ delta z := by
          have hodd' : delta z % 2 = 1 := Nat.odd_iff.mp hodd
          omega
        obtain ⟨qt, q₁, q₂, q₃, hqt, hqts, hqtlow, hqthigh, hq₁, hq₂, hq₃,
          hd₁, hd₂, hd₃, hsum⟩ := hgood r s hrs n hnstar hL
        have hNn : 2 * qt ≤ n := by
          have : (2 : ℝ) * qt ≤ (n : ℝ) := by linarith
          exact_mod_cast this
        have hmdN : md z ≤ 2 * qt := by
          have h1 : ((n : ℝ) + 2) / 2 < 2 * (qt : ℝ) := by linarith
          have h2 : (2 : ℝ) * md z < n := by exact_mod_cast hdense
          have : (md z : ℝ) ≤ 2 * qt := by linarith
          exact_mod_cast this
        exact sparse_case r s hsodd z hodd hd3 qt q₁ q₂ q₃ hqt hqts hNn hmdN
          hq₁ hq₂ hq₃ hd₁ hd₂ hd₃ hsum

/-- An odd integer has odd absolute value. -/
lemma not_two_dvd_natAbs_of_odd {a : ℤ} (h : Odd a) : ¬ (2 ∣ a.natAbs) := by
  intro hdvd
  have h2 : (2 : ℤ) ∣ a := by
    have h3 : ((2 : ℤ).natAbs) ∣ a.natAbs := by simpa using hdvd
    exact Int.natAbs_dvd_natAbs.mp h3
  rw [Int.odd_iff] at h
  omega

/-! ## The Main Theorem -/

/-- **Main Theorem** (Kourovka Notebook, Problem 10.32).  There are absolute
constants `C` and `N₀` such that, for all nonzero integers `r, s` at least one of
which is odd, the word `x^r y^s` is universal on `S_n` whenever
`n ≥ max {N₀, C · log m(r,s)}`.

The constants are quantified before `r` and `s`: the bound is uniform in the word,
which is what Problem 10.32 asks for and what distinguishes it from Droste's
theorem. -/
theorem kourovka_10_32 :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ r s : ℤ, r * s ≠ 0 → (Odd r ∨ Odd s) →
      ∀ n : ℕ, N₀ ≤ n → C * L r s ≤ (n : ℝ) →
        ∀ z : Perm (Fin n), ∃ x y : Perm (Fin n), x ^ r * y ^ s = z := by
  obtain ⟨C_star, N_star, hC, hgood⟩ := exists_good_prime
  refine ⟨C_star, max 381700 N_star, ?_⟩
  intro r s hrs hodd n hn hL z
  -- put the odd exponent second
  rcases hodd with hr | hs
  · -- `r` odd: swap the exponents, using `m(s,r) = m(r,s)`
    refine swap_exponents (s := s) (r := r) ?_ z
    have hsr : s * r ≠ 0 := by rwa [mul_comm] at hrs
    have hLsr : L s r = L r s := by unfold L mrs; rw [mul_comm]
    exact universal_of_odd_right s r hsr (not_two_dvd_natAbs_of_odd hr)
      C_star N_star hC hgood hn (by rwa [hLsr])
  · -- `s` odd
    exact universal_of_odd_right r s hrs (not_two_dvd_natAbs_of_odd hs)
      C_star N_star hC hgood hn hL z

end UniversalWords
