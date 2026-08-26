/-
§5 of the paper: odd targets of large support, via the dyadic window family.

The arithmetic heart is `exists_dyadic_prime`: if none of the five windows
`(3n/2^{a+2}, n/2^a]`, `1 ≤ a ≤ 5`, contained a prime avoiding `rs`, their
Chebyshev masses --- which are disjoint, and sum to more than `0.2158 n` ---
would all be carried by the primes of `rs`, contradicting `n ≥ 4.65 L`.
-/
import UniversalWords.Cases

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

variable {n : ℕ}

/-- Two windows are disjoint once the upper one starts above the lower one's top. -/
lemma primesIn_disjoint {a₁ b₁ a₂ b₂ : ℝ} (hb₂ : 0 ≤ b₂) (h : b₂ ≤ a₁) :
    Disjoint (primesIn a₁ b₁) (primesIn a₂ b₂) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have h1 : a₁ < (p : ℝ) := lt_of_mem_primesIn hp1
  have h2 : (p : ℝ) ≤ b₂ := le_of_mem_primesIn hb₂ hp2
  linarith

/-- **The dyadic step of Proposition 5.1.**  One of the five windows
`(3n/2^{a+2}, n/2^a]`, `1 ≤ a ≤ 5`, contains a prime not dividing `rs`. -/
theorem exists_dyadic_prime (r s : ℤ) (hrs : r * s ≠ 0) (hn : 381700 ≤ n)
    (hL : (4.65 : ℝ) * L r s ≤ (n : ℝ)) :
    ∃ a q : ℕ, 1 ≤ a ∧ a ≤ 5 ∧ q.Prime ∧ ¬ (q ∣ (r * s).natAbs) ∧
      3 * (n : ℝ) / 2 ^ (a + 2) < (q : ℝ) ∧ (q : ℝ) ≤ (n : ℝ) / 2 ^ a := by
  have hn' : (381700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_contra hcon
  push_neg at hcon
  -- the five windows
  set W₁ := primesIn (3 * (n : ℝ) / 8) ((n : ℝ) / 2) with hW₁
  set W₂ := primesIn (3 * (n : ℝ) / 16) ((n : ℝ) / 4) with hW₂
  set W₃ := primesIn (3 * (n : ℝ) / 32) ((n : ℝ) / 8) with hW₃
  set W₄ := primesIn (3 * (n : ℝ) / 64) ((n : ℝ) / 16) with hW₄
  set W₅ := primesIn (3 * (n : ℝ) / 128) ((n : ℝ) / 32) with hW₅
  -- each window sits inside the primes of `rs`
  have key : ∀ (a : ℕ), 1 ≤ a → a ≤ 5 →
      primesIn (3 * (n : ℝ) / 2 ^ (a + 2)) ((n : ℝ) / 2 ^ a) ⊆ (r * s).natAbs.primeFactors := by
    intro a ha1 ha5 p hp
    have hpp : p.Prime := prime_of_mem_primesIn hp
    have hlow : 3 * (n : ℝ) / 2 ^ (a + 2) < (p : ℝ) := lt_of_mem_primesIn hp
    have hhigh : (p : ℝ) ≤ (n : ℝ) / 2 ^ a :=
      le_of_mem_primesIn (by positivity) hp
    have hdvd : p ∣ (r * s).natAbs := by
      by_contra hnd
      exact absurd hhigh (not_le.mpr (hcon a p ha1 ha5 hpp hnd hlow))
    exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Int.natAbs_ne_zero.mpr hrs⟩
  -- ... specialised to the five concrete windows
  have k₁ : W₁ ⊆ (r * s).natAbs.primeFactors := by
    have := key 1 (by norm_num) (by norm_num); norm_num at this; exact this
  have k₂ : W₂ ⊆ (r * s).natAbs.primeFactors := by
    have := key 2 (by norm_num) (by norm_num); norm_num at this; exact this
  have k₃ : W₃ ⊆ (r * s).natAbs.primeFactors := by
    have := key 3 (by norm_num) (by norm_num); norm_num at this; exact this
  have k₄ : W₄ ⊆ (r * s).natAbs.primeFactors := by
    have := key 4 (by norm_num) (by norm_num); norm_num at this; exact this
  have k₅ : W₅ ⊆ (r * s).natAbs.primeFactors := by
    have := key 5 (by norm_num) (by norm_num); norm_num at this; exact this
  -- the union is still inside the primes of `rs`
  have hsub : W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ W₅ ⊆ (r * s).natAbs.primeFactors := by
    intro p hp
    simp only [Finset.mem_union] at hp
    rcases hp with ((((h | h) | h) | h) | h)
    exacts [k₁ h, k₂ h, k₃ h, k₄ h, k₅ h]
  -- masses add, because the windows are pairwise disjoint
  have d12 : Disjoint W₁ W₂ := primesIn_disjoint (by positivity) (by linarith)
  have d13 : Disjoint W₁ W₃ := primesIn_disjoint (by positivity) (by linarith)
  have d14 : Disjoint W₁ W₄ := primesIn_disjoint (by positivity) (by linarith)
  have d15 : Disjoint W₁ W₅ := primesIn_disjoint (by positivity) (by linarith)
  have d23 : Disjoint W₂ W₃ := primesIn_disjoint (by positivity) (by linarith)
  have d24 : Disjoint W₂ W₄ := primesIn_disjoint (by positivity) (by linarith)
  have d25 : Disjoint W₂ W₅ := primesIn_disjoint (by positivity) (by linarith)
  have d34 : Disjoint W₃ W₄ := primesIn_disjoint (by positivity) (by linarith)
  have d35 : Disjoint W₃ W₅ := primesIn_disjoint (by positivity) (by linarith)
  have d45 : Disjoint W₄ W₅ := primesIn_disjoint (by positivity) (by linarith)
  have hsum_eq :
      ∑ p ∈ (W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ W₅), Real.log p =
        (∑ p ∈ W₁, Real.log p) + (∑ p ∈ W₂, Real.log p) + (∑ p ∈ W₃, Real.log p)
          + (∑ p ∈ W₄, Real.log p) + (∑ p ∈ W₅, Real.log p) := by
    rw [Finset.sum_union (by
          simp only [Finset.disjoint_union_left]
          exact ⟨⟨⟨d15, d25⟩, d35⟩, d45⟩),
        Finset.sum_union (by
          simp only [Finset.disjoint_union_left]
          exact ⟨⟨d14, d24⟩, d34⟩),
        Finset.sum_union (by
          simp only [Finset.disjoint_union_left]
          exact ⟨d13, d23⟩),
        Finset.sum_union d12]
  -- lower bounds for the five masses, from Rosser--Schoenfeld
  have m₁ := rs_window_mass (3 * (n : ℝ) / 8) ((n : ℝ) / 2) (by positivity) (by linarith)
    (by linarith)
  have m₂ := rs_window_mass (3 * (n : ℝ) / 16) ((n : ℝ) / 4) (by positivity) (by linarith)
    (by linarith)
  have m₃ := rs_window_mass (3 * (n : ℝ) / 32) ((n : ℝ) / 8) (by positivity) (by linarith)
    (by linarith)
  have m₄ := rs_window_mass (3 * (n : ℝ) / 64) ((n : ℝ) / 16) (by positivity) (by linarith)
    (by linarith)
  have m₅ := rs_window_mass (3 * (n : ℝ) / 128) ((n : ℝ) / 32) (by positivity) (by linarith)
    (by linarith)
  rw [← hW₁] at m₁; rw [← hW₂] at m₂; rw [← hW₃] at m₃; rw [← hW₄] at m₄; rw [← hW₅] at m₅
  -- the union's mass is at most `L`
  have hmono : ∑ p ∈ (W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ W₅), Real.log p ≤ L r s := by
    rw [L_eq_sum r s hrs]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  rw [hsum_eq] at hmono
  -- `0.2158 n ≤ L ≤ n / 4.65 = 0.21505… n`, a contradiction
  linarith

/-- Truncated subtraction from a real bound. -/
lemma nat_sub_le_of_real {a b c : ℕ} (h : (a : ℝ) - (b : ℝ) ≤ (c : ℝ)) : a - b ≤ c := by
  rcases le_total a b with hab | hab
  · simp [Nat.sub_eq_zero_of_le hab]
  · have h2 : (a : ℝ) ≤ (b : ℝ) + (c : ℝ) := by linarith
    have h3 : a ≤ b + c := by exact_mod_cast h2
    omega

/-- Conjugation preserves order. -/
lemma orderOf_conj' {G : Type*} [Group G] (g a : G) :
    orderOf (g⁻¹ * a * g) = orderOf a := by
  have key : ∀ k : ℕ, (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
    intro k
    induction k with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, pow_succ]; group
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [key, pow_orderOf_eq_one]; group
  · apply orderOf_dvd_of_pow_eq_one
    have h1 : (g⁻¹ * a * g) ^ orderOf (g⁻¹ * a * g) = 1 := pow_orderOf_eq_one _
    rw [key] at h1
    calc a ^ orderOf (g⁻¹ * a * g)
        = g * (g⁻¹ * a ^ orderOf (g⁻¹ * a * g) * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h1]
      _ = 1 := by group

/-- The paper's remark after Theorem 2.5: the two cycle lengths may be realised in
either order, since `z = A·B` gives `z = B·(B⁻¹AB)` with `B⁻¹AB` conjugate to `A`. -/
theorem word_of_factorization_swap {G : Type*} [Group G] {z A B : G} (hz : z = A * B)
    {r s : ℤ} (hB : Nat.Coprime (orderOf B) r.natAbs)
    (hA : Nat.Coprime (orderOf A) s.natAbs) :
    ∃ x y : G, x ^ r * y ^ s = z := by
  refine word_of_factorization (A := B) (B := B⁻¹ * A * B) ?_ hB ?_
  · rw [hz]; group
  · rwa [orderOf_conj']

/-- **Proposition 5.1.**  Odd targets moving at least `n/2` points. -/
theorem dense_case (r s : ℤ) (hrs : r * s ≠ 0) (hsodd : ¬ (2 ∣ s.natAbs))
    (hn : 381700 ≤ n) (hL : (4.65 : ℝ) * L r s ≤ (n : ℝ))
    (z : Perm (Fin n)) (hodd : Odd (delta z)) (hdense : n ≤ 2 * md z) :
    ∃ x y : Perm (Fin n), x ^ r * y ^ s = z := by
  have hn' : (381700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLnn := L_nonneg r s
  have hz : z ≠ 1 := by
    intro h; rw [h] at hodd; simp [delta, md, cy] at hodd
  -- the odd factor `u`
  obtain ⟨u, hu, hudvd, hulow, huhigh⟩ :=
    exists_prime_window_coprime r s hrs (3 * (n : ℝ) / 4) (n : ℝ)
      (by positivity) (by linarith) (by linarith) (by linarith)
  -- the even factor `v = 2^a q`
  obtain ⟨a, q, ha1, ha5, hq, hqdvd, hqlow, hqhigh⟩ := exists_dyadic_prime r s hrs hn hL
  set v : ℕ := 2 ^ a * q with hv
  have hpow : (0 : ℝ) < 2 ^ a := by positivity
  have hveq : (v : ℝ) = 2 ^ a * (q : ℝ) := by rw [hv]; push_cast; ring
  have hvlow : 3 * (n : ℝ) / 4 < (v : ℝ) := by
    have h2 : (2 : ℝ) ^ a * (3 * (n : ℝ) / 2 ^ (a + 2)) = 3 * (n : ℝ) / 4 := by
      rw [pow_add]; field_simp; ring
    rw [hveq, ← h2]
    exact mul_lt_mul_of_pos_left hqlow hpow
  have hvhigh : (v : ℝ) ≤ (n : ℝ) := by
    have h2 : (2 : ℝ) ^ a * ((n : ℝ) / 2 ^ a) = (n : ℝ) := by field_simp
    rw [hveq, ← h2]
    exact mul_le_mul_of_nonneg_left hqhigh (le_of_lt hpow)
  have hun : u ≤ n := by exact_mod_cast huhigh
  have hvn : v ≤ n := by exact_mod_cast hvhigh
  have h4u : 3 * n < 4 * u := by exact_mod_cast (by linarith : (3 : ℝ) * n < 4 * u)
  have h4v : 3 * n < 4 * v := by exact_mod_cast (by linarith : (3 : ℝ) * n < 4 * v)
  -- `|u - v| < n/4 ≤ δ`
  have hdelta4 : n ≤ 4 * delta z := by have := md_le_two_mul_delta z; omega
  have hdeltaR : (n : ℝ) / 4 ≤ (delta z : ℝ) := by
    have : (n : ℝ) ≤ 4 * (delta z : ℝ) := by exact_mod_cast hdelta4
    linarith
  have hduv : u - v ≤ delta z :=
    nat_sub_le_of_real (by linarith)
  have hdvu : v - u ≤ delta z :=
    nat_sub_le_of_real (by linarith)
  -- parity: `u` odd, `v` even, `md + cy ≡ δ` odd
  have hu2 : u ≠ 2 := by
    intro h; rw [h] at huhigh hulow; norm_num at hulow; linarith
  have huodd : u % 2 = 1 := Nat.odd_iff.mp (hu.odd_of_ne_two hu2)
  have hveven : v % 2 = 0 := by
    have : 2 ∣ v := by
      rw [hv]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) q
    omega
  have hdodd : delta z % 2 = 1 := Nat.odd_iff.mp hodd
  have hpar := md_add_cy_mod_two z
  have hmdn : md z ≤ n := md_le_card z
  have hcy := two_mul_cy_le_md z
  have hsum : md z + cy z ≤ u + v := by omega
  -- coprimality of the two lengths, and `2 ≤ v`
  have hq1 : 0 < q := hq.pos
  have hpow2 : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  have hv2 : 2 ≤ v := by
    rw [hv]; exact le_trans hpow2 (Nat.le_mul_of_pos_right _ hq1)
  have hucop : Nat.Coprime u r.natAbs := coprime_of_not_dvd_mul_left hu hudvd
  have hvcop : Nat.Coprime v s.natAbs := by
    rw [hv]
    refine Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).mpr hsodd))
      ((hq.coprime_iff_not_dvd).mpr (fun hd => hqdvd ?_))
    exact hd.trans (by rw [Int.natAbs_mul]; exact Dvd.intro_left _ rfl)
  -- HKL, with the larger length first; the swap covers the other order
  rcases le_total v u with hle | hle
  · obtain ⟨A, B, hAc, hAmd, hBc, hBmd, hzAB⟩ :=
      hkl z hz u v hle hv2 hun hsum (by omega) (by omega)
    refine word_of_factorization hzAB ?_ ?_
    · rw [hAc.orderOf, ← md, hAmd]; exact hucop
    · rw [hBc.orderOf, ← md, hBmd]; exact hvcop
  · obtain ⟨A, B, hAc, hAmd, hBc, hBmd, hzAB⟩ :=
      hkl z hz v u hle hu.two_le hvn (by omega) (by omega) (by omega)
    refine word_of_factorization_swap hzAB ?_ ?_
    · rw [hBc.orderOf, ← md, hBmd]; exact hucop
    · rw [hAc.orderOf, ← md, hAmd]; exact hvcop

end UniversalWords
