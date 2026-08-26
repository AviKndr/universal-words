/-
§8 of the paper: optimality of the logarithmic shape.

With `r = lcm(1,…,n)` and `s` its odd part, `x^r = 1` identically and every value
`y^s` has order a power of two.  An element of order 3 is therefore never a value,
so `x^r y^s` is not universal on `S_n` --- while `log m(r,s) = θ(n)`, which is what
makes the constant `1` unattainable.

This file is fully proved: it uses no axioms beyond Mathlib's.  (Corollary 8.2 of
the paper additionally invokes `θ(n) < n` infinitely often, an unconditional but
deep oscillation theorem, which is not formalised here.)
-/
import UniversalWords.Basic

namespace UniversalWords

open Equiv Equiv.Perm

/-- `R n = lcm(1, …, n)`, the paper's `r`. -/
def R (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

lemma R_pos (n : ℕ) : 0 < R n := by
  rw [R, Nat.pos_iff_ne_zero]
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc, id_eq] at h
  obtain ⟨a, ⟨ha1, _⟩, ha0⟩ := h
  omega

/-- Every cycle length in `S_n` lies in `[1,n]`, so the order divides `lcm(1,…,n)`. -/
lemma orderOf_dvd_R {n : ℕ} (x : Perm (Fin n)) : orderOf x ∣ R n := by
  rw [← lcm_cycleType]
  refine Multiset.lcm_dvd.mpr ?_
  intro l hl
  have h2 : 2 ≤ l := two_le_of_mem_cycleType hl
  have hle : l ≤ n := by
    have h3 := le_card_support_of_mem_cycleType hl
    have hcard : x.support.card ≤ n := by
      have := Finset.card_le_univ x.support
      simpa [Fintype.card_fin] using this
    omega
  exact Finset.dvd_lcm (by simp only [Finset.mem_Icc]; omega)

/-- `x ^ lcm(1,…,n) = 1` for every `x ∈ S_n`: the first factor dies identically. -/
lemma pow_R_eq_one {n : ℕ} (x : Perm (Fin n)) : x ^ (R n) = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_R x)

/-! ### The cost of the word: `log m(r,s) = θ(n)` -/

/-- `lcm(1,…,n)` divides `n!`. -/
lemma R_dvd_factorial (n : ℕ) : R n ∣ Nat.factorial n := by
  rw [R]
  refine Finset.lcm_dvd ?_
  intro a ha
  simp only [Finset.mem_Icc] at ha
  simp only [id_eq]
  exact Nat.dvd_factorial ha.1 ha.2

/-- A prime dividing `lcm(1,…,n)` is at most `n`. -/
lemma prime_le_of_dvd_R {n p : ℕ} (hp : p.Prime) (h : p ∣ R n) : p ≤ n :=
  (Nat.Prime.dvd_factorial hp).mp (h.trans (R_dvd_factorial n))

/-- The primes dividing `lcm(1,…,n)` are exactly the primes `≤ n`. -/
lemma primeFactors_R (n : ℕ) :
    (R n).primeFactors = (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    exact ⟨by have := prime_le_of_dvd_R hp hdvd; omega, hp⟩
  · rintro ⟨hlt, hp⟩
    refine ⟨hp, ?_, (R_pos n).ne'⟩
    exact Finset.dvd_lcm (by simp only [Finset.mem_Icc]; exact ⟨hp.pos, by omega⟩)

/-- **The other half of Proposition 8.1**: the exponents cost only `θ(n)`.  This is
what makes the construction bite --- the word fails at degree `n` while
`log m(r,s)` is only `θ(n)`, which is `< n` for infinitely many `n`. -/
theorem L_eq_theta (n s : ℕ) (hs : s ∣ R n) (hs0 : 0 < s) :
    L (R n : ℤ) (s : ℤ) = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p := by
  have hRne : R n ≠ 0 := (R_pos n).ne'
  have hprod : ((R n : ℤ) * (s : ℤ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Int.natCast_eq_zero]
    push_neg
    exact ⟨hRne, hs0.ne'⟩
  rw [L_eq_sum _ _ hprod]
  congr 1
  have hnat : ((R n : ℤ) * (s : ℤ)).natAbs = R n * s := by
    simp [Int.natAbs_mul]
  rw [hnat, Nat.primeFactors_mul hRne hs0.ne']
  rw [Finset.union_eq_left.mpr (Nat.primeFactors_mono hs hRne)]
  exact primeFactors_R n

/-- **Proposition 8.1 and its corollary.**  Taking `r = lcm(1,…,n)` and `s` its odd
part, every value of `x^r y^s` has order a power of two; in particular no element
of order 3 is a value, so the word is not universal on `S_n`. -/
theorem not_universal (n : ℕ) (z : Perm (Fin n)) (hz : orderOf z = 3) :
    ∃ s : ℕ, 0 < s ∧ ¬ (2 ∣ s) ∧ s ∣ R n ∧
      L (R n : ℤ) (s : ℤ) = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ∧
      ∀ x y : Perm (Fin n), x ^ (R n : ℤ) * y ^ (s : ℤ) ≠ z := by
  obtain ⟨a, b, hbodd, hRab⟩ := Nat.exists_eq_two_pow_mul_odd (R_pos n).ne'
  have hb1 : b % 2 = 1 := Nat.odd_iff.mp hbodd
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb1; omega
    · exact h
  have hbdvd : b ∣ R n := ⟨2 ^ a, by rw [hRab]; ring⟩
  refine ⟨b, hbpos, by omega, hbdvd, L_eq_theta n b hbdvd hbpos, ?_⟩
  intro x y hxy
  -- the `x`-side is trivial, so the value is `y^b`
  have h1 : x ^ (R n : ℤ) = 1 := by rw [zpow_natCast]; exact pow_R_eq_one x
  rw [h1, one_mul] at hxy
  -- and `(y^b)^(2^a) = y^(lcm(1,…,n)) = 1`
  have h2 : (y ^ (b : ℤ)) ^ (2 ^ a) = 1 := by
    rw [← zpow_natCast (y ^ (b : ℤ)) (2 ^ a), ← zpow_mul]
    have hmul : (b : ℤ) * ((2 ^ a : ℕ) : ℤ) = ((R n : ℕ) : ℤ) := by
      rw [hRab]; push_cast; ring
    rw [hmul, zpow_natCast]
    exact pow_R_eq_one y
  rw [hxy] at h2
  -- so `3 = orderOf z` divides `2^a`, which is absurd
  have h3 : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h2
  rw [hz] at h3
  have h4 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
  omega

end UniversalWords
