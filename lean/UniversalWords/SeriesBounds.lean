/-
Convergent-series toolbox for the averaging lemma.

The paper's Euler-product numerics (`Π(1+1/((p-2)(p-1))) < 1.75` etc., certified
there by computation) are replaced here by slightly weaker but *provable* bounds:
every product over primes is dominated by `exp` of a sum over integers, and the
two integer sums telescope exactly.  Everything in this file is proved.
-/
import UniversalWords.CountingLemmas
import Mathlib.Analysis.Complex.ExponentialBounds

namespace UniversalWords

open scoped Classical

/-! ## Products against exponentials -/

lemma prod_one_add_le_exp_sum {α : Type*} (P : Finset α) (f : α → ℝ)
    (hf : ∀ p ∈ P, 0 ≤ f p) :
    ∏ p ∈ P, (1 + f p) ≤ Real.exp (∑ p ∈ P, f p) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have := hf p hp
    linarith
  · intro p hp
    have h := Real.add_one_le_exp (f p)
    linarith

lemma sqrt_prod (A : Finset ℕ) :
    Real.sqrt (∏ p ∈ A, (p : ℝ)) = ∏ p ∈ A, Real.sqrt (p : ℝ) := by
  induction A using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.sqrt_mul (by positivity), ih]

/-! ## The two telescoping sums -/

/-- Sums over sets of integers `≥ 3` of `1/((k-2)(k-1))` telescope below `1`. -/
lemma telescope_one (P : Finset ℕ) (hP : ∀ p ∈ P, 3 ≤ p) :
    ∑ p ∈ P, (1 : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1)) ≤ 1 := by
  set f : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hf
  set B := P.sup id + 1 with hB
  have hsub : P ⊆ (Finset.range B).image (fun x : ℕ => x + 3) := by
    intro p hp
    have h3 := hP p hp
    have hle : p ≤ P.sup id := Finset.le_sup (f := id) hp
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨p - 3, by omega, by omega⟩
  have hinj : Set.InjOn (fun x : ℕ => x + 3) ↑(Finset.range B) := by
    intro a _ b _ hab
    simpa using hab
  have step1 : ∑ p ∈ P, (1 : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ (Finset.range B).image (fun x : ℕ => x + 3),
        (1 : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have h3 : 3 ≤ p := by
      simp only [Finset.mem_image, Finset.mem_range] at hp
      obtain ⟨i, -, hi⟩ := hp
      omega
    have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have e1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have e2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have step2 : ∑ p ∈ (Finset.range B).image (fun x : ℕ => x + 3),
      (1 : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1)) =
      ∑ i ∈ Finset.range B, (f i - f (i + 1)) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hf]
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (((i + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    rw [div_sub_div _ _ (by positivity : ((i : ℝ) + 1) ≠ 0)
      (by positivity : ((i : ℝ) + 1 + 1) ≠ 0)]
    have : ((i : ℝ) + 3 - 2) * ((i : ℝ) + 3 - 1) = ((i : ℝ) + 1) * ((i : ℝ) + 1 + 1) := by
      ring
    rw [this]
    congr 1
    ring
  have step3 : ∑ i ∈ Finset.range B, (f i - f (i + 1)) = f 0 - f B :=
    Finset.sum_range_sub' f B
  have hfB : 0 ≤ f B := by simp only [hf]; positivity
  have hf0 : f 0 = 1 := by simp [hf]
  calc ∑ p ∈ P, (1 : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ (Finset.range B).image (fun x : ℕ => x + 3),
          (1 : ℝ) / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := step1
    _ = f 0 - f B := by rw [step2, step3]
    _ ≤ 1 := by rw [hf0]; linarith

/-- Sums over sets of integers `≥ 3` of `1/(√k (k-2))` telescope below `3`. -/
lemma telescope_sqrt (P : Finset ℕ) (hP : ∀ p ∈ P, 3 ≤ p) :
    ∑ p ∈ P, (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2)) ≤ 3 := by
  have hsqrt3 : (5 : ℝ) / 3 ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hsqrt3' : (0 : ℝ) < Real.sqrt 3 := by linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => p = 3)
    (fun p => (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2)))
  rw [← hsplit]
  have h3term : ∑ p ∈ P.filter (fun p => p = 3),
      (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2)) ≤ 3 / 5 := by
    calc ∑ p ∈ P.filter (fun p => p = 3), (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2))
        ≤ ∑ p ∈ ({3} : Finset ℕ), (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter] at hp
            simp [hp.2]
          · intro p hp _
            simp only [Finset.mem_singleton] at hp
            subst hp
            have : (0 : ℝ) < Real.sqrt 3 := hsqrt3'
            have h33 : ((3 : ℕ) : ℝ) = 3 := by norm_num
            rw [h33]
            positivity
      _ = 1 / Real.sqrt 3 := by
          rw [Finset.sum_singleton]
          norm_num
      _ ≤ 3 / 5 := by
          rw [div_le_div_iff₀ hsqrt3' (by norm_num)]
          linarith
  have hrest : ∑ p ∈ P.filter (fun p => ¬ p = 3),
      (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2)) ≤ 12 / 5 := by
    set g : ℕ → ℝ := fun j => 1 / Real.sqrt ((j : ℝ) + 3) with hg
    set Q := P.filter (fun p => ¬ p = 3) with hQ
    have hQ4 : ∀ p ∈ Q, 4 ≤ p := by
      intro p hp
      simp only [hQ, Finset.mem_filter] at hp
      have := hP p hp.1
      omega
    set B := Q.sup id + 1 with hB
    have hsub : Q ⊆ (Finset.range B).image (fun x : ℕ => x + 4) := by
      intro p hp
      have h4 := hQ4 p hp
      have hle : p ≤ Q.sup id := Finset.le_sup (f := id) hp
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨p - 4, by omega, by omega⟩
    have hinj : Set.InjOn (fun x : ℕ => x + 4) ↑(Finset.range B) := by
      intro a _ b _ hab
      simpa using hab
    have hterm : ∀ i : ℕ,
        (1 : ℝ) / (Real.sqrt ((i + 4 : ℕ) : ℝ) * (((i + 4 : ℕ) : ℝ) - 2)) ≤
          4 * (g i - g (i + 1)) := by
      intro i
      simp only [hg]
      have hc4 : (((i + 4 : ℕ) : ℝ)) = (i : ℝ) + 4 := by push_cast; ring
      have hc1 : (((i + 1 : ℕ) : ℝ) + 3) = (i : ℝ) + 4 := by push_cast; ring
      rw [hc4, hc1]
      set s := Real.sqrt ((i : ℝ) + 3) with hs
      set t := Real.sqrt ((i : ℝ) + 4) with ht
      have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have hs2 : s ^ 2 = (i : ℝ) + 3 := Real.sq_sqrt (by positivity)
      have ht2 : t ^ 2 = (i : ℝ) + 4 := Real.sq_sqrt (by positivity)
      have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
      have hsimp : (i : ℝ) + 4 - 2 = (i : ℝ) + 2 := by ring
      rw [hsimp]
      have hdiff : 1 / s - 1 / t = (t - s) / (s * t) := by
        field_simp
      have hform : 4 * ((t - s) / (s * t)) = (4 * (t - s)) / (s * t) := by ring
      rw [hdiff, hform, div_le_div_iff₀ (by positivity) (by positivity)]
      -- goal: `1 * (s * t) ≤ 4 * (t - s) * (t * (i + 2))`
      have hu : (t - s) * (t + s) = 1 := by nlinarith [hs2, ht2]
      have htsp : 0 < t + s := by linarith
      have key : s * (t + s) ≤ 4 * ((i : ℝ) + 2) := by nlinarith [hst, hs2, ht2, hs0, ht0]
      have expand : 4 * (t - s) * (t * ((i : ℝ) + 2)) * (t + s) = 4 * (t * ((i : ℝ) + 2)) := by
        calc 4 * (t - s) * (t * ((i : ℝ) + 2)) * (t + s)
            = 4 * (t * ((i : ℝ) + 2)) * ((t - s) * (t + s)) := by ring
          _ = 4 * (t * ((i : ℝ) + 2)) := by rw [hu]; ring
      have final : 1 * (s * t) * (t + s) ≤ 4 * (t - s) * (t * ((i : ℝ) + 2)) * (t + s) := by
        rw [expand]
        calc 1 * (s * t) * (t + s) = t * (s * (t + s)) := by ring
          _ ≤ t * (4 * ((i : ℝ) + 2)) := mul_le_mul_of_nonneg_left key ht0.le
          _ = 4 * (t * ((i : ℝ) + 2)) := by ring
      exact le_of_mul_le_mul_right final htsp
    calc ∑ p ∈ Q, (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2))
        ≤ ∑ p ∈ (Finset.range B).image (fun x : ℕ => x + 4),
            (1 : ℝ) / (Real.sqrt p * ((p : ℝ) - 2)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hp _
          have h4 : 4 ≤ p := by
            simp only [Finset.mem_image, Finset.mem_range] at hp
            obtain ⟨i, -, hi⟩ := hp
            omega
          have hple : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h4
          have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
          have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          positivity
      _ = ∑ i ∈ Finset.range B,
            (1 : ℝ) / (Real.sqrt ((i + 4 : ℕ) : ℝ) * (((i + 4 : ℕ) : ℝ) - 2)) :=
          Finset.sum_image hinj
      _ ≤ ∑ i ∈ Finset.range B, 4 * (g i - g (i + 1)) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = 4 * (g 0 - g B) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub' g B]
      _ ≤ 4 * g 0 := by
          have hgB : 0 ≤ g B := by
            simp only [hg]
            positivity
          linarith
      _ ≤ 12 / 5 := by
          have hg0 : g 0 = 1 / Real.sqrt 3 := by
            simp only [hg]
            norm_num
          rw [hg0, mul_one_div, div_le_div_iff₀ hsqrt3' (by norm_num)]
          linarith
  linarith

/-! ## Numeric bounds for `exp` -/

lemma exp_one_le : Real.exp 1 ≤ 2.72 := by
  have := Real.exp_one_lt_d9
  linarith

lemma exp_three_le : Real.exp 3 ≤ 20.2 := by
  have h1 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [h3]
  nlinarith

/-! ## Products of distinct primes -/

/-- The totient of a product of distinct primes. -/
lemma totient_prod_primes (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    Nat.totient (∏ p ∈ A, p) = ∏ p ∈ A, (p - 1) := by
  induction A using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hap : a.Prime := hA a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp => hA p (Finset.mem_insert_of_mem hp)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [Nat.totient_mul, Nat.totient_prime hap, ih hs]
      apply Nat.Coprime.prod_right
      intro q hq
      have hqp : q.Prime := hs q hq
      exact (Nat.coprime_primes hap hqp).mpr (fun h => ha (h ▸ hq))

/-- A product of distinct primes taken from the prime factors of `k` divides `k`. -/
lemma prod_subset_primeFactors_dvd (k : ℕ) (A : Finset ℕ) (hA : A ⊆ k.primeFactors) :
    (∏ p ∈ A, p) ∣ k :=
  (Finset.prod_dvd_prod_of_subset _ _ _ hA).trans (Nat.prod_primeFactors_dvd k)

/-- A product of odd primes is odd. -/
lemma prod_odd_of_odd (A : Finset ℕ) (hA : ∀ p ∈ A, p % 2 = 1) :
    (∏ p ∈ A, p) % 2 = 1 := by
  induction A using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1 := hA a (Finset.mem_insert_self a s)
      have h2 := ih (fun p hp => hA p (Finset.mem_insert_of_mem hp))
      rw [Nat.mul_mod, h1, h2]

/-- Products of distinct primes are positive. -/
lemma prod_primes_pos (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    0 < ∏ p ∈ A, p := by
  apply Finset.prod_pos
  intro p hp
  exact (hA p hp).pos

end UniversalWords
