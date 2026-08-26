/-
Elementary counting toolbox for the proof of Proposition 6.5.

Everything here is proved; no axioms are declared.
-/
import UniversalWords.Analytic

namespace UniversalWords

open scoped Classical

/-! ## Trivial facts about `r₂` -/

lemma mem_pairs {k : ℕ} {pq : ℕ × ℕ} :
    pq ∈ pairs k ↔ pq.1 ≤ k ∧ pq.2 ≤ k ∧ pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = k := by
  unfold pairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
  tauto

lemma mem_triples {M : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ triples M ↔ t.1 ≤ M ∧ t.2.1 ≤ M ∧ t.2.2 ≤ M ∧
      t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = M := by
  unfold triples
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
  tauto

/-- An odd number has at most two representations as a sum of two primes
(one summand must be the even prime `2`). -/
lemma r₂_le_two_of_odd {k : ℕ} (hk : Odd k) : r₂ k ≤ 2 := by
  have hsub : pairs k ⊆ {(2, k - 2), (k - 2, 2)} := by
    intro pq hpq
    obtain ⟨h1, h2, hp, hq, hsum⟩ := mem_pairs.mp hpq
    have hkm : k % 2 = 1 := Nat.odd_iff.mp hk
    have h2or : pq.1 = 2 ∨ pq.2 = 2 := by
      by_contra hcon
      push_neg at hcon
      have hpo : pq.1 % 2 = 1 :=
        Nat.odd_iff.mp (hp.odd_of_ne_two hcon.1)
      have hqo : pq.2 % 2 = 1 :=
        Nat.odd_iff.mp (hq.odd_of_ne_two hcon.2)
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    have h22 := hp.two_le
    have h22' := hq.two_le
    rcases h2or with h | h
    · left; constructor <;> omega
    · right; constructor <;> omega
  calc r₂ k = (pairs k).card := rfl
    _ ≤ ({(2, k - 2), (k - 2, 2)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

/-- No representations below `4 = 2 + 2`. -/
lemma r₂_eq_zero_of_lt {k : ℕ} (hk : k < 4) : r₂ k = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc r₂ k = (pairs k).card := rfl
    _ ≤ (∅ : Finset (ℕ × ℕ)).card := by
        apply Finset.card_le_card
        intro pq hpq
        obtain ⟨-, -, hp, hq, hsum⟩ := mem_pairs.mp hpq
        exact absurd hsum (by have := hp.two_le; have := hq.two_le; omega)
    _ = 0 := rfl

/-! ## Fibering bad triples over the excluded coordinate -/

lemma card_triples_fst_le (M p : ℕ) (hp : p ≤ M) :
    ((triples M).filter (fun t => t.1 = p)).card ≤ r₂ (M - p) := by
  unfold r₂
  refine Finset.card_le_card_of_injOn (fun t => (t.2.1, t.2.2)) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨h1, h2, h3, hp1, hp2, hp3, hsum⟩ := mem_triples.mp ht.1
    have hteq : t.1 = p := ht.2
    exact mem_pairs.mpr ⟨show t.2.1 ≤ M - p by omega, show t.2.2 ≤ M - p by omega,
      hp2, hp3, show t.2.1 + t.2.2 = M - p by omega⟩
  · intro t ht t' ht' heq
    simp only [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨a, b, c⟩ := t; obtain ⟨a', b', c'⟩ := t'
    have e : a = p := ht.2
    have e' : a' = p := ht'.2
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨by rw [e, e'], heq.1, heq.2⟩

lemma card_triples_snd_le (M p : ℕ) (hp : p ≤ M) :
    ((triples M).filter (fun t => t.2.1 = p)).card ≤ r₂ (M - p) := by
  unfold r₂
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.2)) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨h1, h2, h3, hp1, hp2, hp3, hsum⟩ := mem_triples.mp ht.1
    have hteq : t.2.1 = p := ht.2
    exact mem_pairs.mpr ⟨show t.1 ≤ M - p by omega, show t.2.2 ≤ M - p by omega,
      hp1, hp3, show t.1 + t.2.2 = M - p by omega⟩
  · intro t ht t' ht' heq
    simp only [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨a, b, c⟩ := t; obtain ⟨a', b', c'⟩ := t'
    have e : b = p := ht.2
    have e' : b' = p := ht'.2
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨heq.1, by rw [e, e'], heq.2⟩

lemma card_triples_thd_le (M p : ℕ) (hp : p ≤ M) :
    ((triples M).filter (fun t => t.2.2 = p)).card ≤ r₂ (M - p) := by
  unfold r₂
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨h1, h2, h3, hp1, hp2, hp3, hsum⟩ := mem_triples.mp ht.1
    have hteq : t.2.2 = p := ht.2
    exact mem_pairs.mpr ⟨show t.1 ≤ M - p by omega, show t.2.1 ≤ M - p by omega,
      hp1, hp2, show t.1 + t.2.1 = M - p by omega⟩
  · intro t ht t' ht' heq
    simp only [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨a, b, c⟩ := t; obtain ⟨a', b', c'⟩ := t'
    have e : c = p := ht.2
    have e' : c' = p := ht'.2
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨heq.1, heq.2, by rw [e, e']⟩

/-- A coordinate-membership count fibers over the value of the coordinate. -/
lemma card_coord_mem_le (M : ℕ) (E : Finset ℕ) (proj : ℕ × ℕ × ℕ → ℕ)
    (hle : ∀ t ∈ triples M, proj t ≤ M)
    (hfib : ∀ p, p ≤ M → ((triples M).filter (fun t => proj t = p)).card ≤ r₂ (M - p)) :
    ((triples M).filter (fun t => proj t ∈ E)).card ≤
      ∑ p ∈ E.filter (fun p => p ≤ M), r₂ (M - p) := by
  have hmaps : ∀ x ∈ (triples M).filter (fun t => proj t ∈ E),
      proj x ∈ E.filter (fun p => p ≤ M) := by
    intro t ht
    simp only [Finset.mem_filter] at ht
    exact Finset.mem_filter.mpr ⟨ht.2, hle t ht.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro p hp
  simp only [Finset.mem_filter] at hp
  calc (((triples M).filter (fun t => proj t ∈ E)).filter (fun t => proj t = p)).card
      ≤ ((triples M).filter (fun t => proj t = p)).card := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_filter] at ht
        simp only [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1.1, ht.2⟩
    _ ≤ r₂ (M - p) := hfib p hp.2

/-- Triples with some coordinate in the excluded set `E` number at most
`3 Σ_{p ∈ E, p ≤ M} r₂(M - p)`. -/
lemma card_bad_triples_le (M : ℕ) (E : Finset ℕ) :
    ((triples M).filter (fun t => t.1 ∈ E ∨ t.2.1 ∈ E ∨ t.2.2 ∈ E)).card ≤
      3 * ∑ p ∈ E.filter (fun p => p ≤ M), r₂ (M - p) := by
  have h1 : ((triples M).filter (fun t => t.1 ∈ E)).card ≤
      ∑ p ∈ E.filter (fun p => p ≤ M), r₂ (M - p) :=
    card_coord_mem_le M E (fun t => t.1)
      (fun t ht => (mem_triples.mp ht).1)
      (fun p hp => card_triples_fst_le M p hp)
  have h2 : ((triples M).filter (fun t => t.2.1 ∈ E)).card ≤
      ∑ p ∈ E.filter (fun p => p ≤ M), r₂ (M - p) :=
    card_coord_mem_le M E (fun t => t.2.1)
      (fun t ht => (mem_triples.mp ht).2.1)
      (fun p hp => card_triples_snd_le M p hp)
  have h3 : ((triples M).filter (fun t => t.2.2 ∈ E)).card ≤
      ∑ p ∈ E.filter (fun p => p ≤ M), r₂ (M - p) :=
    card_coord_mem_le M E (fun t => t.2.2)
      (fun t ht => (mem_triples.mp ht).2.2.1)
      (fun p hp => card_triples_thd_le M p hp)
  have hsub : (triples M).filter (fun t => t.1 ∈ E ∨ t.2.1 ∈ E ∨ t.2.2 ∈ E) ⊆
      ((triples M).filter (fun t => t.1 ∈ E)) ∪
      ((triples M).filter (fun t => t.2.1 ∈ E)) ∪
      ((triples M).filter (fun t => t.2.2 ∈ E)) := by
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hu1 := Finset.card_union_le
    (((triples M).filter (fun t => t.1 ∈ E)) ∪ ((triples M).filter (fun t => t.2.1 ∈ E)))
    ((triples M).filter (fun t => t.2.2 ∈ E))
  have hu2 := Finset.card_union_le
    ((triples M).filter (fun t => t.1 ∈ E))
    ((triples M).filter (fun t => t.2.1 ∈ E))
  have hcard := Finset.card_le_card hsub
  omega

/-! ## Markov's inequality on a finite set -/

lemma finset_markov {α : Type*} (W : Finset α) (f : α → ℕ) (T : ℝ) :
    ((W.filter (fun a => T ≤ (f a : ℝ))).card : ℝ) * T ≤ ∑ a ∈ W, (f a : ℝ) := by
  calc ((W.filter (fun a => T ≤ (f a : ℝ))).card : ℝ) * T
      = ∑ _a ∈ W.filter (fun a => T ≤ (f a : ℝ)), T := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ W.filter (fun a => T ≤ (f a : ℝ)), (f a : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a ∈ W, (f a : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro a _ _
        positivity

end UniversalWords
