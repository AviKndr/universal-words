/-
Lemma 6.4 of the paper: the singular series averaged over the window.

For any shift `b`, `Σ_{q ∈ W} S(2q - b) ≤ 7 n / log n`.  The proof expands each
`S(k)` over subsets of the odd primes up to `n`, swaps the sums, and counts the
window primes in each residue class: by Brun--Titchmarsh when the modulus is at
most `√n` (the non-coprime case is empty, because the window primes exceed `√n`),
and by the trivial injection `q ↦ (2q-b)/d` beyond.  All series constants come
from the telescoping bounds of `SeriesBounds.lean`.  Everything here is proved;
the only axiom reached through this file is `brun_titchmarsh`.
-/
import UniversalWords.SeriesBounds

namespace UniversalWords

open scoped Classical

/-! ## Subsets of odd primes and their weights -/

def oddPrimesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

noncomputable def gA (A : Finset ℕ) : ℝ := ∏ p ∈ A, (1 / ((p : ℝ) - 2))

def dA (A : Finset ℕ) : ℕ := ∏ p ∈ A, p

lemma mem_oddPrimesUpTo {B p : ℕ} :
    p ∈ oddPrimesUpTo B ↔ p ≤ B ∧ p.Prime ∧ p ≠ 2 := by
  unfold oddPrimesUpTo
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

lemma three_le_of_mem_odd {B p : ℕ} (hp : p ∈ oddPrimesUpTo B) : 3 ≤ p := by
  obtain ⟨-, hpp, hp2⟩ := mem_oddPrimesUpTo.mp hp
  have := hpp.two_le
  omega

lemma gA_nonneg {B : ℕ} {A : Finset ℕ} (hA : A ⊆ oddPrimesUpTo B) : 0 ≤ gA A := by
  unfold gA
  apply Finset.prod_nonneg
  intro p hp
  have h3 : 3 ≤ p := three_le_of_mem_odd (hA hp)
  have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

lemma dA_pos {B : ℕ} {A : Finset ℕ} (hA : A ⊆ oddPrimesUpTo B) : 0 < dA A := by
  unfold dA
  exact prod_primes_pos A (fun p hp => (mem_oddPrimesUpTo.mp (hA hp)).2.1)

lemma dA_odd {B : ℕ} {A : Finset ℕ} (hA : A ⊆ oddPrimesUpTo B) : ¬ 2 ∣ dA A := by
  unfold dA
  have h := prod_odd_of_odd A (fun p hp => by
    obtain ⟨-, hpp, hp2⟩ := mem_oddPrimesUpTo.mp (hA hp)
    exact Nat.odd_iff.mp (hpp.odd_of_ne_two hp2))
  omega

/-- `Σ_{A ⊆ P} Π_{p ∈ A} h p = Π_{p ∈ P} (1 + h p)`. -/
lemma sum_powerset_prod (P : Finset ℕ) (h : ℕ → ℝ) :
    ∑ A ∈ P.powerset, ∏ p ∈ A, h p = ∏ p ∈ P, (1 + h p) := by
  have := Finset.prod_add h (fun _ => (1 : ℝ)) P
  simp only [Finset.prod_const_one, mul_one] at this
  rw [← this]
  apply Finset.prod_congr rfl
  intro p _
  ring

/-! ## The pointwise expansion of the singular series -/

lemma singSeries_le_sum (B k : ℕ) (hk1 : 1 ≤ k) (hkB : k ≤ B) :
    SingSeries k ≤
      ∑ A ∈ (oddPrimesUpTo B).powerset, (if dA A ∣ k then gA A else 0) := by
  set F := k.primeFactors.filter (fun p => p ≠ 2) with hF
  have hF3 : ∀ p ∈ F, 3 ≤ p := by
    intro p hp
    simp only [hF, Finset.mem_filter] at hp
    have := (Nat.prime_of_mem_primeFactors hp.1).two_le
    omega
  have hFsub : F ⊆ oddPrimesUpTo B := by
    intro p hp
    simp only [hF, Finset.mem_filter] at hp
    refine mem_oddPrimesUpTo.mpr ⟨?_, Nat.prime_of_mem_primeFactors hp.1, hp.2⟩
    exact le_trans (Nat.le_of_mem_primeFactors hp.1) hkB
  -- `S(k) = Σ_{A ⊆ F} gA A`
  have hexp : SingSeries k = ∑ A ∈ F.powerset, gA A := by
    unfold SingSeries gA
    rw [← hF, sum_powerset_prod F (fun p => 1 / ((p : ℝ) - 2))]
    apply Finset.prod_congr rfl
    intro p hp
    have h3 : 3 ≤ p := hF3 p hp
    have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [hexp]
  -- each `A ⊆ F` contributes with `dA A ∣ k`, and everything is nonnegative
  have hstep : ∑ A ∈ F.powerset, gA A =
      ∑ A ∈ F.powerset, (if dA A ∣ k then gA A else 0) := by
    apply Finset.sum_congr rfl
    intro A hA
    have hAF : A ⊆ F := Finset.mem_powerset.mp hA
    have hdvd : dA A ∣ k := by
      unfold dA
      apply prod_subset_primeFactors_dvd
      intro p hp
      have := hAF hp
      simp only [hF, Finset.mem_filter] at this
      exact this.1
    rw [if_pos hdvd]
  rw [hstep]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.powerset_mono.mpr hFsub
  · intro A hA _
    have hAsub : A ⊆ oddPrimesUpTo B := Finset.mem_powerset.mp hA
    by_cases hdvd : dA A ∣ k
    · rw [if_pos hdvd]; exact gA_nonneg hAsub
    · rw [if_neg hdvd]

/-! ## Counting window primes in a residue class -/

/-- The trivial count: at most `n/d` window primes have `d ∣ 2q - b`. -/
lemma count_crude (n b d : ℕ) (hd : 0 < d) (W' : Finset ℕ)
    (h2q : ∀ q ∈ W', b + 4 ≤ 2 * q ∧ 2 * q ≤ n) :
    ((W'.filter (fun q => d ∣ 2 * q - b)).card : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  have hinj : ((W'.filter (fun q => d ∣ 2 * q - b)).card) ≤ (Finset.Icc 1 (n / d)).card := by
    apply Finset.card_le_card_of_injOn (fun q => (2 * q - b) / d)
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      obtain ⟨hqW, hdvd⟩ := hq
      obtain ⟨hb4, hle⟩ := h2q q hqW
      obtain ⟨j, hj⟩ := hdvd
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · rw [h, Nat.mul_zero] at hj
          omega
        · exact h
      simp only [Finset.mem_coe, Finset.mem_Icc]
      constructor
      · rw [hj, Nat.mul_div_cancel_left j hd]
        exact hj1
      · rw [hj, Nat.mul_div_cancel_left j hd]
        have hdj : d * j ≤ n := by omega
        refine (Nat.le_div_iff_mul_le hd).mpr ?_
        rw [Nat.mul_comm]
        exact hdj
    · intro q hq q' hq' heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
      obtain ⟨hqW, hdvd⟩ := hq
      obtain ⟨hqW', hdvd'⟩ := hq'
      obtain ⟨hb4, -⟩ := h2q q hqW
      obtain ⟨hb4', -⟩ := h2q q' hqW'
      obtain ⟨j, hj⟩ := hdvd
      obtain ⟨j', hj'⟩ := hdvd'
      simp only at heq
      rw [hj, hj', Nat.mul_div_cancel_left j hd, Nat.mul_div_cancel_left j' hd] at heq
      subst heq
      omega
  have hcard : (Finset.Icc 1 (n / d)).card = n / d := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  calc ((W'.filter (fun q => d ∣ 2 * q - b)).card : ℝ)
      ≤ ((n / d : ℕ) : ℝ) := by
        rw [← hcard]
        exact_mod_cast hinj
    _ ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le

/-- Windows sit inside the initial segment. -/
lemma primesIn_subset_left {a b : ℝ} (ha : 0 ≤ a) : primesIn a b ⊆ primesIn 0 b := by
  intro p hp
  unfold primesIn at hp ⊢
  simp only [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  have := hp.2.2
  have h2 := hp.2.1.two_le
  have : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    linarith
  exact this

/-- `√n ≤ n/4` for `n ≥ 16`. -/
lemma sqrt_le_quarter {n : ℕ} (hn : 16 ≤ n) : Real.sqrt n ≤ (n : ℝ) / 4 := by
  have hn' : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) ≤ ((n : ℝ) / 4) ^ 2 := by nlinarith
  calc Real.sqrt n ≤ Real.sqrt (((n : ℝ) / 4) ^ 2) := Real.sqrt_le_sqrt h1
    _ = (n : ℝ) / 4 := Real.sqrt_sq (by positivity)

/-- Brun--Titchmarsh count for the window: for odd `d ≤ √n`,
`#{q ∈ W' : d ∣ 2q - b} ≤ (5/2) n/(φ(d) log n)`. -/
lemma count_bt (n b d : ℕ) (hn : 1024 ≤ n) (hd : 0 < d) (hdodd : ¬ 2 ∣ d)
    (hdsq : (d : ℝ) ≤ Real.sqrt n) (W' : Finset ℕ)
    (hW' : ∀ q ∈ W', q ∈ primesIn (((n : ℝ) + 2) / 4) ((n : ℝ) / 2))
    (hb : ∀ q ∈ W', b ≤ 2 * q) :
    ((W'.filter (fun q => d ∣ 2 * q - b)).card : ℝ) ≤
      5 / 2 * (n : ℝ) / ((Nat.totient d : ℝ) * Real.log n) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hn' : (1024 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have htot : (0 : ℝ) < (Nat.totient d : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hcop2 : Nat.Coprime 2 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hdodd
  have hu2 : IsUnit (((2 : ℕ) : ZMod d)) := (ZMod.isUnit_iff_coprime 2 d).mpr hcop2
  set a : ZMod d := (((2 : ℕ) : ZMod d))⁻¹ * ((b : ℕ) : ZMod d) with ha_def
  -- membership in the filter forces the residue class `a`
  have hclass : ∀ q ∈ W', d ∣ 2 * q - b → ((q : ℕ) : ZMod d) = a := by
    intro q hq hdvd
    have hble : b ≤ 2 * q := hb q hq
    have hcast : ((2 * q - b : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hsub : ((2 * q : ℕ) : ZMod d) - ((b : ℕ) : ZMod d) = 0 := by
      rw [← Nat.cast_sub hble]
      exact hcast
    have h2q : ((2 : ℕ) : ZMod d) * ((q : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) := by
      have := sub_eq_zero.mp hsub
      rw [← this, Nat.cast_mul]
    calc ((q : ℕ) : ZMod d)
        = ((((2 : ℕ) : ZMod d))⁻¹ * ((2 : ℕ) : ZMod d)) * ((q : ℕ) : ZMod d) := by
          rw [ZMod.inv_mul_of_unit _ hu2, one_mul]
      _ = (((2 : ℕ) : ZMod d))⁻¹ * (((2 : ℕ) : ZMod d) * ((q : ℕ) : ZMod d)) := by ring
      _ = a := by rw [h2q]
  by_cases hua : IsUnit a
  · -- reduced class: Brun--Titchmarsh
    have hsubset : W'.filter (fun q => d ∣ 2 * q - b) ⊆
        (primesIn 0 ((n : ℝ) / 2)).filter (fun p : ℕ => (Nat.cast p : ZMod d) = a) := by
      intro q hq
      simp only [Finset.mem_filter] at hq
      obtain ⟨hqW, hdvd⟩ := hq
      simp only [Finset.mem_filter]
      refine ⟨primesIn_subset_left (by positivity) (hW' q hqW), hclass q hqW hdvd⟩
    have hdx : (d : ℝ) < (n : ℝ) / 2 := by
      have h16 : 16 ≤ n := by omega
      have := sqrt_le_quarter h16
      have h4 : (n : ℝ) / 4 < (n : ℝ) / 2 := by linarith
      linarith
    have hbt := brun_titchmarsh d hd a hua ((n : ℝ) / 2) hdx
    have hcount : ((W'.filter (fun q => d ∣ 2 * q - b)).card : ℝ) ≤
        2 * ((n : ℝ) / 2) / ((Nat.totient d : ℝ) * Real.log ((n : ℝ) / 2 / d)) := by
      refine le_trans ?_ hbt
      exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsubset)
    -- `log((n/2)/d) ≥ 0.4 log n`
    have hlow : (2 : ℝ) / 5 * Real.log n ≤ Real.log ((n : ℝ) / 2 / d) := by
      have hsqpos0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
      have hstep1 : Real.sqrt n / 2 ≤ (n : ℝ) / 2 / d := by
        have h1 : (n : ℝ) / 2 / (d : ℝ) = (n : ℝ) / (2 * (d : ℝ)) := by rw [div_div]
        have h2 : (n : ℝ) / (2 * Real.sqrt n) ≤ (n : ℝ) / (2 * (d : ℝ)) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          linarith
        have h3 : (n : ℝ) / (2 * Real.sqrt n) = Real.sqrt n / 2 := by
          rw [show (2 : ℝ) * Real.sqrt n = Real.sqrt n * 2 by ring, ← div_div,
            Real.div_sqrt]
        rw [h1, ← h3]
        exact h2
      have hsqpos : (0 : ℝ) < Real.sqrt n / 2 := by
        have : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
        linarith
      have hmono : Real.log (Real.sqrt n / 2) ≤ Real.log ((n : ℝ) / 2 / d) :=
        Real.log_le_log hsqpos hstep1
      have hval : Real.log (Real.sqrt n / 2) = 1 / 2 * Real.log n - Real.log 2 := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by positivity)]
        ring
      have h2n : Real.log 2 ≤ 1 / 10 * Real.log n := by
        have h1024 : Real.log 1024 ≤ Real.log n :=
          Real.log_le_log (by norm_num) hn'
        have h2 : Real.log 1024 = 10 * Real.log 2 := by
          rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
          norm_num
        linarith
      linarith
    -- assemble
    have hden : (0 : ℝ) < (Nat.totient d : ℝ) * ((2 : ℝ) / 5 * Real.log n) := by positivity
    calc ((W'.filter (fun q => d ∣ 2 * q - b)).card : ℝ)
        ≤ 2 * ((n : ℝ) / 2) / ((Nat.totient d : ℝ) * Real.log ((n : ℝ) / 2 / d)) := hcount
      _ ≤ 2 * ((n : ℝ) / 2) / ((Nat.totient d : ℝ) * ((2 : ℝ) / 5 * Real.log n)) := by
          apply div_le_div_of_nonneg_left (by positivity) hden
          exact mul_le_mul_of_nonneg_left hlow htot.le
      _ = 5 / 2 * (n : ℝ) / ((Nat.totient d : ℝ) * Real.log n) := by
          field_simp
  · -- non-reduced class: the window is empty
    have hempty : W'.filter (fun q => d ∣ 2 * q - b) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro q hq
      simp only [Finset.mem_filter] at hq
      obtain ⟨hqW, hdvd⟩ := hq
      have hqmem := hW' q hqW
      have hqp : q.Prime := prime_of_mem_primesIn hqmem
      have hqlow : ((n : ℝ) + 2) / 4 < (q : ℝ) := lt_of_mem_primesIn hqmem
      have hqa := hclass q hqW hdvd
      by_cases hcq : Nat.Coprime q d
      · exact hua (hqa ▸ (ZMod.isUnit_iff_coprime q d).mpr hcq)
      · have hqd : q ∣ d := by
          by_contra hnd
          exact hcq ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hnd)
        have hqled : (q : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast Nat.le_of_dvd hd hqd
        have h16 : 16 ≤ n := by omega
        have hs4 := sqrt_le_quarter h16
        -- `q ≤ d ≤ √n ≤ n/4 < (n+2)/4 < q`
        have : (n : ℝ) / 4 < ((n : ℝ) + 2) / 4 := by linarith
        linarith
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- `log x ≤ 8 · ⁸√x`, by three halvings and `log y ≤ y - 1`. -/
lemma log_le_eight_sqrt3 {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (1 : ℝ) ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have h2 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt x) := Real.one_le_sqrt.mpr h1
  have h3 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt x)) := Real.one_le_sqrt.mpr h2
  have gen : ∀ y : ℝ, 0 ≤ y → Real.log y = 2 * Real.log (Real.sqrt y) := by
    intro y hy
    rw [Real.log_sqrt hy]
    ring
  have e1 := gen x h0.le
  have e2 := gen (Real.sqrt x) (Real.sqrt_nonneg x)
  have e3 := gen (Real.sqrt (Real.sqrt x)) (Real.sqrt_nonneg _)
  have hle : Real.log (Real.sqrt (Real.sqrt (Real.sqrt x))) ≤
      Real.sqrt (Real.sqrt (Real.sqrt x)) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  linarith

/-- **Lemma 6.4** (the averaging lemma).  For any shift `b`,
`Σ_{q ∈ W'} S(2q - b) ≤ 7 n / log n`, uniformly over subsets `W'` of the window
whose elements clear the shift. -/
theorem averaging (n : ℕ) (hn : 810 ^ 8 ≤ n) (b : ℕ) (W' : Finset ℕ)
    (hW' : ∀ q ∈ W', q ∈ primesIn (((n : ℝ) + 2) / 4) ((n : ℝ) / 2))
    (hb4 : ∀ q ∈ W', b + 4 ≤ 2 * q) :
    ∑ q ∈ W', SingSeries (2 * q - b) ≤ 7 * (n : ℝ) / Real.log n := by
  have hn6 : 1024 ≤ n := le_trans (by norm_num) hn
  have hn' : (1024 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsq2 : (0 : ℝ) < Real.sqrt (Real.sqrt n) := Real.sqrt_pos.mpr hsq
  have h2qn : ∀ q ∈ W', 2 * q ≤ n := by
    intro q hq
    have hle := le_of_mem_primesIn (by positivity) (hW' q hq)
    have h2 : ((2 * q : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  set 𝒜 := (oddPrimesUpTo n).powerset with h𝒜
  have hodd3 : ∀ p ∈ oddPrimesUpTo n, 3 ≤ p := fun p hp => three_le_of_mem_odd hp
  -- pointwise expansion and swap
  have hpoint : ∑ q ∈ W', SingSeries (2 * q - b) ≤
      ∑ A ∈ 𝒜, (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)) := by
    calc ∑ q ∈ W', SingSeries (2 * q - b)
        ≤ ∑ q ∈ W', ∑ A ∈ 𝒜, (if dA A ∣ 2 * q - b then gA A else 0) := by
          apply Finset.sum_le_sum
          intro q hq
          exact singSeries_le_sum n (2 * q - b)
            (by have := hb4 q hq; omega)
            (by have := h2qn q hq; omega)
      _ = ∑ A ∈ 𝒜, ∑ q ∈ W', (if dA A ∣ 2 * q - b then gA A else 0) :=
          Finset.sum_comm
      _ = ∑ A ∈ 𝒜, (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro A _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- split at `dA A ≤ √n`
  have hsplit := Finset.sum_filter_add_sum_filter_not 𝒜
    (fun A => (dA A : ℝ) ≤ Real.sqrt n)
    (fun A => gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ))
  -- the ratio expansions, used by both branches
  have hprime : ∀ A ∈ 𝒜, ∀ p ∈ A, p.Prime := by
    intro A hA p hp
    exact (mem_oddPrimesUpTo.mp ((Finset.mem_powerset.mp hA) hp)).2.1
  have hthree : ∀ A ∈ 𝒜, ∀ p ∈ A, 3 ≤ p := by
    intro A hA p hp
    exact three_le_of_mem_odd ((Finset.mem_powerset.mp hA) hp)
  -- SMALL BRANCH
  have hsmall : ∑ A ∈ 𝒜.filter (fun A => (dA A : ℝ) ≤ Real.sqrt n),
      (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)) ≤
      5 / 2 * 2.72 * ((n : ℝ) / Real.log n) := by
    have hperA : ∀ A ∈ 𝒜.filter (fun A => (dA A : ℝ) ≤ Real.sqrt n),
        gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ) ≤
          5 / 2 * ((n : ℝ) / Real.log n) *
            (∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)))) := by
      intro A hA
      simp only [Finset.mem_filter] at hA
      obtain ⟨hA𝒜, hAsq⟩ := hA
      have hAsub : A ⊆ oddPrimesUpTo n := Finset.mem_powerset.mp hA𝒜
      have hgnn : 0 ≤ gA A := gA_nonneg hAsub
      have hbt := count_bt n b (dA A) hn6 (dA_pos hAsub) (dA_odd hAsub) hAsq W' hW'
        (fun q hq => by have := hb4 q hq; omega)
      have htotpos : (0 : ℝ) < (Nat.totient (dA A) : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (dA_pos hAsub)
      calc gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)
          ≤ gA A * (5 / 2 * (n : ℝ) / ((Nat.totient (dA A) : ℝ) * Real.log n)) :=
            mul_le_mul_of_nonneg_left hbt hgnn
        _ = 5 / 2 * ((n : ℝ) / Real.log n) * (gA A * (1 / (Nat.totient (dA A) : ℝ))) := by
            field_simp
        _ = 5 / 2 * ((n : ℝ) / Real.log n) *
              (∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)))) := by
            congr 1
            -- `gA A / φ(dA A) = Π 1/((p-2)(p-1))`
            unfold gA dA
            rw [totient_prod_primes A (fun p hp => hprime A hA𝒜 p hp), Nat.cast_prod,
              one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro p hp
            have h3 : 3 ≤ p := hthree A hA𝒜 p hp
            have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
            have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
              have : 1 ≤ p := by omega
              push_cast [this]
              ring
            rw [hc]
            have hne1 : (p : ℝ) - 2 ≠ 0 := by linarith
            have hne2 : (p : ℝ) - 1 ≠ 0 := by linarith
            field_simp
    calc ∑ A ∈ 𝒜.filter (fun A => (dA A : ℝ) ≤ Real.sqrt n),
        (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ))
        ≤ ∑ A ∈ 𝒜.filter (fun A => (dA A : ℝ) ≤ Real.sqrt n),
            5 / 2 * ((n : ℝ) / Real.log n) *
              (∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)))) :=
          Finset.sum_le_sum hperA
      _ ≤ ∑ A ∈ 𝒜, 5 / 2 * ((n : ℝ) / Real.log n) *
              (∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro A hA _
          have h3 := hthree A hA
          have : 0 ≤ ∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) := by
            apply Finset.prod_nonneg
            intro p hp
            have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3 p hp
            have e1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
            have e2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            positivity
          positivity
      _ = 5 / 2 * ((n : ℝ) / Real.log n) *
            ∑ A ∈ 𝒜, (∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)))) := by
          rw [Finset.mul_sum]
      _ ≤ 5 / 2 * ((n : ℝ) / Real.log n) * Real.exp 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ A ∈ 𝒜, (∏ p ∈ A, (1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))))
              = ∏ p ∈ oddPrimesUpTo n, (1 + 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) :=
                sum_powerset_prod _ _
            _ ≤ Real.exp (∑ p ∈ oddPrimesUpTo n, 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1))) := by
                apply prod_one_add_le_exp_sum
                intro p hp
                have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd3 p hp
                have e1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
                have e2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
                positivity
            _ ≤ Real.exp 1 :=
                Real.exp_le_exp.mpr (telescope_one _ hodd3)
      _ ≤ 5 / 2 * 2.72 * ((n : ℝ) / Real.log n) := by
          have := exp_one_le
          have hnl : (0 : ℝ) ≤ (n : ℝ) / Real.log n := by positivity
          nlinarith
  -- TAIL BRANCH
  have htail : ∑ A ∈ 𝒜.filter (fun A => ¬ (dA A : ℝ) ≤ Real.sqrt n),
      (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)) ≤
      20.2 * ((n : ℝ) / Real.sqrt (Real.sqrt n)) := by
    have hperA : ∀ A ∈ 𝒜.filter (fun A => ¬ (dA A : ℝ) ≤ Real.sqrt n),
        gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ) ≤
          ((n : ℝ) / Real.sqrt (Real.sqrt n)) *
            (∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2)))) := by
      intro A hA
      simp only [Finset.mem_filter, not_le] at hA
      obtain ⟨hA𝒜, hAsq⟩ := hA
      have hAsub : A ⊆ oddPrimesUpTo n := Finset.mem_powerset.mp hA𝒜
      have hgnn : 0 ≤ gA A := gA_nonneg hAsub
      have hdpos : (0 : ℝ) < (dA A : ℝ) := by exact_mod_cast dA_pos hAsub
      have hsqd : (0 : ℝ) < Real.sqrt (dA A) := Real.sqrt_pos.mpr hdpos
      have hcrude := count_crude n b (dA A) (dA_pos hAsub) W'
        (fun q hq => ⟨hb4 q hq, h2qn q hq⟩)
      have hkey : (n : ℝ) / (dA A : ℝ) ≤
          ((n : ℝ) / Real.sqrt (Real.sqrt n)) * (1 / Real.sqrt (dA A)) := by
        have hd2 : Real.sqrt (dA A) * Real.sqrt (Real.sqrt n) ≤ (dA A : ℝ) := by
          have h1 : Real.sqrt (Real.sqrt n) ≤ Real.sqrt (dA A) :=
            Real.sqrt_le_sqrt hAsq.le
          calc Real.sqrt (dA A) * Real.sqrt (Real.sqrt n)
              ≤ Real.sqrt (dA A) * Real.sqrt (dA A) :=
                mul_le_mul_of_nonneg_left h1 hsqd.le
            _ = (dA A : ℝ) := Real.mul_self_sqrt hdpos.le
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
        apply div_le_div_of_nonneg_left hnpos.le (by positivity) hd2
      calc gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)
          ≤ gA A * ((n : ℝ) / (dA A : ℝ)) := mul_le_mul_of_nonneg_left hcrude hgnn
        _ ≤ gA A * (((n : ℝ) / Real.sqrt (Real.sqrt n)) * (1 / Real.sqrt (dA A))) :=
            mul_le_mul_of_nonneg_left hkey hgnn
        _ = ((n : ℝ) / Real.sqrt (Real.sqrt n)) * (gA A * (1 / Real.sqrt (dA A))) := by
            ring
        _ = ((n : ℝ) / Real.sqrt (Real.sqrt n)) *
              (∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2)))) := by
            congr 1
            unfold gA dA
            rw [Nat.cast_prod, sqrt_prod, one_div, ← Finset.prod_inv_distrib,
              ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro p hp
            have h3 : 3 ≤ p := hthree A hA𝒜 p hp
            have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
            have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
            have hne1 : (p : ℝ) - 2 ≠ 0 := by linarith
            field_simp
    calc ∑ A ∈ 𝒜.filter (fun A => ¬ (dA A : ℝ) ≤ Real.sqrt n),
        (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ))
        ≤ ∑ A ∈ 𝒜.filter (fun A => ¬ (dA A : ℝ) ≤ Real.sqrt n),
            ((n : ℝ) / Real.sqrt (Real.sqrt n)) *
              (∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2)))) :=
          Finset.sum_le_sum hperA
      _ ≤ ∑ A ∈ 𝒜, ((n : ℝ) / Real.sqrt (Real.sqrt n)) *
              (∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2)))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro A hA _
          have h3 := hthree A hA
          have hpr : 0 ≤ ∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2))) := by
            apply Finset.prod_nonneg
            intro p hp
            have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3 p hp
            have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
            have e1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
            positivity
          positivity
      _ = ((n : ℝ) / Real.sqrt (Real.sqrt n)) *
            ∑ A ∈ 𝒜, (∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2)))) := by
          rw [Finset.mul_sum]
      _ ≤ ((n : ℝ) / Real.sqrt (Real.sqrt n)) * Real.exp 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ A ∈ 𝒜, (∏ p ∈ A, (1 / (Real.sqrt p * ((p : ℝ) - 2))))
              = ∏ p ∈ oddPrimesUpTo n, (1 + 1 / (Real.sqrt p * ((p : ℝ) - 2))) :=
                sum_powerset_prod _ _
            _ ≤ Real.exp (∑ p ∈ oddPrimesUpTo n, 1 / (Real.sqrt p * ((p : ℝ) - 2))) := by
                apply prod_one_add_le_exp_sum
                intro p hp
                have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd3 p hp
                have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
                have e1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
                positivity
            _ ≤ Real.exp 3 :=
                Real.exp_le_exp.mpr (telescope_sqrt _ hodd3)
      _ ≤ 20.2 * ((n : ℝ) / Real.sqrt (Real.sqrt n)) := by
          have := exp_three_le
          have hnl : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt (Real.sqrt n) := by positivity
          nlinarith
  -- FINAL NUMERIC ASSEMBLY
  have hfinal : 5 / 2 * 2.72 * ((n : ℝ) / Real.log n) +
      20.2 * ((n : ℝ) / Real.sqrt (Real.sqrt n)) ≤ 7 * (n : ℝ) / Real.log n := by
    have ht := log_le_eight_sqrt3 (show (1 : ℝ) ≤ (n : ℝ) by linarith)
    set t := Real.sqrt (Real.sqrt (Real.sqrt n)) with htdef
    have ht0 : (0 : ℝ) < t := Real.sqrt_pos.mpr hsq2
    have ht2 : t ^ 2 = Real.sqrt (Real.sqrt n) := Real.sq_sqrt hsq2.le
    -- `t ≥ 810`
    have hstage1 : (810 : ℝ) ^ 4 ≤ Real.sqrt n := by
      rw [Real.le_sqrt (by positivity) hnpos.le]
      have : ((810 : ℝ) ^ 4) ^ 2 = (810 : ℝ) ^ 8 := by ring
      rw [this]
      exact_mod_cast hn
    have hstage2 : (810 : ℝ) ^ 2 ≤ Real.sqrt (Real.sqrt n) := by
      rw [Real.le_sqrt (by positivity) hsq.le]
      have : ((810 : ℝ) ^ 2) ^ 2 = (810 : ℝ) ^ 4 := by ring
      rw [this]
      exact hstage1
    have hstage3 : (810 : ℝ) ≤ t := by
      rw [htdef, Real.le_sqrt (by positivity) hsq2.le]
      have : ((810 : ℝ)) ^ 2 = (810 : ℝ) ^ 2 := rfl
      exact hstage2
    -- `101 log n ≤ √√n`
    have hkey : 101 * Real.log n ≤ Real.sqrt (Real.sqrt n) := by
      have h1 : 101 * Real.log n ≤ 101 * (8 * t) :=
        mul_le_mul_of_nonneg_left ht (by norm_num)
      have h2 : 808 * t ≤ t * t := by nlinarith
      have h3 : t * t = Real.sqrt (Real.sqrt n) := by
        rw [← ht2]; ring
      linarith
    -- so `20.2 n/√√n ≤ 0.2 n/log n`
    have hmain : 20.2 * ((n : ℝ) / Real.sqrt (Real.sqrt n)) ≤
        1 / 5 * ((n : ℝ) / Real.log n) := by
      have h1 : (101 * (n : ℝ)) / Real.sqrt (Real.sqrt n) ≤ (n : ℝ) / Real.log n := by
        rw [div_le_div_iff₀ hsq2 hlogn]
        calc 101 * (n : ℝ) * Real.log n = (n : ℝ) * (101 * Real.log n) := by ring
          _ ≤ (n : ℝ) * Real.sqrt (Real.sqrt n) :=
              mul_le_mul_of_nonneg_left hkey hnpos.le
      have e : 20.2 * ((n : ℝ) / Real.sqrt (Real.sqrt n)) =
          1 / 5 * ((101 * (n : ℝ)) / Real.sqrt (Real.sqrt n)) := by
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hsum : 5 / 2 * 2.72 * ((n : ℝ) / Real.log n) = 6.8 * ((n : ℝ) / Real.log n) := by
      norm_num
    have hgoal : 7 * (n : ℝ) / Real.log n = 7 * ((n : ℝ) / Real.log n) := by
      ring
    rw [hsum, hgoal]
    linarith
  calc ∑ q ∈ W', SingSeries (2 * q - b)
      ≤ ∑ A ∈ 𝒜, (gA A * ((W'.filter (fun q => dA A ∣ 2 * q - b)).card : ℝ)) := hpoint
    _ = _ + _ := hsplit.symm
    _ ≤ 5 / 2 * 2.72 * ((n : ℝ) / Real.log n) + 20.2 * ((n : ℝ) / Real.sqrt (Real.sqrt n)) :=
        add_le_add hsmall htail
    _ ≤ 7 * (n : ℝ) / Real.log n := hfinal

end UniversalWords


