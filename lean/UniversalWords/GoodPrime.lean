/-
§6.3 of the paper: Proposition 6.5, **proved** from the analytic axioms.

`exists_good_prime` — previously an axiom — is derived here from `vinogradov`,
`sieve_r2`, `brun_titchmarsh` (through `averaging`) and the Rosser–Schoenfeld
`π`-bounds, exactly as in the paper: the window `W` has `≥ 0.15 n/log n` primes;
at most `2L/log n` of them divide `s`; Markov's inequality against the averaged
sieve bound removes the `q̃` whose ternary representations meet the primes of
`rs` too often; any surviving `q̃` is good.
-/
import UniversalWords.Averaging

namespace UniversalWords

open scoped Classical

/-! ## Small numeric helpers -/

/-- `k/log²k ≤ 4n/log²n` for `4 ≤ k ≤ n`, `n` large. -/
lemma ratio_le (k n : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n) (hn : 10 ^ 6 ≤ n) :
    (k : ℝ) / (Real.log k) ^ 2 ≤ 4 * (n : ℝ) / (Real.log n) ^ 2 := by
  have hk' : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hn' : (10 : ℝ) ^ 6 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  have hlogk : (0 : ℝ) < Real.log k := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ Real.log k := Real.log_le_log (by norm_num) hk'
  have hlog4' : (1.38 : ℝ) ≤ Real.log 4 := by
    have h1 : (1.38 : ℝ) ≤ 2 * 0.6931471803 := by norm_num
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  rcases le_or_gt (k : ℝ) (Real.sqrt n) with hsm | hlg
  · -- `k ≤ √n`: crude
    have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hlk2 : (1.38 : ℝ) ^ 2 ≤ (Real.log k) ^ 2 := by nlinarith
    have h1 : (k : ℝ) / (Real.log k) ^ 2 ≤ Real.sqrt n / (1.38) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hsq.le, hk']
    -- `√n / 1.9 ≤ 4n/log²n  ⟺  log²n · √n ≤ 7.6 n`
    have hlog2 : (Real.log n) ^ 2 ≤ 64 * Real.sqrt (Real.sqrt n) := by
      have hl := log_le_eight_sqrt3 (show (1 : ℝ) ≤ (n : ℝ) by linarith)
      have ht : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt n)) := Real.sqrt_nonneg _
      have hsq2 : Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2 = Real.sqrt (Real.sqrt n) :=
        Real.sq_sqrt (Real.sqrt_nonneg _)
      nlinarith
    have hq4 : (8.43 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
      rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]
      rw [Real.le_sqrt (by positivity) hnpos.le]
      nlinarith
    have hss : Real.sqrt (Real.sqrt n) * Real.sqrt (Real.sqrt n) = Real.sqrt n :=
      Real.mul_self_sqrt (Real.sqrt_nonneg n)
    have hsn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1 ⊢
    -- goal: `k · log²n ≤ 4n · log²k`; use `h1 : k · 1.9044 ≤ √n · log²k`
    -- and `log²n · √n ≤ 64·√√n·√n ≤ 7.6·n` for `√√n ≥ 8.43`
    have hstep : (Real.log n) ^ 2 * Real.sqrt n ≤ 7.6 * (n : ℝ) := by
      calc (Real.log n) ^ 2 * Real.sqrt n ≤ 64 * Real.sqrt (Real.sqrt n) * Real.sqrt n := by
            nlinarith [Real.sqrt_nonneg n]
        _ ≤ 7.6 * (n : ℝ) := by nlinarith [Real.sqrt_nonneg n, Real.sqrt_nonneg (Real.sqrt n)]
    nlinarith [sq_nonneg (Real.log k), Real.sqrt_nonneg n]
  · -- `k > √n`: `log k ≥ log √n = log n / 2`
    have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hlk : Real.log n / 2 ≤ Real.log k := by
      have h1 : Real.log (Real.sqrt n) ≤ Real.log k := Real.log_le_log hsq hlg.le
      rw [Real.log_sqrt hnpos.le] at h1
      exact h1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- `k log²n ≤ 4 n log²k`, from `log k ≥ log n / 2` and `k ≤ n`
    have h2 : (Real.log n / 2) ^ 2 ≤ (Real.log k) ^ 2 := by nlinarith
    have h3 : (k : ℝ) * (Real.log n) ^ 2 ≤ (n : ℝ) * (Real.log n) ^ 2 :=
      mul_le_mul_of_nonneg_right hkn' (sq_nonneg _)
    have h4 : (n : ℝ) * (Real.log n) ^ 2 = 4 * (n : ℝ) * (Real.log n / 2) ^ 2 := by ring
    have h5 : 4 * (n : ℝ) * (Real.log n / 2) ^ 2 ≤ 4 * (n : ℝ) * (Real.log k) ^ 2 := by
      nlinarith [hnpos.le]
    linarith

/-- The window `W`. -/
noncomputable def W (n : ℕ) : Finset ℕ := primesIn (((n : ℝ) + 2) / 4) ((n : ℝ) / 2)

lemma W_prime {n q : ℕ} (h : q ∈ W n) : q.Prime := prime_of_mem_primesIn h

lemma W_low {n q : ℕ} (h : q ∈ W n) : ((n : ℝ) + 2) / 4 < (q : ℝ) := lt_of_mem_primesIn h

lemma W_high {n q : ℕ} (hn : 0 < n) (h : q ∈ W n) : (q : ℝ) ≤ (n : ℝ) / 2 :=
  le_of_mem_primesIn (by positivity) h

/-- Crude size bound: `|W| ≤ n`. -/
lemma W_card_le (n : ℕ) (hn : 2 ≤ n) : ((W n).card : ℝ) ≤ (n : ℝ) := by
  have hsub : W n ⊆ Finset.range (⌊(n : ℝ) / 2⌋₊ + 1) := by
    intro q hq
    unfold W primesIn at hq
    simp only [Finset.mem_filter] at hq
    exact hq.1
  have h1 : (W n).card ≤ ⌊(n : ℝ) / 2⌋₊ + 1 := by
    calc (W n).card ≤ (Finset.range (⌊(n : ℝ) / 2⌋₊ + 1)).card := Finset.card_le_card hsub
      _ = ⌊(n : ℝ) / 2⌋₊ + 1 := Finset.card_range _
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc ((W n).card : ℝ) ≤ (⌊(n : ℝ) / 2⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    _ ≤ (n : ℝ) / 2 + 1 := by
        have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
        linarith
    _ ≤ (n : ℝ) := by linarith

lemma singSeries_nonneg (k : ℕ) : 0 ≤ SingSeries k := by
  unfold SingSeries
  apply Finset.prod_nonneg
  intro p hp
  simp only [Finset.mem_filter] at hp
  have h2 := (Nat.prime_of_mem_primeFactors hp.1).two_le
  have h3 : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp.2
    · exact h
  have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have e1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have e2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

/-- `|W| ≥ 0.15 n / log n` for `n ≥ 810⁸`, by Rosser--Schoenfeld. -/
lemma W_card_ge (hPiU : PiUpperStatement) (hPiL : PiLowerStatement)
    (n : ℕ) (hn : 810 ^ 8 ≤ n) :
    0.15 * (n : ℝ) / Real.log n ≤ ((W n).card : ℝ) := by
  have hn' : ((810 : ℝ)) ^ 8 ≤ (n : ℝ) := by exact_mod_cast hn
  have hbig : (10 : ℝ) ^ 6 ≤ (n : ℝ) := by nlinarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
  -- the sdiff sits inside `W`
  have hsub : primesIn 0 ((n : ℝ) / 2) \ primesIn 0 (((n : ℝ) + 2) / 4) ⊆ W n := by
    intro p hp
    simp only [Finset.mem_sdiff] at hp
    obtain ⟨hin, hout⟩ := hp
    unfold primesIn at hin hout
    unfold W primesIn
    simp only [Finset.mem_filter, Finset.mem_range] at hin hout ⊢
    obtain ⟨hr, hpp, hp0⟩ := hin
    refine ⟨hr, hpp, ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hout
    refine ⟨?_, hpp, hp0⟩
    have hfl : (p : ℝ) ≤ ((n : ℝ) + 2) / 4 := hcon
    have : p ≤ ⌊((n : ℝ) + 2) / 4⌋₊ := Nat.le_floor hfl
    omega
  have hcard : (primesIn 0 ((n : ℝ) / 2)).card -
      (primesIn 0 (((n : ℝ) + 2) / 4)).card ≤ (W n).card :=
    le_trans (Finset.le_card_sdiff _ _) (Finset.card_le_card hsub)
  -- lower bound for `π(n/2)`
  have hpil : ((n : ℝ) / 2) / Real.log ((n : ℝ) / 2) ≤
      ((primesIn 0 ((n : ℝ) / 2)).card : ℝ) :=
    hPiL _ (by nlinarith)
  have hpil' : 0.5 * (n : ℝ) / Real.log n ≤ ((primesIn 0 ((n : ℝ) / 2)).card : ℝ) := by
    refine le_trans ?_ hpil
    have hl2 : (0 : ℝ) < Real.log ((n : ℝ) / 2) := Real.log_pos (by nlinarith)
    have hmono : Real.log ((n : ℝ) / 2) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by linarith)
    rw [div_le_div_iff₀ hlogn hl2]
    nlinarith
  -- upper bound for `π((n+2)/4)`
  have hpiu : ((primesIn 0 (((n : ℝ) + 2) / 4)).card : ℝ) ≤
      1.25506 * (((n : ℝ) + 2) / 4) / Real.log (((n : ℝ) + 2) / 4) :=
    hPiU _ (by nlinarith)
  have hpiu' : ((primesIn 0 (((n : ℝ) + 2) / 4)).card : ℝ) ≤ 0.349 * (n : ℝ) / Real.log n := by
    refine le_trans hpiu ?_
    have hx1 : ((n : ℝ) + 2) / 4 ≤ 0.2501 * (n : ℝ) := by nlinarith
    have hx2 : 0.9 * Real.log n ≤ Real.log (((n : ℝ) + 2) / 4) := by
      have hstep : Real.log ((n : ℝ) / 4) ≤ Real.log (((n : ℝ) + 2) / 4) :=
        Real.log_le_log (by positivity) (by linarith)
      have hval : Real.log ((n : ℝ) / 4) = Real.log n - Real.log 4 := by
        rw [Real.log_div (by positivity) (by norm_num)]
      have h4 : Real.log 4 ≤ 0.1 * Real.log n := by
        have hlog4n : Real.log (4 ^ 10 : ℝ) ≤ Real.log n := by
          apply Real.log_le_log (by norm_num)
          nlinarith
        have : Real.log ((4 : ℝ) ^ 10) = 10 * Real.log 4 := by
          rw [Real.log_pow]; norm_num
        linarith
      linarith
    have hxpos : (0 : ℝ) < ((n : ℝ) + 2) / 4 := by positivity
    have hlx : (0 : ℝ) < Real.log (((n : ℝ) + 2) / 4) := by linarith [hx2]
    rw [div_le_div_iff₀ hlx hlogn]
    nlinarith
  -- combine
  have hWlow : 0.151 * (n : ℝ) / Real.log n ≤ ((W n).card : ℝ) := by
    have hc : ((primesIn 0 ((n : ℝ) / 2)).card : ℝ) -
        ((primesIn 0 (((n : ℝ) + 2) / 4)).card : ℝ) ≤ ((W n).card : ℝ) := by
      have := hcard
      have hcast : ((primesIn 0 ((n : ℝ) / 2)).card : ℝ) -
          ((primesIn 0 (((n : ℝ) + 2) / 4)).card : ℝ) ≤
          (((primesIn 0 ((n : ℝ) / 2)).card -
            (primesIn 0 (((n : ℝ) + 2) / 4)).card : ℕ) : ℝ) := by
        rcases le_total (primesIn 0 (((n : ℝ) + 2) / 4)).card
            (primesIn 0 ((n : ℝ) / 2)).card with h | h
        · rw [Nat.cast_sub h]
        · have h1 : ((primesIn 0 ((n : ℝ) / 2)).card : ℝ) ≤
              ((primesIn 0 (((n : ℝ) + 2) / 4)).card : ℝ) := by exact_mod_cast h
          have h2 : (0 : ℝ) ≤ (((primesIn 0 ((n : ℝ) / 2)).card -
              (primesIn 0 (((n : ℝ) + 2) / 4)).card : ℕ) : ℝ) := by positivity
          linarith
      calc ((primesIn 0 ((n : ℝ) / 2)).card : ℝ) -
          ((primesIn 0 (((n : ℝ) + 2) / 4)).card : ℝ)
          ≤ (((primesIn 0 ((n : ℝ) / 2)).card -
              (primesIn 0 (((n : ℝ) + 2) / 4)).card : ℕ) : ℝ) := hcast
        _ ≤ ((W n).card : ℝ) := by exact_mod_cast this
    have : 0.151 * (n : ℝ) / Real.log n ≤
        0.5 * (n : ℝ) / Real.log n - 0.349 * (n : ℝ) / Real.log n := by
      rw [div_sub_div_same]
      apply div_le_div_of_nonneg_right ?_ hlogn.le
      nlinarith
    linarith
  refine le_trans ?_ hWlow
  apply div_le_div_of_nonneg_right ?_ hlogn.le
  nlinarith

/-- Primes of the window dividing `s` number at most `2L/log n`. -/
lemma E1_card_le (n : ℕ) (r s : ℤ) (hrs : r * s ≠ 0) (hn : 810 ^ 8 ≤ n) :
    ((((W n).filter (fun q => q ∣ s.natAbs)).card : ℝ) ≤ 2 * L r s / Real.log n) := by
  have hn16 : 16 ≤ n := by
    have : 810 ^ 8 ≥ 16 := by norm_num
    omega
  have hn' : ((810 : ℝ)) ^ 8 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by nlinarith)
  set E1 := (W n).filter (fun q => q ∣ s.natAbs) with hE1
  -- each element carries log-weight `> log n / 2`
  have hlogq : ∀ q ∈ E1, Real.log n / 2 ≤ Real.log q := by
    intro q hq
    simp only [hE1, Finset.mem_filter] at hq
    have hql : ((n : ℝ) + 2) / 4 < (q : ℝ) := W_low hq.1
    have hsq := sqrt_le_quarter hn16
    have hqs : Real.sqrt n ≤ (q : ℝ) := by linarith
    have := Real.log_le_log (Real.sqrt_pos.mpr hnpos) hqs
    rwa [Real.log_sqrt hnpos.le] at this
  -- and sits among the prime factors of `rs`
  have hsub : E1 ⊆ (r * s).natAbs.primeFactors := by
    intro q hq
    simp only [hE1, Finset.mem_filter] at hq
    refine Nat.mem_primeFactors.mpr ⟨W_prime hq.1, ?_, Int.natAbs_ne_zero.mpr hrs⟩
    exact hq.2.trans (by rw [Int.natAbs_mul]; exact Dvd.intro_left _ rfl)
  have hcount : (E1.card : ℝ) * (Real.log n / 2) ≤ L r s := by
    calc (E1.card : ℝ) * (Real.log n / 2)
        = ∑ _q ∈ E1, (Real.log n / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ E1, Real.log q := Finset.sum_le_sum hlogq
      _ ≤ ∑ p ∈ (r * s).natAbs.primeFactors, Real.log p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hp _
          exact Real.log_nonneg
            (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      _ = L r s := (L_eq_sum r s hrs).symm
  rw [le_div_iff₀ hlogn]
  linarith

/-- The excluded primes up to `n` number at most `2.52√n/log n + 2L/log n`. -/
lemma omega_card_le (hPiU : PiUpperStatement)
    (n : ℕ) (r s : ℤ) (hrs : r * s ≠ 0) (hn : 810 ^ 8 ≤ n) :
    ((((r * s).natAbs.primeFactors.filter (fun p => p ≤ n)).card : ℝ) ≤
      2.52 * Real.sqrt n / Real.log n + 2 * L r s / Real.log n) := by
  have hn' : ((810 : ℝ)) ^ 8 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by nlinarith)
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  set Ex := (r * s).natAbs.primeFactors.filter (fun p => p ≤ n) with hEx
  set Small := Ex.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt n) with hSmall
  set Big := Ex.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt n) with hBig
  have hsplitc : Small.card + Big.card = Ex.card := by
    rw [hSmall, hBig]
    exact Finset.card_filter_add_card_filter_not _
  -- small part: inject into `primesIn 0 (√n)`
  have hsmall : (Small.card : ℝ) ≤ 2.52 * Real.sqrt n / Real.log n := by
    have hsub : Small ⊆ primesIn 0 (Real.sqrt n) := by
      intro p hp
      simp only [hSmall, hEx, Finset.mem_filter] at hp
      obtain ⟨⟨hpf, -⟩, hple⟩ := hp
      have hpp := Nat.prime_of_mem_primeFactors hpf
      unfold primesIn
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hpp, by exact_mod_cast hpp.pos⟩
      have : p ≤ ⌊Real.sqrt n⌋₊ := Nat.le_floor hple
      omega
    have hpiu : ((primesIn 0 (Real.sqrt n)).card : ℝ) ≤
        1.25506 * Real.sqrt n / Real.log (Real.sqrt n) := by
      apply hPiU
      nlinarith [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg (n : ℝ)]
    have hlsq : Real.log (Real.sqrt n) = Real.log n / 2 := Real.log_sqrt hnpos.le
    calc (Small.card : ℝ) ≤ ((primesIn 0 (Real.sqrt n)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 1.25506 * Real.sqrt n / (Real.log n / 2) := by rw [← hlsq]; exact hpiu
      _ ≤ 2.52 * Real.sqrt n / Real.log n := by
          rw [div_le_div_iff₀ (by linarith) hlogn]
          nlinarith [Real.sqrt_nonneg (n : ℝ)]
  -- big part: log-weight
  have hbig : (Big.card : ℝ) ≤ 2 * L r s / Real.log n := by
    have hlogq : ∀ q ∈ Big, Real.log n / 2 ≤ Real.log q := by
      intro q hq
      simp only [hBig, hEx, Finset.mem_filter, not_le] at hq
      have hqs : Real.sqrt n ≤ (q : ℝ) := hq.2.le
      have := Real.log_le_log hsq hqs
      rwa [Real.log_sqrt hnpos.le] at this
    have hsub : Big ⊆ (r * s).natAbs.primeFactors := by
      intro q hq
      simp only [hBig, hEx, Finset.mem_filter] at hq
      exact hq.1.1
    have hcount : (Big.card : ℝ) * (Real.log n / 2) ≤ L r s := by
      calc (Big.card : ℝ) * (Real.log n / 2)
          = ∑ _q ∈ Big, (Real.log n / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ q ∈ Big, Real.log q := Finset.sum_le_sum hlogq
        _ ≤ ∑ p ∈ (r * s).natAbs.primeFactors, Real.log p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro p hp _
            exact Real.log_nonneg
              (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
        _ = L r s := (L_eq_sum r s hrs).symm
    rw [le_div_iff₀ hlogn]
    linarith
  have : (Ex.card : ℝ) = (Small.card : ℝ) + (Big.card : ℝ) := by
    exact_mod_cast hsplitc.symm
  rw [this]
  linarith

/-! ## Proposition 6.5 -/

set_option maxHeartbeats 1600000 in
/-- **Proposition 6.5 of the paper, proved.**  Derived from the five analytic
statements — Vinogradov's count form, the Halberstam--Richert sieve bound,
Brun--Titchmarsh, and the two Rosser--Schoenfeld `π`-bounds — taken as
hypotheses, so this theorem uses only Lean's standard axioms. -/
theorem exists_good_prime (hPiU : PiUpperStatement) (hPiL : PiLowerStatement)
    (hBT : BrunTitchmarshStatement) (hVino : VinogradovStatement)
    (hSieve : SieveR2Statement) :
    ∃ (C_star : ℝ) (N_star : ℕ), (4.65 : ℝ) ≤ C_star ∧
      ∀ (r s : ℤ), r * s ≠ 0 → ∀ n : ℕ, N_star ≤ n → C_star * L r s ≤ (n : ℝ) →
        ∃ qt q₁ q₂ q₃ : ℕ, qt.Prime ∧ ¬ (qt ∣ s.natAbs) ∧
          ((n : ℝ) + 2) / 4 < (qt : ℝ) ∧ (qt : ℝ) ≤ (n : ℝ) / 2 ∧
          q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
          ¬ (q₁ ∣ (r * s).natAbs) ∧ ¬ (q₂ ∣ (r * s).natAbs) ∧ ¬ (q₃ ∣ (r * s).natAbs) ∧
          q₁ + q₂ + q₃ + 1 = 2 * qt := by
  obtain ⟨c₁, hc₁, M₀, hvino⟩ := hVino
  obtain ⟨C₂, hC₂, hsieve⟩ := hSieve
  set Cs : ℝ := max 67 (max 4.65 (26880 * C₂ / c₁)) with hCs
  set Ns : ℕ := max (max (810 ^ 8) (2 * M₀ + 2))
      (max (⌈(19660800 / c₁ : ℝ) ^ 2⌉₊ + 1) (⌈(169350 * C₂ / c₁ : ℝ) ^ 2⌉₊ + 1)) with hNs
  refine ⟨Cs, Ns, le_max_of_le_right (le_max_left _ _), ?_⟩
  intro r s hrs n hnN hL
  -- unpack the thresholds
  have hn8 : 810 ^ 8 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
  have hnM : 2 * M₀ + 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
  have hnN1 : ⌈(19660800 / c₁ : ℝ) ^ 2⌉₊ + 1 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
  have hnN2 : ⌈(169350 * C₂ / c₁ : ℝ) ^ 2⌉₊ + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN
  have hn' : ((810 : ℝ)) ^ 8 ≤ (n : ℝ) := by exact_mod_cast hn8
  have hbig : (10 : ℝ) ^ 6 ≤ (n : ℝ) := by nlinarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by nlinarith)
  have hsqn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- `√n` clears both ceiled thresholds
  have hsq1 : 19660800 / c₁ ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) hnpos.le]
    have h1 : ((⌈(19660800 / c₁ : ℝ) ^ 2⌉₊ : ℝ)) ≤ (n : ℝ) := by
      have : (⌈(19660800 / c₁ : ℝ) ^ 2⌉₊ : ℕ) ≤ n := by omega
      exact_mod_cast this
    calc (19660800 / c₁ : ℝ) ^ 2 ≤ (⌈(19660800 / c₁ : ℝ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := h1
  have hsq2 : 169350 * C₂ / c₁ ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) hnpos.le]
    have h1 : ((⌈(169350 * C₂ / c₁ : ℝ) ^ 2⌉₊ : ℝ)) ≤ (n : ℝ) := by
      have : (⌈(169350 * C₂ / c₁ : ℝ) ^ 2⌉₊ : ℕ) ≤ n := by omega
      exact_mod_cast this
    calc (169350 * C₂ / c₁ : ℝ) ^ 2 ≤ (⌈(169350 * C₂ / c₁ : ℝ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := h1
  -- `L ≤ n / Cs`
  have hCs67 : (67 : ℝ) ≤ Cs := le_max_left _ _
  have hCsC2 : 26880 * C₂ / c₁ ≤ Cs := le_max_of_le_right (le_max_right _ _)
  have hCspos : (0 : ℝ) < Cs := by linarith
  have hLnn := L_nonneg r s
  have hLle : L r s ≤ (n : ℝ) / Cs := by
    rw [le_div_iff₀ hCspos]
    calc L r s * Cs = Cs * L r s := by ring
      _ ≤ (n : ℝ) := hL
  -- window facts
  have hWmem : ∀ q ∈ W n, q ∈ primesIn (((n : ℝ) + 2) / 4) ((n : ℝ) / 2) := fun q hq => hq
  have hq2n : ∀ q ∈ W n, 2 * q ≤ n := by
    intro q hq
    have h1 := W_high (by omega) hq
    have h2 : ((2 * q : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hq5 : ∀ q ∈ W n, 5 ≤ q := by
    intro q hq
    have h1 := W_low hq
    have h2 : (5 : ℝ) < (q : ℝ) := by nlinarith
    have : 5 < q := by exact_mod_cast h2
    omega
  -- the excluded sets
  set Ex : Finset ℕ := (r * s).natAbs.primeFactors with hExdef
  set Ex' : Finset ℕ := Ex.filter (fun p => p ≤ n) with hEx'def
  set Badf : ℕ → ℕ := fun q =>
    ((triples (2 * q - 1)).filter
      (fun t => t.1 ∈ Ex ∨ t.2.1 ∈ Ex ∨ t.2.2 ∈ Ex)).card with hBadf
  set T : ℝ := c₁ * ((n : ℝ) / 2) ^ 2 / (Real.log n) ^ 3 with hTdef
  have hT0 : (0 : ℝ) < T := by rw [hTdef]; positivity
  -- STEP A: Vinogradov per window prime
  have hstepA : ∀ q ∈ W n, T ≤ (r₃ (2 * q - 1) : ℝ) := by
    intro q hq
    have h5 := hq5 q hq
    have h2n := hq2n q hq
    have hMcast : ((2 * q - 1 : ℕ) : ℝ) = 2 * (q : ℝ) - 1 := by
      have : 1 ≤ 2 * q := by omega
      push_cast [this]
      ring
    have hMlow : (n : ℝ) / 2 < ((2 * q - 1 : ℕ) : ℝ) := by
      rw [hMcast]
      have := W_low hq
      linarith
    have hMhigh : ((2 * q - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : (2 * q - 1 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hModd : Odd (2 * q - 1) := by
      rw [Nat.odd_iff]
      omega
    have hM₀M : M₀ ≤ 2 * q - 1 := by
      have h1 : ((M₀ : ℝ)) < ((2 * q - 1 : ℕ) : ℝ) := by
        have h2 : ((M₀ : ℝ)) ≤ (n : ℝ) / 2 - 1 := by
          have : ((2 * M₀ + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
          push_cast at this
          linarith
        linarith
      have := (Nat.cast_lt (α := ℝ)).mp h1
      omega
    have hv := hvino (2 * q - 1) hM₀M hModd
    refine le_trans ?_ hv
    -- `T ≤ c₁ M²/log³M`
    have hMpos : (0 : ℝ) < ((2 * q - 1 : ℕ) : ℝ) := by linarith
    have hlMpos : (0 : ℝ) < Real.log ((2 * q - 1 : ℕ) : ℝ) := by
      apply Real.log_pos
      nlinarith
    have hlM : Real.log ((2 * q - 1 : ℕ) : ℝ) ≤ Real.log n :=
      Real.log_le_log hMpos hMhigh
    have hM2 : ((n : ℝ) / 2) ^ 2 ≤ ((2 * q - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hl3 : (Real.log ((2 * q - 1 : ℕ) : ℝ)) ^ 3 ≤ (Real.log n) ^ 3 := by
      exact pow_le_pow_left₀ hlMpos.le hlM 3
    rw [hTdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : ((n : ℝ) / 2) ^ 2 * (Real.log ((2 * q - 1 : ℕ) : ℝ)) ^ 3 ≤
        ((2 * q - 1 : ℕ) : ℝ) ^ 2 * (Real.log ((2 * q - 1 : ℕ) : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_right hM2 (by positivity)
    have k2 : ((2 * q - 1 : ℕ) : ℝ) ^ 2 * (Real.log ((2 * q - 1 : ℕ) : ℝ)) ^ 3 ≤
        ((2 * q - 1 : ℕ) : ℝ) ^ 2 * (Real.log n) ^ 3 :=
      mul_le_mul_of_nonneg_left hl3 (by positivity)
    nlinarith [hc₁.le]
  -- STEP B: the summed sieve bound
  have hstepB : ∑ q ∈ W n, (Badf q : ℝ) ≤
      3 * (Ex'.card : ℝ) * (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3) := by
    have hper_nat : ∀ q ∈ W n, Badf q ≤ 3 * ∑ p ∈ Ex', r₂ (2 * q - 1 - p) := by
      intro q hq
      refine le_trans (card_bad_triples_le (2 * q - 1) Ex) ?_
      have hsub : Ex.filter (fun p => p ≤ 2 * q - 1) ⊆ Ex' := by
        intro p hp
        simp only [hEx'def, Finset.mem_filter] at hp ⊢
        have := hq2n q hq
        exact ⟨hp.1, by omega⟩
      have := Finset.sum_le_sum_of_subset (f := fun p => r₂ (2 * q - 1 - p)) hsub
      omega
    calc ∑ q ∈ W n, (Badf q : ℝ)
        ≤ ∑ q ∈ W n, (3 : ℝ) * ∑ p ∈ Ex', (r₂ (2 * q - 1 - p) : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          have := hper_nat q hq
          have hcast : ((3 * ∑ p ∈ Ex', r₂ (2 * q - 1 - p) : ℕ) : ℝ) =
              3 * ∑ p ∈ Ex', (r₂ (2 * q - 1 - p) : ℝ) := by
            push_cast
            ring
          calc (Badf q : ℝ) ≤ ((3 * ∑ p ∈ Ex', r₂ (2 * q - 1 - p) : ℕ) : ℝ) := by
                exact_mod_cast this
            _ = 3 * ∑ p ∈ Ex', (r₂ (2 * q - 1 - p) : ℝ) := hcast
      _ = 3 * ∑ p ∈ Ex', ∑ q ∈ W n, (r₂ (2 * q - 1 - p) : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 3 * ∑ p ∈ Ex', (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro p hp
          have hpprime : p.Prime := by
            have := Finset.mem_filter.mp hp
            exact Nat.prime_of_mem_primeFactors this.1
          by_cases hp2 : p = 2
          · -- `p = 2`: at most two representations each
            subst hp2
            have h1 : ∑ q ∈ W n, (r₂ (2 * q - 1 - 2) : ℝ) ≤ ∑ _q ∈ W n, (2 : ℝ) := by
              apply Finset.sum_le_sum
              intro q hq
              have h5 := hq5 q hq
              have hodd : Odd (2 * q - 1 - 2) := by
                rw [Nat.odd_iff]
                omega
              have := r₂_le_two_of_odd hodd
              exact_mod_cast this
            rw [Finset.sum_const, nsmul_eq_mul] at h1
            have h2 : (0 : ℝ) ≤ 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3 := by positivity
            calc ∑ q ∈ W n, (r₂ (2 * q - 1 - 2) : ℝ)
                ≤ ((W n).card : ℝ) * 2 := h1
              _ ≤ 2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3 := by
                  linarith
          · -- `p` odd: the sieve, averaged
            have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpprime.odd_of_ne_two hp2)
            set Wp := (W n).filter (fun q => (1 + p) + 4 ≤ 2 * q) with hWp
            have hrw : ∀ q : ℕ, 2 * q - 1 - p = 2 * q - (1 + p) := by
              intro q
              omega
            have hzero : ∀ q ∈ (W n).filter (fun q => ¬ ((1 + p) + 4 ≤ 2 * q)),
                (r₂ (2 * q - 1 - p) : ℝ) = 0 := by
              intro q hq
              simp only [Finset.mem_filter, not_le] at hq
              have : r₂ (2 * q - 1 - p) = 0 := by
                apply r₂_eq_zero_of_lt
                omega
              rw [this]
              norm_num
            have hsplit := Finset.sum_filter_add_sum_filter_not (W n)
              (fun q => (1 + p) + 4 ≤ 2 * q) (fun q => (r₂ (2 * q - 1 - p) : ℝ))
            have hrest : ∑ q ∈ (W n).filter (fun q => ¬ ((1 + p) + 4 ≤ 2 * q)),
                (r₂ (2 * q - 1 - p) : ℝ) = 0 :=
              Finset.sum_eq_zero hzero
            have hWp_bound : ∑ q ∈ Wp, (r₂ (2 * q - 1 - p) : ℝ) ≤
                28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3 := by
              have hperq : ∀ q ∈ Wp, (r₂ (2 * q - 1 - p) : ℝ) ≤
                  C₂ * (4 * (n : ℝ) / (Real.log n) ^ 2) * SingSeries (2 * q - (1 + p)) := by
                intro q hq
                simp only [hWp, Finset.mem_filter] at hq
                obtain ⟨hqW, hqp⟩ := hq
                have hk4 : 4 ≤ 2 * q - (1 + p) := by omega
                have hkn : 2 * q - (1 + p) ≤ n := by
                  have := hq2n q hqW
                  omega
                have hkeven : Even (2 * q - (1 + p)) := by
                  rw [Nat.even_iff]
                  omega
                have hs := hsieve (2 * q - (1 + p)) hkeven hk4
                have hr := ratio_le (2 * q - (1 + p)) n hk4 hkn (by omega)
                have hSnn := singSeries_nonneg (2 * q - (1 + p))
                rw [hrw q]
                calc (r₂ (2 * q - (1 + p)) : ℝ)
                    ≤ C₂ * SingSeries (2 * q - (1 + p)) * (2 * q - (1 + p) : ℕ) /
                        (Real.log (2 * q - (1 + p) : ℕ)) ^ 2 := hs
                  _ = C₂ * SingSeries (2 * q - (1 + p)) *
                        (((2 * q - (1 + p) : ℕ) : ℝ) / (Real.log (2 * q - (1 + p) : ℕ)) ^ 2) := by
                      ring
                  _ ≤ C₂ * SingSeries (2 * q - (1 + p)) * (4 * (n : ℝ) / (Real.log n) ^ 2) := by
                      apply mul_le_mul_of_nonneg_left hr
                      positivity
                  _ = C₂ * (4 * (n : ℝ) / (Real.log n) ^ 2) * SingSeries (2 * q - (1 + p)) := by
                      ring
              have havg := averaging hBT n hn8 (1 + p) Wp
                (fun q hq => hWmem q (Finset.mem_filter.mp hq).1)
                (fun q hq => (Finset.mem_filter.mp hq).2)
              calc ∑ q ∈ Wp, (r₂ (2 * q - 1 - p) : ℝ)
                  ≤ ∑ q ∈ Wp, C₂ * (4 * (n : ℝ) / (Real.log n) ^ 2) *
                      SingSeries (2 * q - (1 + p)) := Finset.sum_le_sum hperq
                _ = C₂ * (4 * (n : ℝ) / (Real.log n) ^ 2) *
                      ∑ q ∈ Wp, SingSeries (2 * q - (1 + p)) := by
                    rw [Finset.mul_sum]
                _ ≤ C₂ * (4 * (n : ℝ) / (Real.log n) ^ 2) * (7 * (n : ℝ) / Real.log n) := by
                    apply mul_le_mul_of_nonneg_left havg
                    positivity
                _ = 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3 := by
                    field_simp
                    ring
            have h2W : (0 : ℝ) ≤ 2 * ((W n).card : ℝ) := by positivity
            calc ∑ q ∈ W n, (r₂ (2 * q - 1 - p) : ℝ)
                = ∑ q ∈ Wp, (r₂ (2 * q - 1 - p) : ℝ) := by
                  rw [← hsplit, hrest, add_zero]
              _ ≤ 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3 := hWp_bound
              _ ≤ 2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3 := by
                  linarith
      _ = 3 * (Ex'.card : ℝ) * (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  -- STEP C: Markov
  set Ebad := (W n).filter (fun q => T / 2 ≤ (Badf q : ℝ)) with hEbad
  have hmarkov := finset_markov (W n) Badf (T / 2)
  have hEbadcard : (Ebad.card : ℝ) ≤
      (2 / T) * (3 * (Ex'.card : ℝ) *
        (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3)) := by
    have h1 : (Ebad.card : ℝ) * (T / 2) ≤
        3 * (Ex'.card : ℝ) * (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3) :=
      le_trans hmarkov hstepB
    have hT2 : (0 : ℝ) < T / 2 := by linarith
    calc (Ebad.card : ℝ) = ((Ebad.card : ℝ) * (T / 2)) / (T / 2) := by
          field_simp
      _ ≤ (3 * (Ex'.card : ℝ) *
            (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3)) / (T / 2) := by
          apply div_le_div_of_nonneg_right h1 hT2.le
      _ = (2 / T) * (3 * (Ex'.card : ℝ) *
            (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3)) := by
          field_simp
  -- STEP D: the numeric budget, in `· log n ≤ c·n` form
  set E1 := (W n).filter (fun q => q ∣ s.natAbs) with hE1def
  have hWlogn : 0.15 * (n : ℝ) ≤ ((W n).card : ℝ) * Real.log n := by
    have := W_card_ge hPiU hPiL n hn8
    rw [div_le_iff₀ hlogn] at this
    linarith
  have hWn : ((W n).card : ℝ) ≤ (n : ℝ) := W_card_le n (by omega)
  -- `E1 · log n ≤ 0.03 n`
  have hE1logn : (E1.card : ℝ) * Real.log n ≤ 0.03 * (n : ℝ) := by
    have h1 := E1_card_le n r s hrs hn8
    rw [hE1def]
    have h2 : (((W n).filter (fun q => q ∣ s.natAbs)).card : ℝ) * Real.log n ≤ 2 * L r s := by
      rw [← le_div_iff₀ hlogn]
      exact h1
    have h3 : 2 * L r s ≤ 2 * ((n : ℝ) / Cs) := by linarith
    have h4 : 2 * ((n : ℝ) / Cs) ≤ 2 * ((n : ℝ) / 67) := by
      have : (n : ℝ) / Cs ≤ (n : ℝ) / 67 :=
        div_le_div_of_nonneg_left hnpos.le (by norm_num) hCs67
      linarith
    have h5 : 2 * ((n : ℝ) / 67) ≤ 0.03 * (n : ℝ) := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 67)]
      nlinarith
    linarith
  -- `Ex' · log n ≤ 2.52 √n + 2L`, kept in `L`-form for piece B
  have hEx'L : (Ex'.card : ℝ) * Real.log n ≤ 2.52 * Real.sqrt n + 2 * L r s := by
    have h3 : (Ex'.card : ℝ) ≤
        2.52 * Real.sqrt n / Real.log n + 2 * L r s / Real.log n :=
      omega_card_le hPiU n r s hrs hn8
    have h4 := mul_le_mul_of_nonneg_right h3 hlogn.le
    calc (Ex'.card : ℝ) * Real.log n
        ≤ (2.52 * Real.sqrt n / Real.log n + 2 * L r s / Real.log n) * Real.log n := h4
      _ = 2.52 * Real.sqrt n + 2 * L r s := by field_simp
  have h2L : 2 * L r s ≤ 0.03 * (n : ℝ) := by
    have h4 : 2 * L r s ≤ 2 * ((n : ℝ) / Cs) := by linarith
    have h5 : (n : ℝ) / Cs ≤ (n : ℝ) / 67 :=
      div_le_div_of_nonneg_left hnpos.le (by norm_num) hCs67
    have h6 : 2 * ((n : ℝ) / 67) ≤ 0.03 * (n : ℝ) := by
      rw [mul_div_assoc', div_le_iff₀ (by norm_num : (0:ℝ) < 67)]
      nlinarith
    linarith
  have hsqn_le : Real.sqrt n ≤ (n : ℝ) := by
    have h1 : Real.sqrt n ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq hnpos.le] at h1
  have hEx'X : (Ex'.card : ℝ) * Real.log n ≤ 2.55 * (n : ℝ) := by
    nlinarith [hEx'L, h2L, hsqn_le]
  -- `log³ n ≤ 512 √n`
  have hlog3 : (Real.log n) ^ 3 ≤ 512 * Real.sqrt n := by
    have ht := log_le_eight_sqrt3 (show (1 : ℝ) ≤ (n : ℝ) by linarith)
    set t := Real.sqrt (Real.sqrt (Real.sqrt n)) with htdef
    have ht1 : (1 : ℝ) ≤ t := by
      rw [htdef]
      exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (by linarith)))
    have ht2 : t ^ 2 = Real.sqrt (Real.sqrt n) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have ht4 : t ^ 4 = Real.sqrt n := by
      have h1 : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [h1, ht2]
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have h1 : (Real.log n) ^ 3 ≤ (8 * t) ^ 3 := pow_le_pow_left₀ hlogn.le ht 3
    have h3 : t ^ 3 ≤ t ^ 4 := by nlinarith
    nlinarith [ht4]
  -- `c₁ √n` and `c₁ Cs` clear the numeric thresholds
  have hc1sq1 : (19660800 : ℝ) ≤ c₁ * Real.sqrt n := by
    have h := mul_le_mul_of_nonneg_left hsq1 hc₁.le
    calc (19660800 : ℝ) = c₁ * (19660800 / c₁) := by field_simp
      _ ≤ c₁ * Real.sqrt n := h
  have hc1sq2 : 169350 * C₂ ≤ c₁ * Real.sqrt n := by
    have h := mul_le_mul_of_nonneg_left hsq2 hc₁.le
    calc 169350 * C₂ = c₁ * (169350 * C₂ / c₁) := by field_simp
      _ ≤ c₁ * Real.sqrt n := h
  have hc1Cs : 26880 * C₂ ≤ c₁ * Cs := by
    have h := mul_le_mul_of_nonneg_left hCsC2 hc₁.le
    calc 26880 * C₂ = c₁ * (26880 * C₂ / c₁) := by field_simp
      _ ≤ c₁ * Cs := h
  have hnn : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  have hss : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnn
  -- piece A: `48 Ex' W log⁴ ≤ 0.01 c₁ n³`
  have hA : 48 * (Ex'.card : ℝ) * ((W n).card : ℝ) * (Real.log n) ^ 4 ≤
      0.01 * c₁ * (n : ℝ) ^ 3 := by
    have m1 : ((W n).card : ℝ) * (Real.log n) ^ 3 ≤ (n : ℝ) * (512 * Real.sqrt n) :=
      mul_le_mul hWn hlog3 (by positivity) hnn
    have m2 : ((Ex'.card : ℝ) * Real.log n) * (((W n).card : ℝ) * (Real.log n) ^ 3) ≤
        (2.55 * (n : ℝ)) * ((n : ℝ) * (512 * Real.sqrt n)) :=
      mul_le_mul hEx'X m1 (by positivity) (by nlinarith)
    have meq : 48 * (Ex'.card : ℝ) * ((W n).card : ℝ) * (Real.log n) ^ 4 =
        48 * (((Ex'.card : ℝ) * Real.log n) * (((W n).card : ℝ) * (Real.log n) ^ 3)) := by
      ring
    rw [meq]
    have m3 : 48 * ((2.55 * (n : ℝ)) * ((n : ℝ) * (512 * Real.sqrt n))) ≤
        0.01 * c₁ * (n : ℝ) ^ 3 := by
      have expand : 0.01 * c₁ * (n : ℝ) ^ 3 =
          0.01 * (c₁ * Real.sqrt n) * ((n : ℝ) * (n : ℝ) * Real.sqrt n) := by
        have h1 : (n : ℝ) ^ 3 = (n : ℝ) * (n : ℝ) * (Real.sqrt n * Real.sqrt n) := by
          rw [hss]; ring
        rw [h1]; ring
      rw [expand]
      have hfac : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) * Real.sqrt n := by positivity
      nlinarith [hc1sq1, hfac]
    nlinarith [m2, m3]
  -- piece B: `672 C₂ Ex' n² log ≤ 0.06 c₁ n³`
  have hB : 672 * C₂ * (Ex'.card : ℝ) * (n : ℝ) ^ 2 * Real.log n ≤
      0.06 * c₁ * (n : ℝ) ^ 3 := by
    have hpart1 : 672 * C₂ * (2.52 * Real.sqrt n) ≤ 0.01 * c₁ * (n : ℝ) := by
      have expand : 0.01 * c₁ * (n : ℝ) = 0.01 * (c₁ * Real.sqrt n) * Real.sqrt n := by
        calc 0.01 * c₁ * (n : ℝ) = 0.01 * (c₁ * (Real.sqrt n * Real.sqrt n)) := by
              rw [hss]; ring
          _ = 0.01 * (c₁ * Real.sqrt n) * Real.sqrt n := by ring
      rw [expand]
      have k : 169350 * C₂ * (0.01 * Real.sqrt n) ≤
          (c₁ * Real.sqrt n) * (0.01 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right hc1sq2 (by positivity)
      nlinarith [k, mul_nonneg hC₂.le (Real.sqrt_nonneg (n : ℝ))]
    have hpart2 : 672 * C₂ * (2 * L r s) ≤ 0.05 * c₁ * (n : ℝ) := by
      have k1 : 672 * C₂ * (2 * L r s) ≤ 672 * C₂ * (2 * ((n : ℝ) / Cs)) := by
        have : 2 * L r s ≤ 2 * ((n : ℝ) / Cs) := by linarith
        apply mul_le_mul_of_nonneg_left this (by positivity)
      have k2 : 672 * C₂ * (2 * ((n : ℝ) / Cs)) ≤ 0.05 * c₁ * (n : ℝ) := by
        rw [show 672 * C₂ * (2 * ((n : ℝ) / Cs)) = (1344 * C₂ * (n : ℝ)) / Cs by ring,
          div_le_iff₀ hCspos]
        nlinarith [hc1Cs, hnn]
      linarith
    calc 672 * C₂ * (Ex'.card : ℝ) * (n : ℝ) ^ 2 * Real.log n
        = (672 * C₂ * ((Ex'.card : ℝ) * Real.log n)) * (n : ℝ) ^ 2 := by ring
      _ ≤ (672 * C₂ * (2.52 * Real.sqrt n + 2 * L r s)) * (n : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hEx'L (by positivity)
      _ = (672 * C₂ * (2.52 * Real.sqrt n) + 672 * C₂ * (2 * L r s)) * (n : ℝ) ^ 2 := by
          ring
      _ ≤ (0.01 * c₁ * (n : ℝ) + 0.05 * c₁ * (n : ℝ)) * (n : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right (add_le_add hpart1 hpart2) (by positivity)
      _ = 0.06 * c₁ * (n : ℝ) ^ 3 := by ring
  -- connect `Ebad` to pieces A and B
  have hc0 : c₁ ≠ 0 := hc₁.ne'
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hl0 : Real.log n ≠ 0 := hlogn.ne'
  have hTinv : 2 / T = 8 * (Real.log n) ^ 3 / (c₁ * (n : ℝ) ^ 2) := by
    rw [hTdef]
    field_simp
    ring
  have hkeyEq : (2 / T) * (3 * (Ex'.card : ℝ) *
      (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3)) *
      (Real.log n * (c₁ * (n : ℝ) ^ 2)) =
      48 * (Ex'.card : ℝ) * ((W n).card : ℝ) * (Real.log n) ^ 4 +
        672 * C₂ * (Ex'.card : ℝ) * (n : ℝ) ^ 2 * Real.log n := by
    rw [hTinv]
    field_simp
    ring
  have hEbadLogn : (Ebad.card : ℝ) * Real.log n ≤ 0.07 * (n : ℝ) := by
    have h0 : (0 : ℝ) < c₁ * (n : ℝ) ^ 2 := by positivity
    have h1 : (Ebad.card : ℝ) * (Real.log n * (c₁ * (n : ℝ) ^ 2)) ≤
        (2 / T) * (3 * (Ex'.card : ℝ) *
          (2 * ((W n).card : ℝ) + 28 * C₂ * (n : ℝ) ^ 2 / (Real.log n) ^ 3)) *
          (Real.log n * (c₁ * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hEbadcard (by positivity)
    rw [hkeyEq] at h1
    have h2 : (Ebad.card : ℝ) * (Real.log n * (c₁ * (n : ℝ) ^ 2)) ≤
        0.07 * c₁ * (n : ℝ) ^ 3 := by
      have := add_le_add hA hB
      linarith
    have h3 : (Ebad.card : ℝ) * Real.log n * (c₁ * (n : ℝ) ^ 2) ≤
        (0.07 * (n : ℝ)) * (c₁ * (n : ℝ) ^ 2) := by
      calc (Ebad.card : ℝ) * Real.log n * (c₁ * (n : ℝ) ^ 2)
          = (Ebad.card : ℝ) * (Real.log n * (c₁ * (n : ℝ) ^ 2)) := by ring
        _ ≤ 0.07 * c₁ * (n : ℝ) ^ 3 := h2
        _ = (0.07 * (n : ℝ)) * (c₁ * (n : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_right h3 h0
  -- the strict comparison
  have hstrict : (E1.card : ℝ) + (Ebad.card : ℝ) < ((W n).card : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((W n).card : ℝ) * Real.log n ≤
        ((E1.card : ℝ) + (Ebad.card : ℝ)) * Real.log n :=
      mul_le_mul_of_nonneg_right hcon hlogn.le
    nlinarith [hWlogn, hE1logn, hEbadLogn, hnpos]
  -- STEP E: extract the good prime
  have hgood : ((W n) \ (E1 ∪ Ebad)).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcon
    push_neg at hcon
    have h0 : ((W n) \ (E1 ∪ Ebad)).card = 0 := by omega
    have h1 : (W n).card ≤ (E1 ∪ Ebad).card := by
      have := Finset.le_card_sdiff (E1 ∪ Ebad) (W n)
      omega
    have h2 : (E1 ∪ Ebad).card ≤ E1.card + Ebad.card := Finset.card_union_le _ _
    have h3 : ((W n).card : ℝ) ≤ (E1.card : ℝ) + (Ebad.card : ℝ) := by
      exact_mod_cast le_trans h1 h2
    linarith
  obtain ⟨qt, hqt⟩ := hgood
  rw [Finset.mem_sdiff, Finset.mem_union] at hqt
  obtain ⟨hqtW, hqtn⟩ := hqt
  push_neg at hqtn
  obtain ⟨hqtE1, hqtEbad⟩ := hqtn
  have hqtdvd : ¬ (qt ∣ s.natAbs) := by
    intro hd
    exact hqtE1 (by rw [hE1def]; exact Finset.mem_filter.mpr ⟨hqtW, hd⟩)
  have hbadlt : (Badf qt : ℝ) < T / 2 := by
    by_contra hcon
    push_neg at hcon
    exact hqtEbad (by rw [hEbad]; exact Finset.mem_filter.mpr ⟨hqtW, hcon⟩)
  have hr3T := hstepA qt hqtW
  have hcompl : Badf qt +
      ((triples (2 * qt - 1)).filter
        (fun t => ¬ (t.1 ∈ Ex ∨ t.2.1 ∈ Ex ∨ t.2.2 ∈ Ex))).card = r₃ (2 * qt - 1) := by
    rw [hBadf]
    exact Finset.card_filter_add_card_filter_not _
  have hcleanpos : 0 < ((triples (2 * qt - 1)).filter
      (fun t => ¬ (t.1 ∈ Ex ∨ t.2.1 ∈ Ex ∨ t.2.2 ∈ Ex))).card := by
    by_contra hcon
    have h0 : ((triples (2 * qt - 1)).filter
        (fun t => ¬ (t.1 ∈ Ex ∨ t.2.1 ∈ Ex ∨ t.2.2 ∈ Ex))).card = 0 :=
      Nat.le_zero.mp (Nat.not_lt.mp hcon)
    have h1 : r₃ (2 * qt - 1) = Badf qt := by
      have h1' := hcompl
      rw [h0, Nat.add_zero] at h1'
      exact h1'.symm
    have h2 : (r₃ (2 * qt - 1) : ℝ) = (Badf qt : ℝ) := by exact_mod_cast h1
    linarith [hr3T, hbadlt, hT0]
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hcleanpos
  rw [Finset.mem_filter] at ht
  obtain ⟨htM, htclean⟩ := ht
  push_neg at htclean
  obtain ⟨hcl1, hcl2, hcl3⟩ := htclean
  obtain ⟨-, -, -, hp1, hp2, hp3, hsum⟩ := mem_triples.mp htM
  have h5 := hq5 qt hqtW
  refine ⟨qt, t.1, t.2.1, t.2.2, W_prime hqtW, hqtdvd, W_low hqtW,
    W_high (by omega) hqtW, hp1, hp2, hp3, ?_, ?_, ?_, ?_⟩
  · intro hd
    exact hcl1 (Nat.mem_primeFactors.mpr ⟨hp1, hd, Int.natAbs_ne_zero.mpr hrs⟩)
  · intro hd
    exact hcl2 (Nat.mem_primeFactors.mpr ⟨hp2, hd, Int.natAbs_ne_zero.mpr hrs⟩)
  · intro hd
    exact hcl3 (Nat.mem_primeFactors.mpr ⟨hp3, hd, Int.natAbs_ne_zero.mpr hrs⟩)
  · omega

end UniversalWords
