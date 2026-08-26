/-
Formalization of §2 of "The universality of words `x^r y^s` in symmetric groups".

This file is self-contained mathematics: everything here is *proved* from Mathlib,
with no axioms beyond Mathlib's own.  It sets up the three invariants of a
permutation used throughout the paper --- moved points, non-trivial cycles, and
their difference `δ` --- and proves the two structural facts the case division
rests on (Lemma 2.1), together with the root lemma (Lemma 2.2) in the form
actually used: a permutation whose order is coprime to `t` is a `t`-th power.
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The invariants `md`, `cy`, `δ` -/

/-- `md σ` is the number of points moved by `σ` (written `m(σ)` in the paper). -/
def md (σ : Perm α) : ℕ := σ.support.card

/-- `cy σ` is the number of non-trivial cycles of `σ` (written `c(σ)`). -/
def cy (σ : Perm α) : ℕ := Multiset.card σ.cycleType

/-- `δ σ = md σ - cy σ`.  Truncated subtraction is harmless: `cy_le_md` below. -/
def delta (σ : Perm α) : ℕ := md σ - cy σ

lemma md_eq_sum (σ : Perm α) : md σ = σ.cycleType.sum := (sum_cycleType σ).symm

/-- Lemma 2.1(2): every non-trivial cycle moves at least two points. -/
lemma two_mul_cy_le_md (σ : Perm α) : 2 * cy σ ≤ md σ := by
  have h : ∀ x ∈ σ.cycleType, 2 ≤ x := fun _ hx => two_le_of_mem_cycleType hx
  have := Multiset.card_nsmul_le_sum h
  simpa [md_eq_sum, cy, smul_eq_mul, Nat.mul_comm] using this

lemma cy_le_md (σ : Perm α) : cy σ ≤ md σ :=
  le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) (two_mul_cy_le_md σ)

lemma md_eq_delta_add_cy (σ : Perm α) : md σ = delta σ + cy σ :=
  (Nat.sub_add_cancel (cy_le_md σ)).symm

/-- Lemma 2.1(2), the form used for the case division: `δ ≥ md/2`. -/
lemma md_le_two_mul_delta (σ : Perm α) : md σ ≤ 2 * delta σ := by
  have h := two_mul_cy_le_md σ
  have e := md_eq_delta_add_cy σ
  omega

/-- Lemma 2.1(1): `sgn σ = (-1) ^ δ(σ)`. -/
lemma sign_eq_neg_one_pow_delta (σ : Perm α) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ delta σ := by
  have hsum : σ.cycleType.sum = delta σ + cy σ := by
    rw [← md_eq_sum]; exact md_eq_delta_add_cy σ
  have := sign_of_cycleType σ
  rw [this, hsum]
  have : delta σ + cy σ + Multiset.card σ.cycleType = delta σ + 2 * cy σ := by
    simp [cy]; ring
  rw [this, pow_add, pow_mul]
  simp

/-- An odd permutation has odd `δ`, and conversely (Lemma 2.1(1)). -/
lemma odd_delta_iff (σ : Perm α) :
    Odd (delta σ) ↔ Equiv.Perm.sign σ = -1 := by
  rw [sign_eq_neg_one_pow_delta]
  constructor
  · rintro ⟨k, hk⟩; rw [hk]; simp [pow_succ, pow_mul]
  · intro h
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨k, hk⟩ := hodd
    rw [hk] at h
    have : ((-1 : ℤˣ) ^ (k + k)) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this] at h
    exact absurd h (by decide)

/-- `δ σ = 0` exactly for the identity. -/
lemma delta_eq_zero_iff (σ : Perm α) : delta σ = 0 ↔ σ = 1 := by
  constructor
  · intro h
    have h2 := md_le_two_mul_delta σ
    rw [h] at h2
    have : σ.support.card = 0 := Nat.le_zero.mp (by simpa [md] using h2)
    simpa using Finset.card_eq_zero.mp this
  · rintro rfl; simp [delta, md, cy]

/-! ## The root lemma (Lemma 2.2) -/

/-- Lemma 2.2, group-theoretic form: if `orderOf σ` is coprime to `t` then `σ` is a
`t`-th power.  The paper phrases this for a product of disjoint cycles of lengths
coprime to `t`; that hypothesis gives exactly this one, via `coprime_orderOf`. -/
theorem exists_zpow_eq_of_coprime {G : Type*} [Group G] {σ : G} {t : ℤ}
    (h : Nat.Coprime (orderOf σ) t.natAbs) : ∃ x : G, x ^ t = σ := by
  set N : ℕ := orderOf σ with hN
  -- Bézout: `1 = t * a + N * b`, so `a * t ≡ 1 [ZMOD N]`.
  have hgcd : Int.gcd t (N : ℤ) = 1 := by
    simpa [Int.gcd, Int.natAbs_natCast, Nat.coprime_comm] using h
  have hbez : (1 : ℤ) = t * Int.gcdA t (N : ℤ) + (N : ℤ) * Int.gcdB t (N : ℤ) := by
    have := Int.gcd_eq_gcd_ab t (N : ℤ)
    rw [hgcd] at this
    exact_mod_cast this
  refine ⟨σ ^ Int.gcdA t (N : ℤ), ?_⟩
  rw [← zpow_mul]
  have hmod : Int.gcdA t (N : ℤ) * t ≡ 1 [ZMOD (N : ℤ)] := by
    have : Int.gcdA t (N : ℤ) * t - 1 = -((N : ℤ) * Int.gcdB t (N : ℤ)) := by linarith [hbez]
    have hdvd : (N : ℤ) ∣ (Int.gcdA t (N : ℤ) * t - 1) := ⟨-Int.gcdB t (N : ℤ), by linarith [hbez]⟩
    exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using hdvd))
  calc σ ^ (Int.gcdA t (N : ℤ) * t) = σ ^ (1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq]; exact hmod
    _ = σ := by simp

/-- `lcm a b` is coprime to `t` when both `a` and `b` are. -/
lemma coprime_lcm_of_coprime {a b t : ℕ} (ha : Nat.Coprime a t) (hb : Nat.Coprime b t) :
    Nat.Coprime (Nat.lcm a b) t :=
  Nat.Coprime.coprime_dvd_left
    (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)) (ha.mul_left hb)

/-- The lcm of a multiset of naturals each coprime to `t` is coprime to `t`. -/
lemma coprime_multiset_lcm {t : ℕ} :
    ∀ {s : Multiset ℕ}, (∀ l ∈ s, Nat.Coprime l t) → Nat.Coprime (Multiset.lcm s) t := by
  intro s
  induction s using Multiset.induction with
  | empty => intro _; simp [Nat.Coprime]
  | cons a s ih =>
      intro h
      rw [Multiset.lcm_cons]
      exact coprime_lcm_of_coprime (h a (Multiset.mem_cons_self a s))
        (ih fun l hl => h l (Multiset.mem_cons_of_mem hl))

/-- All cycle lengths coprime to `t` implies the order is coprime to `t`. -/
lemma coprime_orderOf_of_cycleType {σ : Perm α} {t : ℕ}
    (h : ∀ l ∈ σ.cycleType, Nat.Coprime l t) : Nat.Coprime (orderOf σ) t := by
  rw [← lcm_cycleType]; exact coprime_multiset_lcm h

/-- A cycle of length coprime to `t` is a `t`-th power. -/
lemma IsCycle.exists_zpow_eq {σ : Perm α} {t : ℤ} (hc : σ.IsCycle)
    (h : Nat.Coprime (md σ) t.natAbs) : ∃ x : Perm α, x ^ t = σ :=
  exists_zpow_eq_of_coprime (by rwa [hc.orderOf])

/-! ## The core reduction: a factorization with coprime orders yields the word -/

/-- Everything the three constructions of §§4--6 have to supply.  Once a target `z`
is written as `A * B` with `orderOf A` coprime to `r` and `orderOf B` coprime to
`s`, the word `x^r y^s` attains `z`. -/
theorem word_of_factorization {G : Type*} [Group G] {z A B : G} (hz : z = A * B)
    {r s : ℤ} (hA : Nat.Coprime (orderOf A) r.natAbs)
    (hB : Nat.Coprime (orderOf B) s.natAbs) :
    ∃ x y : G, x ^ r * y ^ s = z := by
  obtain ⟨x, hx⟩ := exists_zpow_eq_of_coprime hA
  obtain ⟨y, hy⟩ := exists_zpow_eq_of_coprime hB
  exact ⟨x, y, by rw [hx, hy, hz]⟩

/-! ## The arithmetic of the exponents -/

/-- `m(r,s)`: the product of the distinct primes dividing `rs` (so `m = 1` when
`rs = ±1`).  This is the paper's `m(r,s)`, and matches the encoding audited
against the Kourovka register. -/
def mrs (r s : ℤ) : ℕ := (r * s).natAbs.primeFactors.prod id

/-- `L = log m(r,s)`, the total logarithmic mass of the primes dividing `rs`. -/
noncomputable def L (r s : ℤ) : ℝ := Real.log (mrs r s)

/-- The primes in the half-open window `(a, b]`. -/
noncomputable def primesIn (a b : ℝ) : Finset ℕ :=
  (Finset.range (⌊b⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ a < (p : ℝ))

lemma prime_of_mem_primesIn {a b : ℝ} {p : ℕ} (h : p ∈ primesIn a b) : p.Prime := by
  simp only [primesIn, Finset.mem_filter] at h; exact h.2.1

lemma lt_of_mem_primesIn {a b : ℝ} {p : ℕ} (h : p ∈ primesIn a b) : a < (p : ℝ) := by
  simp only [primesIn, Finset.mem_filter] at h; exact h.2.2

lemma le_of_mem_primesIn {a b : ℝ} {p : ℕ} (hb : 0 ≤ b) (h : p ∈ primesIn a b) :
    (p : ℝ) ≤ b := by
  simp only [primesIn, Finset.mem_filter, Finset.mem_range] at h
  have : p ≤ ⌊b⌋₊ := Nat.lt_succ_iff.mp h.1
  calc (p : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast this
    _ ≤ b := Nat.floor_le hb

/-- `L r s` is the total log-mass of the primes dividing `rs`. -/
lemma L_eq_sum (r s : ℤ) (_h : (r * s) ≠ 0) :
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


end UniversalWords
