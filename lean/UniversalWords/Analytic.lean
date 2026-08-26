/-
The analytic inputs to Proposition 6.5, as named statements.

This file **states** five published theorems as propositions; it assumes
nothing.  Proposition 6.5 (`exists_good_prime`) is proved in `GoodPrime.lean`
from these statements taken as hypotheses, so it — and the conditional main
theorem — use only Lean's standard axioms.  `Unconditional.lean` separately
assumes these statements as axioms to recover unconditional forms.

Sources:
* `pi_upper`, `pi_lower` --- J. B. Rosser, L. Schoenfeld, *Approximate formulas
  for some functions of prime numbers*, Illinois J. Math. **6** (1962), 64--94,
  eqs. (3.6) and (3.5): `π(x) < 1.25506 x/log x` for `x > 1`, and
  `π(x) > x/log x` for `x ≥ 17`.
* `brun_titchmarsh` --- H. L. Montgomery, R. C. Vaughan, *The large sieve*,
  Mathematika **20** (1973), 119--134, Theorem 2:
  `π(x; d, a) < 2x/(φ(d) log(x/d))` for `x > d` and `gcd(a, d) = 1`.
* `vinogradov` --- I. M. Vinogradov, *Representation of an odd number as a sum of
  three primes*, C. R. (Dokl.) Acad. Sci. URSS **15** (1937), 169--172; the count
  form with an ineffective threshold is classical (see R. C. Vaughan, *The
  Hardy--Littlewood Method*, 2nd ed., Theorem 3.4): the number of ordered
  representations of an odd `M` as a sum of three primes is `≫ M²/log³M`.
* `sieve_r2` --- H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press,
  1974, Theorem 3.11: the number of ordered representations of an even `k` as a
  sum of two primes is `≤ C₂ · S(k) · k/log²k` for an absolute `C₂`, where
  `S(k) = ∏_{p ∣ k, p > 2} (p-1)/(p-2)` (the constant absorbs the twin-prime
  constant and the `1 + o(1)`).
-/
import UniversalWords.Basic

namespace UniversalWords

open scoped Classical

/-! ## Counting functions -/

/-- The set of ordered prime pairs summing to `k`. -/
def pairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
    (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = k)

/-- The set of ordered prime triples summing to `M`. -/
def triples (M : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = M)

/-- Ordered representations of `k` as a sum of two primes. -/
def r₂ (k : ℕ) : ℕ := (pairs k).card

/-- Ordered representations of `M` as a sum of three primes. -/
def r₃ (M : ℕ) : ℕ := (triples M).card

/-- The singular series `S(k) = ∏_{p ∣ k, p > 2} (p-1)/(p-2)` of the sieve bound. -/
noncomputable def SingSeries (k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-! ## The five statements -/

/-- **Rosser--Schoenfeld (3.6)**: `π(x) < 1.25506 x/log x` for `x > 1`. -/
def PiUpperStatement : Prop :=
  ∀ (x : ℝ), 1 < x → ((primesIn 0 x).card : ℝ) ≤ 1.25506 * x / Real.log x

/-- **Rosser--Schoenfeld (3.5)**: `π(x) > x/log x` for `x ≥ 17`. -/
def PiLowerStatement : Prop :=
  ∀ (x : ℝ), 17 ≤ x → x / Real.log x ≤ ((primesIn 0 x).card : ℝ)

/-- **Montgomery--Vaughan (Brun--Titchmarsh)**: primes `≤ x` in a reduced residue
class `a` mod `d` number at most `2x/(φ(d) log(x/d))`, for `x > d`. -/
def BrunTitchmarshStatement : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (a : ZMod d), IsUnit a → ∀ (x : ℝ), (d : ℝ) < x →
    (((primesIn 0 x).filter (fun p : ℕ => (Nat.cast p : ZMod d) = a)).card : ℝ) ≤
      2 * x / ((Nat.totient d : ℝ) * Real.log (x / d))

/-- **Vinogradov's three-primes theorem**, count form: for odd `M` beyond an
ineffective threshold, `r₃(M) ≥ c₁ M²/log³M` for an absolute `c₁ > 0`. -/
def VinogradovStatement : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → Odd M →
    c₁ * (M : ℝ) ^ 2 / (Real.log M) ^ 3 ≤ (r₃ M : ℝ)

/-- **Halberstam--Richert Theorem 3.11** (upper-bound sieve for Goldbach counts):
for even `k ≥ 4`, `r₂(k) ≤ C₂ · S(k) · k/log²k` for an absolute `C₂`. -/
def SieveR2Statement : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ k : ℕ, Even k → 4 ≤ k →
    (r₂ k : ℝ) ≤ C₂ * SingSeries k * k / (Real.log k) ^ 2

end UniversalWords
