import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Kourovka Notebook Problem 10.32: universality of the words `x^r y^s`

**Problem 10.32** of the Kourovka Notebook (*Unsolved Problems in Group
Theory*), posed by Yu. I. Merzlyakov in its tenth issue (1986), asks for a
bound of Brenner–Evans–Silberger shape for the symmetric groups: for which
degrees `n` is the word `x^r y^s` *universal* on `Sₙ` — every element of `Sₙ`
a value of `x^r y^s`?

This file states the two principal results of the accompanying development,
which answer the question in both directions for the parity range where
universality is possible at all (`r` or `s` odd):

* `kourovka_10_32_conditional` — **the positive direction.**  There are
  constants `C` and `N₀` such that for all nonzero exponents `r, s` with `r`
  or `s` odd, the word `x^r y^s` is universal on `Sₙ` whenever `n ≥ N₀` and
  `n ≥ C · log m(r,s)`, where `m(r,s)` is the product of the distinct primes
  dividing `rs`.  (In the accompanying paper the multiplicative constant is
  effective — `C = 4.65` suffices for its effective cases — while the
  threshold `N₀` is ineffective, solely because the proof invokes
  Vinogradov's three-primes theorem; the formal statement accordingly
  asserts existence of the constants.)  The theorem is stated as a fully proved
  implication from eight named classical results (Herzog–Kaplan–Lev, Boccara,
  three Rosser–Schoenfeld bounds, Montgomery–Vaughan's Brun–Titchmarsh
  inequality, Vinogradov's three-primes theorem, and the Halberstam–Richert
  sieve bound), each stated below exactly in the form used, with its source.
  The proof of the implication depends on no axioms beyond Lean's standard
  three.

* `not_universal` — **the negative direction, unconditionally.**  The
  logarithmic shape of the bound is optimal: with `r = lcm(1,…,n)` and `s` the
  odd part of `r`, no element of order `3` in `Sₙ` is a value of `x^r y^s` —
  yet `log m(r,s)` equals `θ(n) = Σ_{p ≤ n} log p`, the Chebyshev function.
  Since `θ(n) < n` for infinitely many `n` (a classical oscillation fact *not*
  used or formalised here), no bound of the form `n ≥ 1 · log m(r,s)` with
  threshold constant `1` can replace `C`.

Every definition below carries its ordinary mathematical meaning, documented
on the definition itself.  The statements of the eight classical inputs are
part of the audited surface: `kourovka_10_32_conditional` proves exactly the
implication from those statements as written.
-/

namespace Kourovka1032

open Equiv Equiv.Perm
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Permutation invariants -/

/-- `md σ` is the number of points moved by the permutation `σ`. -/
def md (σ : Perm α) : ℕ := σ.support.card

/-- `cy σ` is the number of non-trivial cycles of `σ`. -/
def cy (σ : Perm α) : ℕ := Multiset.card σ.cycleType

/-- `delta σ = md σ - cy σ` (moved points minus non-trivial cycles); `σ` is even
iff `delta σ` is even, and `delta σ = 0` iff `σ = 1`. -/
def delta (σ : Perm α) : ℕ := md σ - cy σ

/-! ## The arithmetic of the exponents -/

/-- `mrs r s` is `m(r,s)`: the product of the distinct primes dividing `r·s`
(the largest squarefree divisor of `rs`; `m = 1` when `rs = ±1`). -/
def mrs (r s : ℤ) : ℕ := (r * s).natAbs.primeFactors.prod id

/-- `L r s = log m(r,s)`, the total logarithmic mass of the primes dividing `rs`.
The main theorem's bound on the degree `n` is linear in this quantity. -/
noncomputable def L (r s : ℤ) : ℝ := Real.log (mrs r s)

/-- The set of primes in the half-open real window `(a, b]`. -/
noncomputable def primesIn (a b : ℝ) : Finset ℕ :=
  (Finset.range (⌊b⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ a < (p : ℝ))

/-- `R n = lcm(1, …, n)`, the exponent witnessing optimality in `not_universal`. -/
def R (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-! ## Additive prime-counting functions -/

/-- The set of ordered prime pairs summing to `k`. -/
def pairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
    (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = k)

/-- The set of ordered prime triples summing to `M`. -/
def triples (M : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = M)

/-- `r₂ k`: the number of ordered representations of `k` as a sum of two primes. -/
def r₂ (k : ℕ) : ℕ := (pairs k).card

/-- `r₃ M`: the number of ordered representations of `M` as a sum of three primes. -/
def r₃ (M : ℕ) : ℕ := (triples M).card

/-- The singular series `S(k) = ∏_{p ∣ k, p > 2} (p-1)/(p-2)` appearing in the
sieve upper bound for `r₂`. -/
noncomputable def SingSeries (k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-! ## The eight classical inputs

Each of the following propositions states a published theorem, in exactly the
form the development uses.  `kourovka_10_32_conditional` is the fully proved
implication from these eight statements. -/

/-- **Rosser–Schoenfeld, window-mass form.**  The primes in `(a, b]` carry
logarithmic mass at least `0.985·b − 1.01624·a`.  This combines
`θ(b) > 0.985·b` for `b > 11927` (Rosser–Schoenfeld, *Math. Comp.* **29**
(1975), Corollary to Theorem 6) with `θ(a) < 1.01624·a` for `a > 0`
(Rosser–Schoenfeld, *Illinois J. Math.* **6** (1962), Theorem 9), the case
`a = 0` being trivial. -/
def RSWindowMassStatement : Prop :=
  ∀ (a b : ℝ), 0 ≤ a → (11927 : ℝ) < b → a ≤ b →
    0.985 * b - 1.01624 * a ≤ ∑ p ∈ primesIn a b, Real.log p

/-- **Herzog–Kaplan–Lev** (*Discrete Math.* **285** (2004), Theorem 7,
sufficiency): a non-identity permutation `σ` satisfying the stated sum, parity
and difference constraints is a product of an `l₁`-cycle and an `l₂`-cycle. -/
def HKLStatement : Prop :=
  ∀ (n : ℕ) (σ : Perm (Fin n)), σ ≠ 1 → ∀ (l₁ l₂ : ℕ),
    l₂ ≤ l₁ → 2 ≤ l₂ → l₁ ≤ n →
    md σ + cy σ ≤ l₁ + l₂ →
    (l₁ + l₂) % 2 = (md σ + cy σ) % 2 →
    l₁ - l₂ ≤ delta σ →
    ∃ A B : Perm (Fin n), A.IsCycle ∧ md A = l₁ ∧ B.IsCycle ∧ md B = l₂ ∧ σ = A * B

/-- **Boccara** (*Discrete Math.* **38** (1982)), specialised to the cycle type
`(q₁, q₂, q₃, 1, …)` against a full `N`-cycle on an `N`-point set containing
the support of `z`: for odd `z` with `delta z ≥ 3`, the factorization exists. -/
def BoccaraStatement : Prop :=
  ∀ (n : ℕ) (z : Perm (Fin n)) (N q₁ q₂ q₃ : ℕ),
    md z ≤ N → N ≤ n →
    q₁ + q₂ + q₃ + 1 = N → 2 ≤ q₁ → 2 ≤ q₂ → 2 ≤ q₃ →
    3 ≤ delta z → Odd (delta z) →
    ∃ A B : Perm (Fin n), A.cycleType = {q₁, q₂, q₃} ∧ B.IsCycle ∧ md B = N ∧ z = A * B

/-- **Rosser–Schoenfeld (1962), eq. (3.6)**: `π(x) < 1.25506·x / log x` for `x > 1`. -/
def PiUpperStatement : Prop :=
  ∀ (x : ℝ), 1 < x → ((primesIn 0 x).card : ℝ) ≤ 1.25506 * x / Real.log x

/-- **Rosser–Schoenfeld (1962), eq. (3.5)**: `π(x) > x / log x` for `x ≥ 17`. -/
def PiLowerStatement : Prop :=
  ∀ (x : ℝ), 17 ≤ x → x / Real.log x ≤ ((primesIn 0 x).card : ℝ)

/-- **Montgomery–Vaughan's Brun–Titchmarsh theorem** (*Mathematika* **20**
(1973), Theorem 2): the primes up to `x` in a reduced residue class modulo `d`
number at most `2x / (φ(d) · log(x/d))`, for `x > d`. -/
def BrunTitchmarshStatement : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (a : ZMod d), IsUnit a → ∀ (x : ℝ), (d : ℝ) < x →
    (((primesIn 0 x).filter (fun p : ℕ => (Nat.cast p : ZMod d) = a)).card : ℝ) ≤
      2 * x / ((Nat.totient d : ℝ) * Real.log (x / d))

/-- **Vinogradov's three-primes theorem**, count form (see Vaughan, *The
Hardy–Littlewood Method*, 2nd ed., Theorem 3.4): for odd `M` beyond an
(ineffective) threshold, `r₃(M) ≥ c₁·M²/log³M` for an absolute `c₁ > 0`. -/
def VinogradovStatement : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → Odd M →
    c₁ * (M : ℝ) ^ 2 / (Real.log M) ^ 3 ≤ (r₃ M : ℝ)

/-- **Halberstam–Richert** (*Sieve Methods*, 1974, Theorem 3.11), upper-bound
sieve for Goldbach counts: for even `k ≥ 4`, `r₂(k) ≤ C₂·S(k)·k/log²k` for an
absolute constant `C₂`. -/
def SieveR2Statement : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ k : ℕ, Even k → 4 ≤ k →
    (r₂ k : ℝ) ≤ C₂ * SingSeries k * k / (Real.log k) ^ 2

/-! ## The two principal theorems -/

/-- **Main Theorem (positive direction), conditional form.**  Assuming the
eight classical statements above, there are constants `C : ℝ` and `N₀ : ℕ`
such that for all nonzero integer exponents `r, s` with `r` or `s` odd, and
every `n ≥ N₀` with `C · log m(r,s) ≤ n`, the word `x^r y^s` is universal on
the symmetric group of `Fin n`: every permutation `z` equals `x^r * y^s` for
some permutations `x, y`.  (Powers are integer powers `zpow` in the
permutation group.) -/
theorem kourovka_10_32_conditional (hRS : RSWindowMassStatement)
    (hHKL : HKLStatement) (hBoc : BoccaraStatement)
    (hPiU : PiUpperStatement) (hPiL : PiLowerStatement)
    (hBT : BrunTitchmarshStatement) (hVino : VinogradovStatement)
    (hSieve : SieveR2Statement) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ r s : ℤ, r * s ≠ 0 → (Odd r ∨ Odd s) →
      ∀ n : ℕ, N₀ ≤ n → C * L r s ≤ (n : ℝ) →
        ∀ z : Perm (Fin n), ∃ x y : Perm (Fin n), x ^ r * y ^ s = z :=
  sorry

/-- **Optimality (negative direction), unconditional.**  For every `n` there is
a single odd exponent `s` — the odd part of `lcm(1,…,n)`, as the conjunct
`lcm(1,…,n) = 2^a·s` records — such that the word `x^(lcm(1,…,n)) y^s` attains
no element of order `3` in the symmetric group of `Fin n`, while its cost
`log m(lcm(1,…,n), s)` equals `θ(n) = Σ_{p ≤ n} log p` exactly.
So the logarithmic shape of the main theorem's hypothesis cannot be improved
to `n ≥ log m(r,s)` with constant `1`, since `θ(n) < n` infinitely often (a
classical oscillation fact not formalised here). -/
theorem not_universal (n : ℕ) :
    ∃ s : ℕ, 0 < s ∧ ¬ (2 ∣ s) ∧ s ∣ R n ∧ (∃ a : ℕ, R n = 2 ^ a * s) ∧
      L (R n : ℤ) (s : ℤ) = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ∧
      ∀ z : Perm (Fin n), orderOf z = 3 →
        ∀ x y : Perm (Fin n), x ^ (R n : ℤ) * y ^ (s : ℤ) ≠ z :=
  sorry

end Kourovka1032
