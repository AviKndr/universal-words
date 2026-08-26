/-
The external inputs of the paper, as axioms.

**Everything in this file is assumed, not proved.**  Each axiom is a published
theorem cited in the paper, restated in the exact form in which the paper uses
it, with one clearly-flagged exception (`exists_good_prime`) noted below.  Running
`#print axioms UniversalWords.kourovka_10_32` at the end of `Main.lean` lists
precisely which of these the final theorem depends on.

Sources:
* `hkl` --- M. Herzog, G. Kaplan, A. Lev, *Representation of permutations as
  products of two cycles*, Discrete Math. **285** (2004), 323--327, Theorem 7
  (sufficiency of clause (b) only).
* `boccara_three` --- G. Boccara, *Cycles comme produit de deux permutations de
  classes données*, Discrete Math. **38** (1982), 129--142, specialised to the
  cycle type `(q₁,q₂,q₃,1)` against a full cycle, which is the only case used.
* `rs_window_mass` --- J. B. Rosser, L. Schoenfeld, Illinois J. Math. **6**
  (1962), Theorem 9 (`θ(x) < 1.01624x`), together with Math. Comp. **29** (1975),
  Corollary to Theorem 6 (`θ(x) > 0.985x` for `x > 11927`); the difference of the
  two gives the stated mass bound on a window.
* `exists_good_prime` --- **this one is the paper's own Proposition 6.5**, not an
  external citation.  Its proof (paper §6.2--6.3) derives it from Vinogradov's
  three-primes theorem, an upper-bound sieve (Halberstam--Richert Theorem 3.11)
  and Brun--Titchmarsh (Montgomery--Vaughan), by averaging the singular series
  over a window of primes.  That analytic argument is *not* formalised here; it
  is assumed, and the honest reading of `Main.lean` is "the combinatorial content
  of the paper is machine-checked, conditional on Proposition 6.5 and on the four
  published theorems above".
-/
import UniversalWords.Basic

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

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

/-! ## Axiom 1: Rosser--Schoenfeld, in window-mass form -/

/-- **Rosser--Schoenfeld.**  The primes in `(a, b]` carry logarithmic mass at least
`0.985 b - 1.01624 a`.  This is `θ(b) - θ(a)` bounded below by combining
`θ(b) > 0.985 b` (valid for `b > 11927`) with `θ(a) < 1.01624 a` (valid for all
`a > 0`); it is the only form of Chebyshev-type prime counting the paper uses. -/
axiom rs_window_mass (a b : ℝ) (ha : 0 ≤ a) (hb : (11927 : ℝ) < b) (hab : a ≤ b) :
    0.985 * b - 1.01624 * a ≤ ∑ p ∈ primesIn a b, Real.log p

/-! ## Axiom 2: the Herzog--Kaplan--Lev two-cycle criterion -/

/-- **Herzog--Kaplan--Lev, Theorem 7**, sufficiency of clause (b): under the sum,
parity and difference constraints, `σ` is a product of an `l₁`-cycle and an
`l₂`-cycle.  (The paper never uses the necessity direction outside the obstruction
Proposition 6.1, which is commentary rather than part of the proof.) -/
axiom hkl {n : ℕ} (σ : Perm (Fin n)) (hσ : σ ≠ 1) (l₁ l₂ : ℕ)
    (hle : l₂ ≤ l₁) (hl₂ : 2 ≤ l₂) (hl₁ : l₁ ≤ n)
    (hsum : md σ + cy σ ≤ l₁ + l₂)
    (hpar : (l₁ + l₂) % 2 = (md σ + cy σ) % 2)
    (hdiff : l₁ - l₂ ≤ delta σ) :
    ∃ A B : Perm (Fin n), A.IsCycle ∧ md A = l₁ ∧ B.IsCycle ∧ md B = l₂ ∧ σ = A * B

/-! ## Axiom 3: Boccara's full-cycle criterion, in the form used -/

/-- **Boccara (1982)**, specialised to `λ = (q₁,q₂,q₃,1)` against the class of
`N`-cycles on an `N`-point subset containing the support of `z`.

The general criterion reads `ℓ(λ) + ℓ(μ) ≤ N+1` with equality of parity mod 2,
counting fixed points as parts.  Here `ℓ(λ) = 4` and `ℓ(μ) = cy z + (N - md z)`,
so the two conditions become exactly `3 ≤ δ(z)` and `δ(z)` odd, which is how they
are stated below. -/
axiom boccara_three {n : ℕ} (z : Perm (Fin n)) (N q₁ q₂ q₃ : ℕ)
    (hmd : md z ≤ N) (hN : N ≤ n)
    (hq : q₁ + q₂ + q₃ + 1 = N) (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂) (h₃ : 2 ≤ q₃)
    (hdelta : 3 ≤ delta z) (hodd : Odd (delta z)) :
    ∃ A B : Perm (Fin n), A.cycleType = {q₁, q₂, q₃} ∧ B.IsCycle ∧ md B = N ∧ z = A * B

/-! ## Axiom 4: the paper's Proposition 6.5 (NOT an external citation) -/

/-- **Proposition 6.5 of the paper** --- assumed here, not formalised.

Given the exponents, for `n` beyond an (ineffective) threshold and past the
logarithmic barrier, there is a prime `q̃` in `(n/4, n/2]` not dividing `s` such
that `2q̃ - 1` is a sum of three primes none of which divides `rs`.

The paper proves this in §6.2--6.3 from Vinogradov's three-primes theorem, an
upper-bound sieve, and Brun--Titchmarsh, by averaging the singular series over the
window; the ineffectivity of `N₀` in the Main Theorem enters here and only here.

Note the quantifier order, which is the whole content of Problem 10.32: the
constants `C_star` and `N_star` are chosen *before* `r` and `s`, so the threshold
is uniform in the word.  (`N_star` is the ineffective one.) -/
axiom exists_good_prime :
    ∃ (C_star : ℝ) (N_star : ℕ), (4.65 : ℝ) ≤ C_star ∧
      ∀ (r s : ℤ), r * s ≠ 0 → ∀ n : ℕ, N_star ≤ n → C_star * L r s ≤ (n : ℝ) →
        ∃ qt q₁ q₂ q₃ : ℕ, qt.Prime ∧ ¬ (qt ∣ s.natAbs) ∧
          ((n : ℝ) + 2) / 4 < (qt : ℝ) ∧ (qt : ℝ) ≤ (n : ℝ) / 2 ∧
          q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
          ¬ (q₁ ∣ (r * s).natAbs) ∧ ¬ (q₂ ∣ (r * s).natAbs) ∧ ¬ (q₃ ∣ (r * s).natAbs) ∧
          q₁ + q₂ + q₃ + 1 = 2 * qt

end UniversalWords
