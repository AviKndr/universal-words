/-
The external inputs of the paper, as axioms.

**Everything in this file is assumed, not proved.**  Each axiom is a published
theorem cited in the paper, restated in the exact form in which the paper uses
it.  (In earlier revisions the paper's own Proposition 6.5 was also an axiom
here; it is now **proved** in `GoodPrime.lean` from the analytic axioms of
`Analytic.lean`.)  Running `#print axioms UniversalWords.kourovka_10_32` in
`UniversalWords.lean` lists precisely which axioms the final theorem depends
on.

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
-/
import UniversalWords.Basic

namespace UniversalWords

open Equiv Equiv.Perm
open scoped Classical

/-! ## Axiom 1: Rosser--Schoenfeld, in window-mass form -/

/-- **Rosser--Schoenfeld.**  The primes in `(a, b]` carry logarithmic mass at least
`0.985 b - 1.01624 a`.  This is `θ(b) - θ(a)` bounded below by combining
`θ(b) > 0.985 b` (valid for `b > 11927`) with `θ(a) < 1.01624 a` (valid for all
`a > 0`; at `a = 0` both sides are the trivial `θ(0) = 0`); it is the only form of Chebyshev-type prime counting the paper uses. -/
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

end UniversalWords
