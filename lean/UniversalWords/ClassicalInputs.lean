/-
The external inputs of the paper, as axioms.

This file **states** three published theorems as named propositions; it
assumes nothing.  Each statement is quoted in the exact form the paper uses,
with its source documented.  The main development is parameterized by these
statements as hypotheses, so the principal theorem
(`kourovka_10_32_conditional`) is *fully proved* using only Lean's standard
axioms.  `Unconditional.lean` separately assumes the statements as axioms to
recover the unconditional form; running `#print axioms` in
`UniversalWords.lean` shows both dependency sets.

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

/-! ## Statement 1: Rosser--Schoenfeld, in window-mass form -/

/-- **Rosser--Schoenfeld.**  The primes in `(a, b]` carry logarithmic mass at least
`0.985 b - 1.01624 a`.  This is `θ(b) - θ(a)` bounded below by combining
`θ(b) > 0.985 b` (valid for `b > 11927`) with `θ(a) < 1.01624 a` (valid for all
`a > 0`; at `a = 0` both sides are the trivial `θ(0) = 0`); it is the only form of Chebyshev-type prime counting the paper uses. -/
def RSWindowMassStatement : Prop :=
  ∀ (a b : ℝ), 0 ≤ a → (11927 : ℝ) < b → a ≤ b →
    0.985 * b - 1.01624 * a ≤ ∑ p ∈ primesIn a b, Real.log p

/-! ## Statement 2: the Herzog--Kaplan--Lev two-cycle criterion -/

/-- **Herzog--Kaplan--Lev, Theorem 7**, sufficiency of clause (b): under the sum,
parity and difference constraints, `σ` is a product of an `l₁`-cycle and an
`l₂`-cycle.  (The paper never uses the necessity direction outside the obstruction
Proposition 6.1, which is commentary rather than part of the proof.) -/
def HKLStatement : Prop :=
  ∀ (n : ℕ) (σ : Perm (Fin n)), σ ≠ 1 → ∀ (l₁ l₂ : ℕ),
    l₂ ≤ l₁ → 2 ≤ l₂ → l₁ ≤ n →
    md σ + cy σ ≤ l₁ + l₂ →
    (l₁ + l₂) % 2 = (md σ + cy σ) % 2 →
    l₁ - l₂ ≤ delta σ →
    ∃ A B : Perm (Fin n), A.IsCycle ∧ md A = l₁ ∧ B.IsCycle ∧ md B = l₂ ∧ σ = A * B

/-! ## Statement 3: Boccara's full-cycle criterion, in the form used -/

/-- **Boccara (1982)**, specialised to `λ = (q₁,q₂,q₃,1)` against the class of
`N`-cycles on an `N`-point subset containing the support of `z`.

The general criterion reads `ℓ(λ) + ℓ(μ) ≤ N+1` with equality of parity mod 2,
counting fixed points as parts.  Here `ℓ(λ) = 4` and `ℓ(μ) = cy z + (N - md z)`,
so the two conditions become exactly `3 ≤ δ(z)` and `δ(z)` odd, which is how they
are stated below. -/
def BoccaraStatement : Prop :=
  ∀ (n : ℕ) (z : Perm (Fin n)) (N q₁ q₂ q₃ : ℕ),
    md z ≤ N → N ≤ n →
    q₁ + q₂ + q₃ + 1 = N → 2 ≤ q₁ → 2 ≤ q₂ → 2 ≤ q₃ →
    3 ≤ delta z → Odd (delta z) →
    ∃ A B : Perm (Fin n), A.cycleType = {q₁, q₂, q₃} ∧ B.IsCycle ∧ md B = N ∧ z = A * B

end UniversalWords
