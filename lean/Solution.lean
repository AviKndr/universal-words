import UniversalWords.Main
import UniversalWords.LowerBound

/-!
# Solution to the Challenge

This module redeclares, definition-for-definition, the environment of
`Challenge.lean` (Comparator requires every declaration used in the compared
statements to agree between the two environments) and then supplies proofs of
the two compared theorems by instantiating the `UniversalWords` development:

* `Kourovka1032.kourovka_10_32_conditional` is
  `UniversalWords.kourovka_10_32_conditional` (proved in
  `UniversalWords/Main.lean` from the eight classical statements taken as
  hypotheses); the definitions here are definitionally equal to the library's.
* `Kourovka1032.not_universal` is `UniversalWords.not_universal` (proved in
  `UniversalWords/LowerBound.lean`).

Both library theorems depend only on the axioms `propext`,
`Classical.choice`, and `Quot.sound`; `UniversalWords.lean` prints the audit.
-/

namespace Kourovka1032

open Equiv Equiv.Perm
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

def md (σ : Perm α) : ℕ := σ.support.card

def cy (σ : Perm α) : ℕ := Multiset.card σ.cycleType

def delta (σ : Perm α) : ℕ := md σ - cy σ

def mrs (r s : ℤ) : ℕ := (r * s).natAbs.primeFactors.prod id

noncomputable def L (r s : ℤ) : ℝ := Real.log (mrs r s)

noncomputable def primesIn (a b : ℝ) : Finset ℕ :=
  (Finset.range (⌊b⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ a < (p : ℝ))

def R (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

def pairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
    (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = k)

def triples (M : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = M)

def r₂ (k : ℕ) : ℕ := (pairs k).card

def r₃ (M : ℕ) : ℕ := (triples M).card

noncomputable def SingSeries (k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))

def RSWindowMassStatement : Prop :=
  ∀ (a b : ℝ), 0 ≤ a → (11927 : ℝ) < b → a ≤ b →
    0.985 * b - 1.01624 * a ≤ ∑ p ∈ primesIn a b, Real.log p

def HKLStatement : Prop :=
  ∀ (n : ℕ) (σ : Perm (Fin n)), σ ≠ 1 → ∀ (l₁ l₂ : ℕ),
    l₂ ≤ l₁ → 2 ≤ l₂ → l₁ ≤ n →
    md σ + cy σ ≤ l₁ + l₂ →
    (l₁ + l₂) % 2 = (md σ + cy σ) % 2 →
    l₁ - l₂ ≤ delta σ →
    ∃ A B : Perm (Fin n), A.IsCycle ∧ md A = l₁ ∧ B.IsCycle ∧ md B = l₂ ∧ σ = A * B

def BoccaraStatement : Prop :=
  ∀ (n : ℕ) (z : Perm (Fin n)) (N q₁ q₂ q₃ : ℕ),
    md z ≤ N → N ≤ n →
    q₁ + q₂ + q₃ + 1 = N → 2 ≤ q₁ → 2 ≤ q₂ → 2 ≤ q₃ →
    3 ≤ delta z → Odd (delta z) →
    ∃ A B : Perm (Fin n), A.cycleType = {q₁, q₂, q₃} ∧ B.IsCycle ∧ md B = N ∧ z = A * B

def PiUpperStatement : Prop :=
  ∀ (x : ℝ), 1 < x → ((primesIn 0 x).card : ℝ) ≤ 1.25506 * x / Real.log x

def PiLowerStatement : Prop :=
  ∀ (x : ℝ), 17 ≤ x → x / Real.log x ≤ ((primesIn 0 x).card : ℝ)

def BrunTitchmarshStatement : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (a : ZMod d), IsUnit a → ∀ (x : ℝ), (d : ℝ) < x →
    (((primesIn 0 x).filter (fun p : ℕ => (Nat.cast p : ZMod d) = a)).card : ℝ) ≤
      2 * x / ((Nat.totient d : ℝ) * Real.log (x / d))

def VinogradovStatement : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → Odd M →
    c₁ * (M : ℝ) ^ 2 / (Real.log M) ^ 3 ≤ (r₃ M : ℝ)

def SieveR2Statement : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ k : ℕ, Even k → 4 ≤ k →
    (r₂ k : ℝ) ≤ C₂ * SingSeries k * k / (Real.log k) ^ 2

theorem kourovka_10_32_conditional (hRS : RSWindowMassStatement)
    (hHKL : HKLStatement) (hBoc : BoccaraStatement)
    (hPiU : PiUpperStatement) (hPiL : PiLowerStatement)
    (hBT : BrunTitchmarshStatement) (hVino : VinogradovStatement)
    (hSieve : SieveR2Statement) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ r s : ℤ, r * s ≠ 0 → (Odd r ∨ Odd s) →
      ∀ n : ℕ, N₀ ≤ n → C * L r s ≤ (n : ℝ) →
        ∀ z : Perm (Fin n), ∃ x y : Perm (Fin n), x ^ r * y ^ s = z :=
  UniversalWords.kourovka_10_32_conditional hRS hHKL hBoc hPiU hPiL hBT hVino hSieve

theorem not_universal (n : ℕ) :
    ∃ s : ℕ, 0 < s ∧ ¬ (2 ∣ s) ∧ s ∣ R n ∧ (∃ a : ℕ, R n = 2 ^ a * s) ∧
      L (R n : ℤ) (s : ℤ) = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ∧
      ∀ z : Perm (Fin n), orderOf z = 3 →
        ∀ x y : Perm (Fin n), x ^ (R n : ℤ) * y ^ (s : ℤ) ≠ z :=
  UniversalWords.not_universal n

end Kourovka1032
