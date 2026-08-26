/-
The universality of words `x^r y^s` in symmetric groups --- Lean formalization.

Answers Problem 10.32 of the Kourovka Notebook.  See `universal-words.tex` for the
mathematics; each Lean file names the section of the paper it formalizes.

`Main.kourovka_10_32` is the Main Theorem; `LowerBound.not_universal` is
Proposition 8.1 (both halves: the word fails at degree `n`, and its cost
`log m(r,s)` is exactly `θ(n)`).  Corollary 8.2, which additionally needs
`θ(n) < n` infinitely often, is not formalized.

The `#print axioms` commands below are the honest accounting of what each result
depends on: everything beyond Lean's three standard axioms is declared in
`ClassicalInputs.lean` and documented there with its source.
-/
import UniversalWords.Basic
import UniversalWords.ClassicalInputs
import UniversalWords.Analytic
import UniversalWords.CountingLemmas
import UniversalWords.SeriesBounds
import UniversalWords.Averaging
import UniversalWords.GoodPrime
import UniversalWords.Windows
import UniversalWords.Cases
import UniversalWords.Dense
import UniversalWords.Main
import UniversalWords.Unconditional
import UniversalWords.LowerBound

-- The conditional main theorem and the whole §8 development are fully proved:
#print axioms UniversalWords.kourovka_10_32_conditional
#print axioms UniversalWords.exists_good_prime
#print axioms UniversalWords.averaging
#print axioms UniversalWords.not_universal
#print axioms UniversalWords.L_eq_theta
-- The quarantined unconditional form assumes the eight classical statements:
#print axioms UniversalWords.kourovka_10_32
