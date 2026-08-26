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
import UniversalWords.Windows
import UniversalWords.Cases
import UniversalWords.Dense
import UniversalWords.Main
import UniversalWords.LowerBound

#print axioms UniversalWords.kourovka_10_32
#print axioms UniversalWords.not_universal
#print axioms UniversalWords.L_eq_theta
#print axioms UniversalWords.exists_dyadic_prime
