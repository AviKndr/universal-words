# The universality of words $x^r y^s$ in symmetric groups

A self-contained paper answering **Problem 10.32 of the Kourovka Notebook**, posed by
Yu. I. Merzlyakov in 1986.

## The result

A word $w$ is *universal* on a group $G$ if the word map $(x,y) \mapsto w(x,y)$ is onto.
Write $m(r,s)$ for the largest squarefree divisor of $rs$ (the product of the distinct
primes dividing $rs$).

> **Main Theorem.** There are absolute constants $C$ and $N_0$ such that, for all nonzero
> integers $r,s$ at least one of which is odd, the word $x^r y^s$ is universal on the
> symmetric group $S_n$ whenever $n \ge \max\{N_0,\, C\log m(r,s)\}$.

This is the symmetric-group analogue of the alternating-group theorem of Brenner, Evans
and Silberger (1986), and it replaces Droste's bound $n \ge \max\{6,\, 4m-4\}$ — linear in
$m$, and the best known since 1986. A complementary construction shows the constant cannot
be taken to be $1$, so the logarithmic shape is **optimal**: the threshold is
$\Theta(\log m)$, and the problem is answered in both directions.

The parity hypothesis is necessary: if $r$ and $s$ are both even, every value of $x^r y^s$
is an even permutation.

### How it goes

Even targets, and odd targets moving at least $n/2$ points, are factored as products of two
cycles of controlled prime-related lengths via the Herzog–Kaplan–Lev two-cycle criterion and
Chebyshev-type prime counting; this part is explicit and fully effective. For odd targets of
small support, the paper *proves* that any such two-cycle factorization would encode prime
constellations of twin-prime type — placing the problem on the divide between binary and
ternary additive prime problems. The escape buys a third summand: such targets are factored
as a permutation of cycle type $(q_1,q_2,q_3,1)$ times a full cycle of even length, via
Boccara's criterion, with the three primes supplied by Vinogradov's three-primes theorem
relative to the excluded set of primes dividing $rs$. That last ingredient is the only
ineffective one.

## Contents

| File | What it is |
| --- | --- |
| `universal-words.tex` | The paper (LaTeX source, `amsart`, no external style files) |
| `universal-words.pdf` | Compiled paper, 14 pages |
| `validate.py` | Machine validation of the paper's computational claims |
| `lean/` | Lean 4 formalization of the proof, on top of Mathlib |

The paper and `validate.py` are self-contained (`validate.py` needs only `sympy`).
The Lean development needs Mathlib; see `lean/README.md`.

## Building

```bash
pdflatex universal-words.tex && pdflatex universal-words.tex
```

No bibliography tool is needed — the bibliography is a `thebibliography` environment.

## Validation

```bash
pip install sympy && python3 validate.py --all
```

Five independent checks, each runnable on its own (`python3 validate.py criteria`, etc.):

- **`criteria`** — exhaustive verification of the two imported factorization criteria:
  Herzog–Kaplan–Lev (products of two cycles) and Boccara (an arbitrary class times a full
  cycle), over all cycle types in small symmetric groups, in both directions.
- **`bookkeeping`** — the inequality and parity chains of Propositions 4.1 and 5.1 and
  Lemma 6.2, exactly as displayed, on random instances $(n,r,s,z)$ with $n$ up to 3000.
- **`endtoend`** — the small-support construction executed on real permutations in
  $S_{14}$–$S_{16}$: build the factorization, take the roots, verify $x^r y^s = z$ exactly.
- **`constants`** — rigorous certification of the numerical constants of the averaging
  lemma (partial Euler products with elementary tail bounds), and $\pi(11927) = 1429$.
- **`lowerbound`** — the optimality construction, exhaustively for $n \le 7$.

These guard chiefly against misquotation of the imported criteria and against slips in
composition-order conventions; the mathematics itself is proved in the paper.

## Formalization

`lean/` contains a Lean 4 formalization checked against Mathlib. The Main Theorem
(`kourovka_10_32`) and the §8 lower bound both compile with **no `sorry`s**.

What that does and does not establish is recorded by `#print axioms`, which the
development runs on itself:

- **`kourovka_10_32_conditional`** — the Main Theorem as a fully-proved
  implication: eight explicitly stated published theorems (Herzog–Kaplan–Lev,
  Boccara, three Rosser–Schoenfeld bounds, Brun–Titchmarsh, the
  Halberstam–Richert sieve, Vinogradov) imply the logarithmic universality
  bound. This implication, the paper's entire analysis (Lemma 6.4 and
  Proposition 6.5), and §8's Proposition 8.1 are all proved **using only
  Lean's three standard axioms** — no custom axiom appears in any of their
  dependency sets.
- **Proposition 8.1** (§8) is unconditional outright: the word
  `x^lcm(1..n) y^s` misses every element of order 3, and its cost
  `log m(r,s)` is exactly `θ(n)`.
- A quarantined module (`Unconditional.lean`, imported by nothing else)
  assumes the eight statements as axioms — each a published theorem with its
  source documented — and derives the unconditional `kourovka_10_32`.

The one deliberately unformalized step is Corollary 8.2's use of `θ(n) < n`
infinitely often (a deep oscillation theorem), so the *optimality* conclusion —
though its construction is verified — is not machine-checked. See
`lean/README.md` for the exact axiom listing.

## Status

Preprint, **not yet refereed**. Comments and corrections are welcome via the issue tracker.

## A note on how this was written

The paper was researched and written with substantial assistance from Claude (Anthropic) —
literature retrieval and verification, design and checking of the argument, and drafting —
and was put through repeated adversarial review passes, with every load-bearing citation
checked against primary sources and the computational claims checked by the suite above.
The disclosure is repeated in the paper's acknowledgements. Errors are the author's.
