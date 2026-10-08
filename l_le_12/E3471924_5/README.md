# E3471924_5

$$2x^4+x+y^3-y+2=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 46$ |
| Length | $l = 11$ |
| Method | Cubic and quadratic graphs |

## Outline of the proof

The proof combines quadratic Hilbert symbols over $\mathbb{Q}$ and cubic Hilbert symbols over $K=\mathbb{Q}(\omega)$, where $\omega^2+\omega+1=0$. To a hypothetical integer solution we attach the values of auxiliary polynomials $H_i$ with rational coefficients, linked by a graph, and the values of auxiliary polynomials $J_i$ with coefficients in $\mathbb{Z}[\omega]$, linked by a weighted graph. By the product formula and the reciprocity law, the products of the quadratic symbols over all places are $1$, and the sums of the cubic symbols over all places are $0$. We show that the local contributions vanish at the primes outside a finite set $S$, determine the sign contributions at the real place, compute the local contributions jointly at the primes of $S$, and obtain a contradiction. Apart from polynomial identities, which can be checked by expanding both sides, finite computations with residues, and basic properties of the Legendre symbol and of the quadratic Hilbert symbol, the proof uses two standard facts from class field theory: the explicit formula for the cubic Hilbert symbol at the places not above $3$, and the Hilbert reciprocity law.

The complete proof, with all the identities and tables that it uses, is in [E3471924_5.pdf](E3471924_5.pdf) (18 pages).

## Files

- [E3471924_5.pdf](E3471924_5.pdf): a self-contained proof.
- [E3471924_5.tex](E3471924_5.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E3471924_5.Challenge l_le_12.E3471924_5.Solution
lake env /path/to/comparator l_le_12/E3471924_5/comparator.json
```

[Back to the list of equations](../../README.md)
