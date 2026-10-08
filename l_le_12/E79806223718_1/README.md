# E79806223718_1

$$2x^4+xy+3y^3+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 61$ |
| Length | $l = 11.58$ |
| Method | Quadratic graph |

## Outline of the proof

The proof uses 21 auxiliary polynomials $H_0,\dots,H_{20}$, 6 of which are constants, and a graph on these vertices with 42 edges; to each edge $\lbrace i,j\rbrace $ we attach the Hilbert symbol $(H_i,H_j)_v$ of the values at a hypothetical solution. By the product formula, the product of these symbols over all edges and all places is $1$. We show that the product over the edges is $1$ at every odd prime outside a finite set $S$, compute it at the primes of $S$ and at the real place, and obtain a contradiction. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Legendre symbol and of the Hilbert symbol.

The complete proof, with all the identities and tables that it uses, is in [E79806223718_1.pdf](E79806223718_1.pdf) (11 pages).

## Files

- [E79806223718_1.pdf](E79806223718_1.pdf): a self-contained proof.
- [E79806223718_1.tex](E79806223718_1.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E79806223718_1.Challenge l_le_12.E79806223718_1.Solution
lake env /path/to/comparator l_le_12/E79806223718_1/comparator.json
```

[Back to the list of equations](../../README.md)
