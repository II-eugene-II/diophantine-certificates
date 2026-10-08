# E114892895_2

$$2x^5+xy+y^3+y-1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 79$ |
| Length | $l = 12$ |
| Method | Quadratic graph |

## Outline of the proof

The proof uses 4 auxiliary polynomials $H_0,\dots,H_{3}$, 2 of which are constants, and a graph on these vertices with 3 edges; to each edge $\lbrace i,j\rbrace $ we attach the Hilbert symbol $(H_i,H_j)_v$ of the values at a hypothetical solution. By the product formula, the product of these symbols over all edges and all places is $1$. We show that the product over the edges is $1$ at every odd prime outside a finite set $S$, compute it at the primes of $S$ and at the real place, and obtain a contradiction. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Legendre symbol and of the Hilbert symbol.

The complete proof, with all the identities and tables that it uses, is in [E114892895_2.pdf](E114892895_2.pdf) (5 pages).

## Files

- [E114892895_2.pdf](E114892895_2.pdf): a self-contained proof.
- [E114892895_2.tex](E114892895_2.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E114892895_2.Challenge l_le_12.E114892895_2.Solution
lake env /path/to/comparator l_le_12/E114892895_2/comparator.json
```

[Back to the list of equations](../../README.md)
