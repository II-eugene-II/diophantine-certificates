# E524064_25

$$x^4+x+y^3-2y+5=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 35$ |
| Length | $l = 12.32$ |
| Method | Cubic graph |

## Certificate

One reciprocity graph over $K=\mathbb{Q}(\omega)$, where $\omega^2+\omega+1=0$, for the cubic Hilbert symbol. Its 44 vertices are auxiliary polynomials $H_0,\dots,H_{43}$ with coefficients in $\mathbb{Z}[\omega]$, each with a constant $c_i\in\mathbb{Z}[\omega]$, and it has 187 weighted edges.

At an integer solution, the edges give local contributions $B_p\in\mathbb{Z}/3\mathbb{Z}$ of the primes $p$, and by the Hilbert reciprocity law their sum is $0$. The proof shows that $B_p=0$ for every prime $p$ outside $S=\lbrace 2,3,7,13 \rbrace$, while $\sum_{p\in S}B_p=1$.

The complete proof, with all the identities and tables that it uses, is in [E524064_25.pdf](E524064_25.pdf) (11 pages).

## Files

- [E524064_25.pdf](E524064_25.pdf): a self-contained proof.
- [E524064_25.tex](E524064_25.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_eq_35.E524064_25.Challenge h_eq_35.E524064_25.Solution
lake env /path/to/comparator h_eq_35/E524064_25/comparator.json
```

[Back to the list of equations](../../README.md)
