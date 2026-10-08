# E851604_5

$$x^4+xy+x+y^3-y+2=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 34$ |
| Length | $l = 12$ |
| Method | Cubic graph |

## Outline of the proof

The proof uses the cubic Hilbert reciprocity law over the field $K=\mathbb{Q}(\omega)$, where $\omega^2+\omega+1=0$. To a hypothetical integer solution we attach the values of 21 auxiliary polynomials $H_0,\dots,H_{20}$ with coefficients in $\mathbb{Z}[\omega]$, constants $c_0,\dots,c_{20}\in\mathbb{Z}[\omega]$, and a sum $B$ of cubic Hilbert symbols of these values, recorded by a graph with 54 weighted edges. By the reciprocity law, the local contributions $B_p$ of all primes $p$ add up to $0$ modulo $3$. We show that $B_p=0$ for $p\notin S$, compute $B_p$ for the primes $p\in S$, and obtain a contradiction. Two standard facts from class field theory are quoted without proof: the explicit formula for the cubic Hilbert symbol at the places not above $3$, and the Hilbert reciprocity law. Apart from these, the proof uses polynomial identities, which can be checked by expanding both sides, and finite computations with residues.

The complete proof, with all the identities and tables that it uses, is in [E851604_5.pdf](E851604_5.pdf) (8 pages).

## Files

- [E851604_5.pdf](E851604_5.pdf): a self-contained proof.
- [E851604_5.tex](E851604_5.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_le_34.E851604_5.Challenge h_le_34.E851604_5.Solution
lake env /path/to/comparator h_le_34/E851604_5/comparator.json
```

[Back to the list of equations](../../README.md)
