# E105653540590_1

$$4x^4+xy+y^3+y+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 79$ |
| Length | $l = 12$ |
| Method | Cubic graph |

## Outline of the proof

The proof uses the cubic Hilbert reciprocity law over the field $K=\mathbb{Q}(\omega)$, where $\omega^2+\omega+1=0$. To a hypothetical integer solution we attach the values of 64 auxiliary polynomials $H_0,\dots,H_{63}$ with coefficients in $\mathbb{Z}[\omega]$, constants $c_0,\dots,c_{63}\in\mathbb{Z}[\omega]$, and a sum $B$ of cubic Hilbert symbols of these values, recorded by a graph with 286 weighted edges. By the reciprocity law, the local contributions $B_p$ of all primes $p$ add up to $0$ modulo $3$. We show that $B_p=0$ for $p\notin S$, compute $B_p$ for the primes $p\in S$, and obtain a contradiction. Two standard facts from class field theory are quoted without proof: the explicit formula for the cubic Hilbert symbol at the places not above $3$, and the Hilbert reciprocity law. Apart from these, the proof uses polynomial identities, which can be checked by expanding both sides, and finite computations with residues.

The complete proof, with all the identities and tables that it uses, is in [E105653540590_1.pdf](E105653540590_1.pdf) (21 pages).

## Files

- [E105653540590_1.pdf](E105653540590_1.pdf): a self-contained proof.
- [E105653540590_1.tex](E105653540590_1.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E105653540590_1.Challenge l_le_12.E105653540590_1.Solution
lake env /path/to/comparator l_le_12/E105653540590_1/comparator.json
```

[Back to the list of equations](../../README.md)
