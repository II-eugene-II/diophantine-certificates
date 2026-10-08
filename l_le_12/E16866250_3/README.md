# E16866250_3

$$x^5-x+y^3+4y+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 51$ |
| Length | $l = 12$ |
| Method | Quartic graph |

## Outline of the proof

The proof uses the quartic Hilbert reciprocity law over the field $K=\mathbb{Q}(i)$. To a hypothetical integer solution we attach the values of 82 auxiliary polynomials $H_0,\dots,H_{81}$ with coefficients in $\mathbb{Z}[i]$, constants $c_0,\dots,c_{81}\in\mathbb{Z}[i]$, and a sum $B$ of quartic Hilbert symbols of these values, recorded by a graph with 676 weighted edges. By the reciprocity law, the local contributions $B_p$ of all primes $p$ add up to $0$ modulo $4$. We show that $B_p=0$ for $p\notin S$, compute $B_p$ for the primes $p\in S$, and obtain a contradiction. Two standard facts from class field theory are quoted without proof: the explicit formula for the quartic Hilbert symbol at the places not above $2$, and the Hilbert reciprocity law. Apart from these, the proof uses polynomial identities, which can be checked by expanding both sides, and finite computations with residues.

The complete proof, with all the identities and tables that it uses, is in [E16866250_3.pdf](E16866250_3.pdf) (29 pages).

## Files

- [E16866250_3.pdf](E16866250_3.pdf): a self-contained proof.
- [E16866250_3.tex](E16866250_3.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E16866250_3.Challenge l_le_12.E16866250_3.Solution
lake env /path/to/comparator l_le_12/E16866250_3/comparator.json
```

[Back to the list of equations](../../README.md)
