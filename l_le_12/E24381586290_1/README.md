# E24381586290_1

$$4x^4+x+y^3+y+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 77$ |
| Length | $l = 11$ |
| Method | Cubic graph |

## Outline of the proof

The proof uses the cubic Hilbert reciprocity law over the field $K=\mathbb{Q}(\omega)$, where $\omega^2+\omega+1=0$. It uses 2 graphs. For the $g$-th graph, we attach to a hypothetical integer solution the values of auxiliary polynomials $H^{(g)}_i$ with coefficients in $\mathbb{Z}[\omega]$, constants $c^{(g)}_i\in\mathbb{Z}[\omega]$, and a sum $B^{(g)}$ of cubic Hilbert symbols of these values, recorded by weighted edges. By the reciprocity law, the local contributions $B^{(g)}_p$ of all primes $p$ add up to $0$ modulo $3$, for every $g$. We show that $B^{(g)}_p=0$ for $p\notin S$, compute the vectors $(B^{(g)}_p)_g$ for the primes $p\in S$, and obtain a contradiction. Two standard facts from class field theory are quoted without proof: the explicit formula for the cubic Hilbert symbol at the places not above $3$, and the Hilbert reciprocity law. Apart from these, the proof uses polynomial identities, which can be checked by expanding both sides, and finite computations with residues.

The complete proof, with all the identities and tables that it uses, is in [E24381586290_1.pdf](E24381586290_1.pdf) (30 pages).

## Files

- [E24381586290_1.pdf](E24381586290_1.pdf): a self-contained proof.
- [E24381586290_1.tex](E24381586290_1.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E24381586290_1.Challenge l_le_12.E24381586290_1.Solution
lake env /path/to/comparator l_le_12/E24381586290_1/comparator.json
```

[Back to the list of equations](../../README.md)
