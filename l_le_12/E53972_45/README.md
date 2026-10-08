# E53972_45

$$x^5-2x+y^3-y+2=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 48$ |
| Length | $l = 12$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses two polynomial identities of the form $H_kT_k=U_k^2+3V_k^2$ on the curve, and the fact that an odd prime $p$ with $\left(\frac{-3}{p}\right)=-1$ divides $U_k^2+3V_k^2$ only to an even power. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Jacobi symbol and the law of quadratic reciprocity.

The complete proof, with all the identities and tables that it uses, is in [E53972_45.pdf](E53972_45.pdf) (4 pages).

## Files

- [E53972_45.pdf](E53972_45.pdf): a self-contained proof.
- [E53972_45.tex](E53972_45.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E53972_45.Challenge l_le_12.E53972_45.Solution
lake env /path/to/comparator l_le_12/E53972_45/comparator.json
```

[Back to the list of equations](../../README.md)
