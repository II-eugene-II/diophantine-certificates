# E7522502_5

$$2x^4+xy+y^3-y+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 47$ |
| Length | $l = 11$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses two polynomial identities of the form $H_kT_k=U_k^2+d_kV_k^2$ on the curve, with $(d_1,d_2)=(-11,22)$, and the fact that an odd prime $p$ with $\left(\frac{-d_k}{p}\right)=-1$ divides $U_k^2+d_kV_k^2$ only to an even power. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Jacobi symbol and the law of quadratic reciprocity.

The complete proof, with all the identities and tables that it uses, is in [E7522502_5.pdf](E7522502_5.pdf) (4 pages).

## Files

- [E7522502_5.pdf](E7522502_5.pdf): a self-contained proof.
- [E7522502_5.tex](E7522502_5.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E7522502_5.Challenge l_le_12.E7522502_5.Solution
lake env /path/to/comparator l_le_12/E7522502_5/comparator.json
```

[Back to the list of equations](../../README.md)
