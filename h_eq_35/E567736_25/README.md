# E567736_25

$$x^4+xy+y^3-2y+3=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 35$ |
| Length | $l = 12.58$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses two polynomial identities of the form $H_kT_k=U_k^2+d_kV_k^2$ on the curve, with $(d_{1},d_{2})=(15,15)$, the fact that an odd prime $p$ with $\left(\frac{-d_k}{p}\right)=-1$ divides $U_k^2+d_kV_k^2$ only to an even power, and the product formula for Hilbert symbols. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Legendre symbol and of the Hilbert symbol.

The complete proof, with all the identities and tables that it uses, is in [E567736_25.pdf](E567736_25.pdf) (4 pages).

## Files

- [E567736_25.pdf](E567736_25.pdf): a self-contained proof.
- [E567736_25.tex](E567736_25.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_eq_35.E567736_25.Challenge h_eq_35.E567736_25.Solution
lake env /path/to/comparator h_eq_35/E567736_25/comparator.json
```

[Back to the list of equations](../../README.md)
