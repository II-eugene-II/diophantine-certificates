# E851604_1

$$x^4+xy+x+y^3+2=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 32$ |
| Length | $l = 11$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses four polynomial identities of the form $H_kT_k=U_k^2+d_kV_k^2$ on the curve, where $d_{1}=H_{2}$, $d_{2}=H_{1}$, $d_{3}=1$, and $d_{4}=2$, and the product formula for three Hilbert symbols. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Legendre symbol and of the Hilbert symbol.

The complete proof, with all the identities and tables that it uses, is in [E851604_1.pdf](E851604_1.pdf) (7 pages).

## Files

- [E851604_1.pdf](E851604_1.pdf): a self-contained proof.
- [E851604_1.tex](E851604_1.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_le_34.E851604_1.Challenge h_le_34.E851604_1.Solution
lake env /path/to/comparator h_le_34/E851604_1/comparator.json
```

[Back to the list of equations](../../README.md)
