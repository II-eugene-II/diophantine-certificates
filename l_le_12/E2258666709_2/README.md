# E2258666709_2

$$x^4+xy+x+3y^3-1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 47$ |
| Length | $l = 11.58$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses a polynomial identity of the form $HT=U^2-5V^2$ on the curve, and the fact that an odd prime $p$ with $\left(\frac{5}{p}\right)=-1$ divides $U^2-5V^2$ only to an even power. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Jacobi symbol and the law of quadratic reciprocity.

The complete proof, with all the identities and tables that it uses, is in [E2258666709_2.pdf](E2258666709_2.pdf) (3 pages).

## Files

- [E2258666709_2.pdf](E2258666709_2.pdf): a self-contained proof.
- [E2258666709_2.tex](E2258666709_2.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E2258666709_2.Challenge l_le_12.E2258666709_2.Solution
lake env /path/to/comparator l_le_12/E2258666709_2/comparator.json
```

[Back to the list of equations](../../README.md)
