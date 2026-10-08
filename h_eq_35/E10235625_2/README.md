# E10235625_2

$$x^4+x+y^3+4y-1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 35$ |
| Length | $l = 11$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses five polynomial identities of the form $H_kT_k=U_k^2+d_kV_k^2$ on the curve, where $d_{1}=2H_{2}$, $d_{2}=-2H_{1}$, $d_{3}=-H_{4}$, $d_{4}=-19H_{3}$, and $d_{5}=-19$, and the product formula for three Hilbert symbols. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Legendre symbol and of the Hilbert symbol.

The complete proof, with all the identities and tables that it uses, is in [E10235625_2.pdf](E10235625_2.pdf) (9 pages).

## Files

- [E10235625_2.pdf](E10235625_2.pdf): a self-contained proof.
- [E10235625_2.tex](E10235625_2.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_eq_35.E10235625_2.Challenge h_eq_35.E10235625_2.Solution
lake env /path/to/comparator h_eq_35/E10235625_2/comparator.json
```

[Back to the list of equations](../../README.md)
