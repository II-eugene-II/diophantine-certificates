# E354835_32

$$x^4+xy+y^3+y-5=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 35$ |
| Length | $l = 12.32$ |
| Method | Quadratic norm |

## Outline of the proof

The proof uses two polynomial identities of the form $H_kT_k=U_k^2+d_kV_k^2$ on the curve, where $d_{1}=H_{2}$ and $d_{2}=-H_{1}$, and the product formula for the Hilbert symbol of one pair of values. Apart from polynomial identities, which can be checked by expanding both sides, and finite checks of congruences, the proof uses only basic properties of the Legendre symbol and of the Hilbert symbol.

The complete proof, with all the identities and tables that it uses, is in [E354835_32.pdf](E354835_32.pdf) (5 pages).

## Files

- [E354835_32.pdf](E354835_32.pdf): a self-contained proof.
- [E354835_32.tex](E354835_32.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_eq_35.E354835_32.Challenge h_eq_35.E354835_32.Solution
lake env /path/to/comparator h_eq_35/E354835_32/comparator.json
```

[Back to the list of equations](../../README.md)
