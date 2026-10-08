# E17326866_1

$$x^4+x+y^3+2y^2+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 35$ |
| Length | $l = 11$ |
| Method | Quadratic norm |

## Certificate

One quadratic norm identity. Put $F=x^4+x+y^3+2y^2+1$ and

$$H=x-2y,\qquad U=16x^2+x+2,\qquad V=3x+6,\qquad T=32x^2+64xy+128x+128y^2+256y.$$

Then

$$HT-U^2-7V^2=-256\,F,$$

so $HT=U^2+7V^2$ at every integer solution. The proof shows that $H>0$, that $\left(\frac{H}{7}\right)=-1$, and that every odd prime $p$ with $\left(\frac{-7}{p}\right)=-1$ divides $H$ to an even power. By quadratic reciprocity, these three facts cannot hold together.

The complete proof, with all the identities and tables that it uses, is in [E17326866_1.pdf](E17326866_1.pdf) (3 pages).

## Files

- [E17326866_1.pdf](E17326866_1.pdf): a self-contained proof.
- [E17326866_1.tex](E17326866_1.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build h_eq_35.E17326866_1.Challenge h_eq_35.E17326866_1.Solution
lake env /path/to/comparator h_eq_35/E17326866_1/comparator.json
```

[Back to the list of equations](../../README.md)
