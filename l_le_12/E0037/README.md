# E0037

$$2y^3 + xy + x^4 + 1 = 0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 37$ |
| Length | $l = 10$ |
| Method | Quadratic norm |
| Paper | Section 6.1, Table 9 |

In Table 9 of the paper it is written as $2y^3+xy=x^4+1$, after replacing $y$ by $-y$.

## Files

- [E0037.pdf](E0037.pdf): a self-contained proof.
- [E0037.tex](E0037.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It is self-contained and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`.
