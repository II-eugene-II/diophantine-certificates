# H33_01 (E0258)

$$y^3 + y^2 + xy = x^4 + 1$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 33$ |
| Length | $l = 11$ |
| Method | Quadratic norm |
| Paper | Table 1; Section 3.3, Table 2 |

The identifier E0258 refers to the equation $x^4 + xy + y^3 - y^2 + 1 = 0$, which is obtained by replacing $y$ by $-y$.

## Files

- [H33_01.pdf](H33_01.pdf): a self-contained proof.
- [H33_01.tex](H33_01.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It is self-contained and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`.
