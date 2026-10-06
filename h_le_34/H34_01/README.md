# H34_01 (E1179)

$$y^3 + y^2 = x^4 + x + 4$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 34$ |
| Length | $l = 12$ |
| Method | Quadratic norm |
| Paper | Table 1; Section 3.3, Table 2 |

The identifier E1179 refers to the equation $x^4 + x + y^3 - y^2 + 4 = 0$, which is obtained by replacing $y$ by $-y$.

## Files

- [H34_01.pdf](H34_01.pdf): a self-contained proof.
- [H34_01.tex](H34_01.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It is self-contained and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`.
