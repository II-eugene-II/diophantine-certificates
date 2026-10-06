# H32_01 (E0150)

$$y^3 - y = x^4 + 2x - 2$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 32$ |
| Length | $l = 11$ |
| Method | Quadratic norm |
| Paper | Table 1; Section 3.1 |

The identifier E0150 refers to the equation $x^4 + 2x + y^3 - y - 2 = 0$, which is obtained by replacing $y$ by $-y$.

## Files

- [H32_01.pdf](H32_01.pdf): a self-contained proof.
- [H32_01.tex](H32_01.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It is self-contained and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`.
