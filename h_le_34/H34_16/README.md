# H34_16 (E1154)

$$y^3 - y^2 + y = x^4 + x + 2$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 34$ |
| Length | $l = 12$ |
| Method | Cubic reciprocity graph over $\mathbb Q(\omega)$, with 20 vertices and 58 edges |
| Paper | Table 1; Section 3.3; the complete proof is in Section 5.9 |

The identifier E1154 refers to the equation $x^4 + x + y^3 + y^2 + y + 2 = 0$, which is obtained by replacing $y$ by $-y$.

## Files

- [H34_16.pdf](H34_16.pdf): a self-contained proof.
- [H34_16.tex](H34_16.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It is self-contained and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`.
