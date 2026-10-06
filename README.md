# Diophantine certificates

Certificates, self-contained proofs and Lean formalisations for the paper

> Bogdan Grechuk and Eugene Go, *Certifying non-existence of integer points on curves*, arXiv:XXXX.XXXXX.

Every equation below has **no integer solutions**. For each equation there is

- a self-contained proof in PDF, and
- a proof in Lean 4, with its statement in a separate file of a few lines, ready to be checked with [comparator](https://github.com/leanprover/comparator).

In the tables, the name of an equation links to its folder, which contains all files for this equation. The columns *Proof* and *Lean* link directly to the PDF proof and to the Lean proof.

## Equations of size h ≤ 34

The two-variable equations of size $h \le 34$ for which it was open whether they have integer solutions (Table 1 of the paper).

| Name | Equation | $h$ | $l$ | Method | Proof | Lean |
|---|---|---|---|---|---|---|
| [H32_01](h_le_34/H32_01) (E0150) | $y^3 - y = x^4 + 2x - 2$ | 32 | 11 | Quadratic norm | [PDF](h_le_34/H32_01/H32_01.pdf) | [Lean](h_le_34/H32_01/Solution.lean) |
| [H33_01](h_le_34/H33_01) (E0258) | $y^3 + y^2 + xy = x^4 + 1$ | 33 | 11 | Quadratic norm | [PDF](h_le_34/H33_01/H33_01.pdf) | [Lean](h_le_34/H33_01/Solution.lean) |
| [H34_01](h_le_34/H34_01) (E1179) | $y^3 + y^2 = x^4 + x + 4$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/H34_01/H34_01.pdf) | [Lean](h_le_34/H34_01/Solution.lean) |
| [H34_16](h_le_34/H34_16) (E1154) | $y^3 - y^2 + y = x^4 + x + 2$ | 34 | 12 | Cubic graph | [PDF](h_le_34/H34_16/H34_16.pdf) | [Lean](h_le_34/H34_16/Solution.lean) |

## Equations of length l ≤ 12

Two-variable equations of size $h > 35$ and length $l \le 12$ (Section 6 of the paper).

| Name | Equation | $h$ | $l$ | Method | Proof | Lean |
|---|---|---|---|---|---|---|
| [E0037](l_le_12/E0037) | $2y^3 + xy + x^4 + 1 = 0$ | 37 | 10 | Quadratic norm | [PDF](l_le_12/E0037/E0037.pdf) | [Lean](l_le_12/E0037/Solution.lean) |

## Contents of a folder

```
h_le_34/H32_01/
├── README.md         the equation, its size and length, the method and the reference to the paper
├── H32_01.pdf        a self-contained proof
├── H32_01.tex        the LaTeX source of the PDF
├── Challenge.lean    the statement in Lean, with the proof replaced by sorry
├── Solution.lean     the proof in Lean, which needs only Mathlib
└── comparator.json   configuration of comparator
```

To trust a Lean proof, it is enough to read its `Challenge.lean`: comparator checks that `Solution.lean` proves exactly this statement, using only the standard axioms of Lean.

The Lean files are written for Lean 4.34.0 and the version of Mathlib fixed in `lakefile.toml`.

## Size, length and names

If the polynomial $P(x,y)$ consists of monomials with integer coefficients $a_1,\dots,a_k$ and degrees $d_1,\dots,d_k$, then the size and the length of the equation $P(x,y)=0$ are

$$h(P)=\sum_{i=1}^k |a_i|\,2^{d_i},\qquad l(P)=\sum_{i=1}^k \bigl(\log_2|a_i|+d_i\bigr).$$

An equation of size $h \le 35$ is named `Hh_k`, where the equations of size $h$ are numbered in the order of the tables of the paper. An equation of size $h > 35$ and length $l \le 12$ is named by its identifier `Exxxx` in the database of equations ordered by length. For an equation of size $h \le 35$ and length $l \le 12$, this identifier is given in parentheses. An identifier may refer to the equation with $y$ replaced by $-y$; the README of each folder says when this is the case.

## Use of AI

The certificates were found by computer search, and the Lean proofs were written with the help of AI tools. The correctness of the results does not depend on these tools, because every proof is checked by the Lean kernel.

## Citation

```bibtex
@misc{GrechukGo,
  author        = {Bogdan Grechuk and Eugene Go},
  title         = {Certifying non-existence of integer points on curves},
  year          = {2026},
  eprint        = {XXXX.XXXXX},
  archivePrefix = {arXiv},
  primaryClass  = {math.NT}
}
```
