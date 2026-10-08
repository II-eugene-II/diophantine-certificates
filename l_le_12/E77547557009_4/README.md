# E77547557009_4

$$x^4+xy+4y^3-2=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 54$ |
| Length | $l = 12$ |
| Method | Quartic graph |

## Outline of the proof

The proof uses the quartic Hilbert reciprocity law over the field $K=\mathbb{Q}(i)$. To a hypothetical integer solution we attach the values of 43 auxiliary polynomials $H_0,\dots,H_{42}$ with coefficients in $\mathbb{Z}[i]$, constants $c_0,\dots,c_{42}\in\mathbb{Z}[i]$, and a sum $B$ of quartic Hilbert symbols of these values, recorded by a graph with 164 weighted edges. By the reciprocity law, the local contributions $B_p$ of all primes $p$ add up to $0$ modulo $4$. We show that $B_p=0$ for $p\notin S$, compute $B_p$ for the primes $p\in S$, and obtain a contradiction. Two standard facts from class field theory are quoted without proof: the explicit formula for the quartic Hilbert symbol at the places not above $2$, and the Hilbert reciprocity law. Apart from these, the proof uses polynomial identities, which can be checked by expanding both sides, and finite computations with residues.

The complete proof, with all the identities and tables that it uses, is in [E77547557009_4.pdf](E77547557009_4.pdf) (12 pages).

## Files

- [E77547557009_4.pdf](E77547557009_4.pdf): a self-contained proof.
- [E77547557009_4.tex](E77547557009_4.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E77547557009_4.Challenge l_le_12.E77547557009_4.Solution
lake env /path/to/comparator l_le_12/E77547557009_4/comparator.json
```

[Back to the list of equations](../../README.md)
