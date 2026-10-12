# E775475570090_1

$$x^4+xy+4y^3+y+1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 55$ |
| Length | $l = 12$ |
| Method | Cubic graph and graph of order 8 |

## Outline of the proof

Replacing $y$ by $-y$, the equation becomes $4y^3+xy+y=x^4+1$. The proof uses two reciprocity graphs.

- A graph of cubic Hilbert symbols over $\mathbb{Q}(\omega)$, $\omega^2+\omega+1=0$, with 76 auxiliary lines and 542 weighted edges, shows that every integer solution satisfies $(x,y) \bmod 7 \in \{(0,4),(0,5),(2,2),(4,6)\}$.
- A graph of Hilbert symbols of order 8 over $\mathbb{Q}(\zeta_8)$, with 77 auxiliary lines and 519 weighted edges, defines a class $\mathcal{A}$ in the Brauer group of the curve. The class is unramified, its local invariants vanish at the primes outside $S=\{2,3,5,7,11,13,17,41,73\}$, and their values at the primes of $S$ cannot add up to $0$ on the four residue classes modulo 7.

Besides the Hilbert reciprocity law and the explicit formula for tame Hilbert symbols, the PDF quotes standard facts on Brauer groups of curves: residues and corestriction, purity, and the description of the local evaluation maps by the Tate pairing. The finite computations were carried out with exact arithmetic.

The proof is in [E775475570090_1.pdf](E775475570090_1.pdf) (25 pages). Besides the two graphs, it lists all the data used in the finite computations: the cube and eighth roots of the vertex identities, the resultants, the Frobenius checks, the residue classes and the local values.

## Files

- [E775475570090_1.pdf](E775475570090_1.pdf): the proof.
- [E775475570090_1.tex](E775475570090_1.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib. It proves the reciprocity laws it uses within the file, and it replaces the facts on Brauer groups quoted in the PDF by explicit computations. The file is large (about 58 MB), and checking it takes about 12 hours.
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E775475570090_1.Challenge l_le_12.E775475570090_1.Solution
lake env /path/to/comparator l_le_12/E775475570090_1/comparator.json
```

[Back to the list of equations](../../README.md)
