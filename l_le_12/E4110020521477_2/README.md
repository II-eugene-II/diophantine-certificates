# E4110020521477_2

$$2x^4+xy+4y^3-1=0$$

This equation has **no integer solutions**.

| | |
|---|---|
| Size | $h = 69$ |
| Length | $l = 12$ |
| Method | Graph of order 8 |

## Outline of the proof

Replacing $y$ by $-y$, the equation becomes $4y^3+xy-2x^4+1=0$. The proof uses one reciprocity graph of Hilbert symbols of order 8 over $\mathbb{Q}(\zeta_8)$. It has 824 representative lines, which together with their Galois conjugates give 3296 lines, and 42512 weighted edges at 26615 anchor points. The graph defines a class $\mathcal{A}$ in the Brauer group of the curve. Its properties:

- The class is unramified.
- Its local invariants vanish at the odd primes outside $S$, where $S$ is a set of 28 primes up to 457.
- On the integral points, the invariants are $\frac12$ at $13$, $17$ and $137$ and $0$ at the other primes of $S$, except at $19$.
- At $19$, the values are such that the sum of all the invariants is never $0$.

Besides the Hilbert reciprocity law and the explicit formula for tame Hilbert symbols, the PDF quotes standard facts on Brauer groups of curves and of their regular models over $\mathbb{Z}_p$: residues and corestriction, purity, the reciprocity law for residues on a curve, the description of the local evaluation maps by the Tate pairing, and Raynaud's description of the Néron model of the Jacobian. The finite computations were carried out with exact arithmetic.

The proof is in [E4110020521477_2.pdf](E4110020521477_2.pdf) (154 pages). Besides the graph, it lists all the data used in the finite computations: the generators of the $S$-units, the lines and their constants, the stars at the anchors, the 8th-root witnesses of the vertex identities, and the local values.

## Files

- [E4110020521477_2.pdf](E4110020521477_2.pdf): the proof.
- [E4110020521477_2.tex](E4110020521477_2.tex): the LaTeX source of the PDF.
- [Challenge.lean](Challenge.lean): the statement in Lean, with the proof replaced by `sorry`.
- [Solution.lean](Solution.lean): the proof in Lean. It does not depend on other files of this repository and needs only Mathlib. It proves the reciprocity law it uses within the file, and it replaces the facts on Brauer groups quoted in the PDF by explicit computations. The file is large (about 95 MB).
- [comparator.json](comparator.json): configuration of [comparator](https://github.com/leanprover/comparator), which checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.

## Checking the Lean proof

From the root of the repository:

```
lake exe cache get
lake build l_le_12.E4110020521477_2.Challenge l_le_12.E4110020521477_2.Solution
lake env /path/to/comparator l_le_12/E4110020521477_2/comparator.json
```

[Back to the list of equations](../../README.md)
