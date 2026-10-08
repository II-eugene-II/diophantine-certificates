# Diophantine certificates

Certificates, self-contained proofs and Lean formalisations for the paper

> Bogdan Grechuk and Eugene Go, *Certifying non-existence of integer points on curves*, arXiv:XXXX.XXXXX.

Each of the 208 equations in this repository has **no integer solutions**. These are all the equations which the paper proves to have no integer solutions. For each equation there is

- a self-contained proof in PDF, together with its LaTeX source, and
- a proof in Lean 4, with its statement in a separate file of a few lines, ready to be checked with [comparator](https://github.com/leanprover/comparator).

## Equations

| Folder | Equations | Number |
|---|---|---:|
| [h_le_34](#equations-of-size-h--34) | size $h \le 34$: the two-variable equations which were open | 30 |
| [h_eq_35](#equations-of-size-h--35) | size $h = 35$ | 41 |
| [l_le_12](#equations-of-length-l--12) | size $h > 35$ and length $l \le 12$ | 137 |
| | **total** | **208** |

The certificates are of two kinds.

- **Quadratic norm.** One or several identities which express a multiple of an auxiliary polynomial $H(x,y)$ as a quadratic norm $U^2 + dV^2$ modulo the equation. Quadratic reciprocity then shows that $H$ cannot take the required values.
- **Reciprocity graphs.** A graph whose vertices are auxiliary polynomials and whose edges carry Hilbert symbols over $K = \mathbb{Q}$, $\mathbb{Q}(\omega)$ or $\mathbb{Q}(i)$, of degree $n = 2$, $3$ or $4$. The Hilbert reciprocity law fails at every integer point of the curve. Some equations use several graphs over different fields.

| Method | $h \le 34$ | $h = 35$ | $l \le 12$ | Total |
|---|---:|---:|---:|---:|
| Quadratic norm | 25 | 38 | 90 | 153 |
| Quadratic graph ($\mathbb{Q}$, $n=2$) |  |  | 21 | 21 |
| Cubic graph ($\mathbb{Q}(\omega)$, $n=3$) | 2 | 2 | 17 | 21 |
| Quartic graph ($\mathbb{Q}(i)$, $n=4$) |  | 1 | 5 | 6 |
| Cubic and quadratic graphs | 3 |  | 3 | 6 |
| Quartic and quadratic graphs |  |  | 1 | 1 |
| **Total** | **30** | **41** | **137** | **208** |

In the tables below, the name of an equation links to its folder, which contains all files for this equation. The columns *Proof* and *Lean* link directly to the PDF proof and to the Lean proof. The equations are ordered by $h$ and then by $l$, except in the last table, where they are ordered by $l$ and then by $h$.

<!-- References to the sections of the paper can be added when the paper is final. -->

### Equations of size h ≤ 34

The 30 two-variable equations of size $h \le 34$ for which it was open whether they have integer solutions. Their list was published in [Grechuk and Wilcox, *Polynomial Diophantine equations: a systematic approach*, Springer, 2024].

| Name | Equation | $h$ | $l$ | Method | Proof | Lean |
|---|---|---:|---:|---|---|---|
| [E49131_20](h_le_34/E49131_20) | $x^4+2x+y^3-y-2=0$ | 32 | 11 | Quadratic norm | [PDF](h_le_34/E49131_20/E49131_20.pdf) | [Lean](h_le_34/E49131_20/Solution.lean) |
| [E1310160_1](h_le_34/E1310160_1) | $x^4+x+y^3+y+4=0$ | 32 | 11 | Quadratic norm | [PDF](h_le_34/E1310160_1/E1310160_1.pdf) | [Lean](h_le_34/E1310160_1/Solution.lean) |
| [E851604_1](h_le_34/E851604_1) | $x^4+xy+x+y^3+2=0$ | 32 | 11 | Quadratic norm | [PDF](h_le_34/E851604_1/E851604_1.pdf) | [Lean](h_le_34/E851604_1/Solution.lean) |
| [E1135472_1](h_le_34/E1135472_1) | $x^4+xy+y^3+4=0$ | 32 | 11 | Quadratic norm | [PDF](h_le_34/E1135472_1/E1135472_1.pdf) | [Lean](h_le_34/E1135472_1/Solution.lean) |
| [E141934_23](h_le_34/E141934_23) | $x^4+xy+y^3-y^2+1=0$ | 33 | 11 | Quadratic norm | [PDF](h_le_34/E141934_23/E141934_23.pdf) | [Lean](h_le_34/E141934_23/Solution.lean) |
| [E709670_3](h_le_34/E709670_3) | $x^4+xy-x+y^3+y+1=0$ | 33 | 11 | Quadratic norm | [PDF](h_le_34/E709670_3/E709670_3.pdf) | [Lean](h_le_34/E709670_3/Solution.lean) |
| [E1703208_1](h_le_34/E1703208_1) | $x^4+xy+x+y^3+3=0$ | 33 | 11.58 | Quadratic norm | [PDF](h_le_34/E1703208_1/E1703208_1.pdf) | [Lean](h_le_34/E1703208_1/Solution.lean) |
| [E212901_8](h_le_34/E212901_8) | $x^4+xy+x+y^3-3=0$ | 33 | 11.58 | Quadratic norm | [PDF](h_le_34/E212901_8/E212901_8.pdf) | [Lean](h_le_34/E212901_8/Solution.lean) |
| [E70967_24](h_le_34/E70967_24) | $x^4+xy-x+y^3-3=0$ | 33 | 11.58 | Quadratic norm | [PDF](h_le_34/E70967_24/E70967_24.pdf) | [Lean](h_le_34/E70967_24/Solution.lean) |
| [E98880_53](h_le_34/E98880_53) | $-x^4+x+y^3+y+6=0$ | 34 | 11.58 | Quadratic norm | [PDF](h_le_34/E98880_53/E98880_53.pdf) | [Lean](h_le_34/E98880_53/Solution.lean) |
| [E5240640_1](h_le_34/E5240640_1) | $x^4+x+y^3+y+6=0$ | 34 | 11.58 | Quadratic norm | [PDF](h_le_34/E5240640_1/E5240640_1.pdf) | [Lean](h_le_34/E5240640_1/Solution.lean) |
| [E85284_53](h_le_34/E85284_53) | $-x^4+2x+y^3+y^2+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E85284_53/E85284_53.pdf) | [Lean](h_le_34/E85284_53/Solution.lean) |
| [E3930480_1](h_le_34/E3930480_1) | $x^4+2x+y^3+y+4=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E3930480_1/E3930480_1.pdf) | [Lean](h_le_34/E3930480_1/Solution.lean) |
| [E245655_16](h_le_34/E245655_16) | $x^4+2x+y^3+y-4=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E245655_16/E245655_16.pdf) | [Lean](h_le_34/E245655_16/Solution.lean) |
| [E4520052_1](h_le_34/E4520052_1) | $x^4+2x+y^3+y^2+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E4520052_1/E4520052_1.pdf) | [Lean](h_le_34/E4520052_1/Solution.lean) |
| [E6550800_1](h_le_34/E6550800_1) | $x^4+x+y^3+2y+4=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E6550800_1/E6550800_1.pdf) | [Lean](h_le_34/E6550800_1/Solution.lean) |
| [E7533420_1](h_le_34/E7533420_1) | $x^4+x+y^3+y^2+y+2=0$ | 34 | 12 | Cubic graph | [PDF](h_le_34/E7533420_1/E7533420_1.pdf) | [Lean](h_le_34/E7533420_1/Solution.lean) |
| [E262032_23](h_le_34/E262032_23) | $x^4+x+y^3-y^2+4=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E262032_23/E262032_23.pdf) | [Lean](h_le_34/E262032_23/Solution.lean) |
| [E327540_23](h_le_34/E327540_23) | $x^4+x+y^3-y^2+y+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E327540_23/E327540_23.pdf) | [Lean](h_le_34/E327540_23/Solution.lean) |
| [E65508_115](h_le_34/E65508_115) | $x^4+x+y^3-y^2-y+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E65508_115/E65508_115.pdf) | [Lean](h_le_34/E65508_115/Solution.lean) |
| [E1987076_1](h_le_34/E1987076_1) | $x^4+x^2+xy+y^3+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E1987076_1/E1987076_1.pdf) | [Lean](h_le_34/E1987076_1/Solution.lean) |
| [E3406416_1](h_le_34/E3406416_1) | $x^4+xy+x+y^3+4=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E3406416_1/E3406416_1.pdf) | [Lean](h_le_34/E3406416_1/Solution.lean) |
| [E851604_5](h_le_34/E851604_5) | $x^4+xy+x+y^3-y+2=0$ | 34 | 12 | Cubic graph | [PDF](h_le_34/E851604_5/E851604_5.pdf) | [Lean](h_le_34/E851604_5/Solution.lean) |
| [E5677360_1](h_le_34/E5677360_1) | $x^4+xy+y^3+y+4=0$ | 34 | 12 | Cubic and quadratic graphs | [PDF](h_le_34/E5677360_1/E5677360_1.pdf) | [Lean](h_le_34/E5677360_1/Solution.lean) |
| [E6528964_1](h_le_34/E6528964_1) | $x^4+xy+y^3+y^2+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E6528964_1/E6528964_1.pdf) | [Lean](h_le_34/E6528964_1/Solution.lean) |
| [E1135472_5](h_le_34/E1135472_5) | $x^4+xy+y^3-y+4=0$ | 34 | 12 | Cubic and quadratic graphs | [PDF](h_le_34/E1135472_5/E1135472_5.pdf) | [Lean](h_le_34/E1135472_5/Solution.lean) |
| [E70967_80](h_le_34/E70967_80) | $x^4+xy+y^3-y-4=0$ | 34 | 12 | Cubic and quadratic graphs | [PDF](h_le_34/E70967_80/E70967_80.pdf) | [Lean](h_le_34/E70967_80/Solution.lean) |
| [E70967_48](h_le_34/E70967_48) | $x^4+xy-x+y^3-4=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E70967_48/E70967_48.pdf) | [Lean](h_le_34/E70967_48/Solution.lean) |
| [E65508_35](h_le_34/E65508_35) | $x^4-x^2+x+y^3-y+2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E65508_35/E65508_35.pdf) | [Lean](h_le_34/E65508_35/Solution.lean) |
| [E16377_140](h_le_34/E16377_140) | $x^4-x^2+x+y^3-y-2=0$ | 34 | 12 | Quadratic norm | [PDF](h_le_34/E16377_140/E16377_140.pdf) | [Lean](h_le_34/E16377_140/Solution.lean) |

### Equations of size h = 35

The two-variable equations of size $h = 35$.

| Name | Equation | $h$ | $l$ | Method | Proof | Lean |
|---|---|---:|---:|---|---|---|
| [E17326866_1](h_eq_35/E17326866_1) | $x^4+x+y^3+2y^2+1=0$ | 35 | 11 | Quadratic norm | [PDF](h_eq_35/E17326866_1/E17326866_1.pdf) | [Lean](h_eq_35/E17326866_1/Solution.lean) |
| [E20471250_1](h_eq_35/E20471250_1) | $x^4+x+y^3+4y+1=0$ | 35 | 11 | Quadratic norm | [PDF](h_eq_35/E20471250_1/E20471250_1.pdf) | [Lean](h_eq_35/E20471250_1/Solution.lean) |
| [E10235625_2](h_eq_35/E10235625_2) | $x^4+x+y^3+4y-1=0$ | 35 | 11 | Quadratic norm | [PDF](h_eq_35/E10235625_2/E10235625_2.pdf) | [Lean](h_eq_35/E10235625_2/Solution.lean) |
| [E6141375_2](h_eq_35/E6141375_2) | $x^4+2x+y^3+3y-1=0$ | 35 | 11.58 | Quadratic norm | [PDF](h_eq_35/E6141375_2/E6141375_2.pdf) | [Lean](h_eq_35/E6141375_2/Solution.lean) |
| [E922571_8](h_eq_35/E922571_8) | $x^4+2xy+y^3-3=0$ | 35 | 11.58 | Quadratic norm | [PDF](h_eq_35/E922571_8/E922571_8.pdf) | [Lean](h_eq_35/E922571_8/Solution.lean) |
| [E9083776_1](h_eq_35/E9083776_1) | $x^4+xy+y^3+7=0$ | 35 | 11.81 | Quadratic norm | [PDF](h_eq_35/E9083776_1/E9083776_1.pdf) | [Lean](h_eq_35/E9083776_1/Solution.lean) |
| [E5650065_2](h_eq_35/E5650065_2) | $x^4+2x+y^3+y^2+y-1=0$ | 35 | 12 | Quadratic norm | [PDF](h_eq_35/E5650065_2/E5650065_2.pdf) | [Lean](h_eq_35/E5650065_2/Solution.lean) |
| [E993538_5](h_eq_35/E993538_5) | $x^4+x^2+xy+y^3-y+1=0$ | 35 | 12 | Quadratic norm | [PDF](h_eq_35/E993538_5/E993538_5.pdf) | [Lean](h_eq_35/E993538_5/Solution.lean) |
| [E10645050_1](h_eq_35/E10645050_1) | $x^4+xy+x+y^3+2y+1=0$ | 35 | 12 | Quadratic norm | [PDF](h_eq_35/E10645050_1/E10645050_1.pdf) | [Lean](h_eq_35/E10645050_1/Solution.lean) |
| [E5322525_2](h_eq_35/E5322525_2) | $x^4+xy+x+y^3+2y-1=0$ | 35 | 12 | Quadratic norm | [PDF](h_eq_35/E5322525_2/E5322525_2.pdf) | [Lean](h_eq_35/E5322525_2/Solution.lean) |
| [E3548350_3](h_eq_35/E3548350_3) | $x^4+xy-x+y^3+2y+1=0$ | 35 | 12 | Quadratic norm | [PDF](h_eq_35/E3548350_3/E3548350_3.pdf) | [Lean](h_eq_35/E3548350_3/Solution.lean) |
| [E1774175_6](h_eq_35/E1774175_6) | $x^4+xy-x+y^3+2y-1=0$ | 35 | 12 | Quadratic norm | [PDF](h_eq_35/E1774175_6/E1774175_6.pdf) | [Lean](h_eq_35/E1774175_6/Solution.lean) |
| [E128544_53](h_eq_35/E128544_53) | $-x^4+xy+x+y^3+5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E128544_53/E128544_53.pdf) | [Lean](h_eq_35/E128544_53/Solution.lean) |
| [E7860960_1](h_eq_35/E7860960_1) | $x^4+2x+y^3+y+5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E7860960_1/E7860960_1.pdf) | [Lean](h_eq_35/E7860960_1/Solution.lean) |
| [E524064_25](h_eq_35/E524064_25) | $x^4+x+y^3-2y+5=0$ | 35 | 12.32 | Cubic graph | [PDF](h_eq_35/E524064_25/E524064_25.pdf) | [Lean](h_eq_35/E524064_25/Solution.lean) |
| [E16377_800](h_eq_35/E16377_800) | $x^4+x+y^3-2y-5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E16377_800/E16377_800.pdf) | [Lean](h_eq_35/E16377_800/Solution.lean) |
| [E6812832_1](h_eq_35/E6812832_1) | $x^4+xy+x+y^3+5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E6812832_1/E6812832_1.pdf) | [Lean](h_eq_35/E6812832_1/Solution.lean) |
| [E212901_32](h_eq_35/E212901_32) | $x^4+xy+x+y^3-5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E212901_32/E212901_32.pdf) | [Lean](h_eq_35/E212901_32/Solution.lean) |
| [E354835_32](h_eq_35/E354835_32) | $x^4+xy+y^3+y-5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E354835_32/E354835_32.pdf) | [Lean](h_eq_35/E354835_32/Solution.lean) |
| [E2270944_3](h_eq_35/E2270944_3) | $x^4+xy-x+y^3+5=0$ | 35 | 12.32 | Quadratic norm | [PDF](h_eq_35/E2270944_3/E2270944_3.pdf) | [Lean](h_eq_35/E2270944_3/Solution.lean) |
| [E56856_265](h_eq_35/E56856_265) | $-x^4+x+y^3+y^2-y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E56856_265/E56856_265.pdf) | [Lean](h_eq_35/E56856_265/Solution.lean) |
| [E17304_265](h_eq_35/E17304_265) | $-x^4+x^2+x+y^3-y+3=0$ | 35 | 12.58 | Quartic graph | [PDF](h_eq_35/E17304_265/E17304_265.pdf) | [Lean](h_eq_35/E17304_265/Solution.lean) |
| [E74984_53](h_eq_35/E74984_53) | $-x^4+x^2+xy+y^3+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E74984_53/E74984_53.pdf) | [Lean](h_eq_35/E74984_53/Solution.lean) |
| [E9040104_1](h_eq_35/E9040104_1) | $x^4+2x+y^3+y^2+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E9040104_1/E9040104_1.pdf) | [Lean](h_eq_35/E9040104_1/Solution.lean) |
| [E393048_25](h_eq_35/E393048_25) | $x^4+2x+y^3-2y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E393048_25/E393048_25.pdf) | [Lean](h_eq_35/E393048_25/Solution.lean) |
| [E3013368_5](h_eq_35/E3013368_5) | $x^4+x+y^3+y^2-y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E3013368_5/E3013368_5.pdf) | [Lean](h_eq_35/E3013368_5/Solution.lean) |
| [E131016_115](h_eq_35/E131016_115) | $x^4+x+y^3-y^2-y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E131016_115/E131016_115.pdf) | [Lean](h_eq_35/E131016_115/Solution.lean) |
| [E4585560_1](h_eq_35/E4585560_1) | $x^4+x^2+x+y^3+y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E4585560_1/E4585560_1.pdf) | [Lean](h_eq_35/E4585560_1/Solution.lean) |
| [E3974152_1](h_eq_35/E3974152_1) | $x^4+x^2+xy+y^3+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E3974152_1/E3974152_1.pdf) | [Lean](h_eq_35/E3974152_1/Solution.lean) |
| [E496769_8](h_eq_35/E496769_8) | $x^4+x^2+xy+y^3-3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E496769_8/E496769_8.pdf) | [Lean](h_eq_35/E496769_8/Solution.lean) |
| [E5109624_1](h_eq_35/E5109624_1) | $x^4+xy+2x+y^3+3=0$ | 35 | 12.58 | Cubic graph | [PDF](h_eq_35/E5109624_1/E5109624_1.pdf) | [Lean](h_eq_35/E5109624_1/Solution.lean) |
| [E8516040_1](h_eq_35/E8516040_1) | $x^4+xy+x+y^3+y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E8516040_1/E8516040_1.pdf) | [Lean](h_eq_35/E8516040_1/Solution.lean) |
| [E1064505_8](h_eq_35/E1064505_8) | $x^4+xy+x+y^3+y-3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E1064505_8/E1064505_8.pdf) | [Lean](h_eq_35/E1064505_8/Solution.lean) |
| [E1703208_5](h_eq_35/E1703208_5) | $x^4+xy+x+y^3-y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E1703208_5/E1703208_5.pdf) | [Lean](h_eq_35/E1703208_5/Solution.lean) |
| [E13057928_1](h_eq_35/E13057928_1) | $x^4+xy+y^3+y^2+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E13057928_1/E13057928_1.pdf) | [Lean](h_eq_35/E13057928_1/Solution.lean) |
| [E1632241_8](h_eq_35/E1632241_8) | $x^4+xy+y^3+y^2-3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E1632241_8/E1632241_8.pdf) | [Lean](h_eq_35/E1632241_8/Solution.lean) |
| [E567736_25](h_eq_35/E567736_25) | $x^4+xy+y^3-2y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E567736_25/E567736_25.pdf) | [Lean](h_eq_35/E567736_25/Solution.lean) |
| [E567736_23](h_eq_35/E567736_23) | $x^4+xy+y^3-y^2+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E567736_23/E567736_23.pdf) | [Lean](h_eq_35/E567736_23/Solution.lean) |
| [E567736_15](h_eq_35/E567736_15) | $x^4+xy-x+y^3-y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E567736_15/E567736_15.pdf) | [Lean](h_eq_35/E567736_15/Solution.lean) |
| [E131016_35](h_eq_35/E131016_35) | $x^4-x^2+x+y^3-y+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E131016_35/E131016_35.pdf) | [Lean](h_eq_35/E131016_35/Solution.lean) |
| [E567736_7](h_eq_35/E567736_7) | $x^4-x^2+xy+y^3+3=0$ | 35 | 12.58 | Quadratic norm | [PDF](h_eq_35/E567736_7/E567736_7.pdf) | [Lean](h_eq_35/E567736_7/Solution.lean) |

### Equations of length l ≤ 12

The two-variable equations of size $h > 35$ and length $l \le 12$.

| Name | Equation | $h$ | $l$ | Method | Proof | Lean |
|---|---|---:|---:|---|---|---|
| [E14619202_1](l_le_12/E14619202_1) | $x^4+xy+2y^3+1=0$ | 37 | 10 | Quadratic norm | [PDF](l_le_12/E14619202_1/E14619202_1.pdf) | [Lean](l_le_12/E14619202_1/Solution.lean) |
| [E6747324_5](l_le_12/E6747324_5) | $x^4+x+2y^3-y+2=0$ | 38 | 11 | Quadratic norm | [PDF](l_le_12/E6747324_5/E6747324_5.pdf) | [Lean](l_le_12/E6747324_5/Solution.lean) |
| [E14619202_3](l_le_12/E14619202_3) | $x^4+xy-x+2y^3+1=0$ | 39 | 11 | Quadratic norm | [PDF](l_le_12/E14619202_3/E14619202_3.pdf) | [Lean](l_le_12/E14619202_3/Solution.lean) |
| [E3471924_5](l_le_12/E3471924_5) | $2x^4+x+y^3-y+2=0$ | 46 | 11 | Cubic and quadratic graphs | [PDF](l_le_12/E3471924_5/E3471924_5.pdf) | [Lean](l_le_12/E3471924_5/Solution.lean) |
| [E15045004_1](l_le_12/E15045004_1) | $2x^4+xy+y^3+2=0$ | 46 | 11 | Quadratic norm | [PDF](l_le_12/E15045004_1/E15045004_1.pdf) | [Lean](l_le_12/E15045004_1/Solution.lean) |
| [E7522502_5](l_le_12/E7522502_5) | $2x^4+xy+y^3-y+1=0$ | 47 | 11 | Quadratic norm | [PDF](l_le_12/E7522502_5/E7522502_5.pdf) | [Lean](l_le_12/E7522502_5/Solution.lean) |
| [E178955900790_1](l_le_12/E178955900790_1) | $x^4+x+4y^3+y+1=0$ | 53 | 11 | Quadratic norm | [PDF](l_le_12/E178955900790_1/E178955900790_1.pdf) | [Lean](l_le_12/E178955900790_1/Solution.lean) |
| [E89477950395_2](l_le_12/E89477950395_2) | $x^4+x+4y^3+y-1=0$ | 53 | 11 | Quadratic norm | [PDF](l_le_12/E89477950395_2/E89477950395_2.pdf) | [Lean](l_le_12/E89477950395_2/Solution.lean) |
| [E155095114018_1](l_le_12/E155095114018_1) | $x^4+xy+4y^3+1=0$ | 53 | 11 | Quadratic norm | [PDF](l_le_12/E155095114018_1/E155095114018_1.pdf) | [Lean](l_le_12/E155095114018_1/Solution.lean) |
| [E24381586290_1](l_le_12/E24381586290_1) | $4x^4+x+y^3+y+1=0$ | 77 | 11 | Cubic graph | [PDF](l_le_12/E24381586290_1/E24381586290_1.pdf) | [Lean](l_le_12/E24381586290_1/Solution.lean) |
| [E15974796743854_1](l_le_12/E15974796743854_1) | $x^4+xy+5y^3+1=0$ | 61 | 11.32 | Quadratic norm | [PDF](l_le_12/E15974796743854_1/E15974796743854_1.pdf) | [Lean](l_le_12/E15974796743854_1/Solution.lean) |
| [E39796110_1](l_le_12/E39796110_1) | $x^4+6x+y^3+y+1=0$ | 39 | 11.58 | Quadratic norm | [PDF](l_le_12/E39796110_1/E39796110_1.pdf) | [Lean](l_le_12/E39796110_1/Solution.lean) |
| [E19898055_2](l_le_12/E19898055_2) | $x^4+6x+y^3+y-1=0$ | 39 | 11.58 | Quadratic norm | [PDF](l_le_12/E19898055_2/E19898055_2.pdf) | [Lean](l_le_12/E19898055_2/Solution.lean) |
| [E13494648_5](l_le_12/E13494648_5) | $x^4+x+2y^3-y+3=0$ | 39 | 11.58 | Quartic graph | [PDF](l_le_12/E13494648_5/E13494648_5.pdf) | [Lean](l_le_12/E13494648_5/Solution.lean) |
| [E511781250_1](l_le_12/E511781250_1) | $x^4+x+y^3+6y+1=0$ | 39 | 11.58 | Cubic graph | [PDF](l_le_12/E511781250_1/E511781250_1.pdf) | [Lean](l_le_12/E511781250_1/Solution.lean) |
| [E255890625_2](l_le_12/E255890625_2) | $x^4+x+y^3+6y-1=0$ | 39 | 11.58 | Quadratic graph | [PDF](l_le_12/E255890625_2/E255890625_2.pdf) | [Lean](l_le_12/E255890625_2/Solution.lean) |
| [E4968750_103](l_le_12/E4968750_103) | $x^4+x-y^3+6y+1=0$ | 39 | 11.58 | Cubic graph | [PDF](l_le_12/E4968750_103/E4968750_103.pdf) | [Lean](l_le_12/E4968750_103/Solution.lean) |
| [E2484375_206](l_le_12/E2484375_206) | $x^4+x-y^3+6y-1=0$ | 39 | 11.58 | Quadratic norm | [PDF](l_le_12/E2484375_206/E2484375_206.pdf) | [Lean](l_le_12/E2484375_206/Solution.lean) |
| [E58476808_1](l_le_12/E58476808_1) | $x^4+xy+2y^3+3=0$ | 39 | 11.58 | Quadratic norm | [PDF](l_le_12/E58476808_1/E58476808_1.pdf) | [Lean](l_le_12/E58476808_1/Solution.lean) |
| [E7309601_8](l_le_12/E7309601_8) | $x^4+xy+2y^3-3=0$ | 39 | 11.58 | Quadratic graph | [PDF](l_le_12/E7309601_8/E7309601_8.pdf) | [Lean](l_le_12/E7309601_8/Solution.lean) |
| [E421707750_1](l_le_12/E421707750_1) | $x^4+x+2y^3+3y+1=0$ | 41 | 11.58 | Quadratic norm | [PDF](l_le_12/E421707750_1/E421707750_1.pdf) | [Lean](l_le_12/E421707750_1/Solution.lean) |
| [E210853875_2](l_le_12/E210853875_2) | $x^4+x+2y^3+3y-1=0$ | 41 | 11.58 | Quadratic norm | [PDF](l_le_12/E210853875_2/E210853875_2.pdf) | [Lean](l_le_12/E210853875_2/Solution.lean) |
| [E2470645138_1](l_le_12/E2470645138_1) | $x^4+3xy+2y^3+1=0$ | 45 | 11.58 | Quadratic norm | [PDF](l_le_12/E2470645138_1/E2470645138_1.pdf) | [Lean](l_le_12/E2470645138_1/Solution.lean) |
| [E34719240_1](l_le_12/E34719240_1) | $2x^4+x+y^3+y+3=0$ | 47 | 11.58 | Cubic and quadratic graphs | [PDF](l_le_12/E34719240_1/E34719240_1.pdf) | [Lean](l_le_12/E34719240_1/Solution.lean) |
| [E30090008_1](l_le_12/E30090008_1) | $2x^4+xy+y^3+3=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E30090008_1/E30090008_1.pdf) | [Lean](l_le_12/E30090008_1/Solution.lean) |
| [E3761251_8](l_le_12/E3761251_8) | $2x^4+xy+y^3-3=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E3761251_8/E3761251_8.pdf) | [Lean](l_le_12/E3761251_8/Solution.lean) |
| [E2606153895_2](l_le_12/E2606153895_2) | $x^4+2x+3y^3+y-1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E2606153895_2/E2606153895_2.pdf) | [Lean](l_le_12/E2606153895_2/Solution.lean) |
| [E8687179650_1](l_le_12/E8687179650_1) | $x^4+x+3y^3+2y+1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E8687179650_1/E8687179650_1.pdf) | [Lean](l_le_12/E8687179650_1/Solution.lean) |
| [E4343589825_2](l_le_12/E4343589825_2) | $x^4+x+3y^3+2y-1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E4343589825_2/E4343589825_2.pdf) | [Lean](l_le_12/E4343589825_2/Solution.lean) |
| [E4517333418_1](l_le_12/E4517333418_1) | $x^4+xy+x+3y^3+1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E4517333418_1/E4517333418_1.pdf) | [Lean](l_le_12/E4517333418_1/Solution.lean) |
| [E2258666709_2](l_le_12/E2258666709_2) | $x^4+xy+x+3y^3-1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E2258666709_2/E2258666709_2.pdf) | [Lean](l_le_12/E2258666709_2/Solution.lean) |
| [E1505777806_3](l_le_12/E1505777806_3) | $x^4+xy-x+3y^3+1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E1505777806_3/E1505777806_3.pdf) | [Lean](l_le_12/E1505777806_3/Solution.lean) |
| [E752888903_6](l_le_12/E752888903_6) | $x^4+xy-x+3y^3-1=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E752888903_6/E752888903_6.pdf) | [Lean](l_le_12/E752888903_6/Solution.lean) |
| [E1403272_1](l_le_12/E1403272_1) | $x^5+xy+y^3+3=0$ | 47 | 11.58 | Quadratic norm | [PDF](l_le_12/E1403272_1/E1403272_1.pdf) | [Lean](l_le_12/E1403272_1/Solution.lean) |
| [E79806223718_1](l_le_12/E79806223718_1) | $2x^4+xy+3y^3+1=0$ | 61 | 11.58 | Quadratic graph | [PDF](l_le_12/E79806223718_1/E79806223718_1.pdf) | [Lean](l_le_12/E79806223718_1/Solution.lean) |
| [E39903111859_2](l_le_12/E39903111859_2) | $2x^4+xy+3y^3-1=0$ | 61 | 11.58 | Quadratic norm | [PDF](l_le_12/E39903111859_2/E39903111859_2.pdf) | [Lean](l_le_12/E39903111859_2/Solution.lean) |
| [E1993463030_1](l_le_12/E1993463030_1) | $3x^4+xy+y^3+y+1=0$ | 63 | 11.58 | Quadratic norm | [PDF](l_le_12/E1993463030_1/E1993463030_1.pdf) | [Lean](l_le_12/E1993463030_1/Solution.lean) |
| [E41065338418_1](l_le_12/E41065338418_1) | $3x^4+xy+2y^3+1=0$ | 69 | 11.58 | Cubic graph | [PDF](l_le_12/E41065338418_1/E41065338418_1.pdf) | [Lean](l_le_12/E41065338418_1/Solution.lean) |
| [E20532669209_2](l_le_12/E20532669209_2) | $3x^4+xy+2y^3-1=0$ | 69 | 11.58 | Quadratic norm | [PDF](l_le_12/E20532669209_2/E20532669209_2.pdf) | [Lean](l_le_12/E20532669209_2/Solution.lean) |
| [E1898543151481110_1](l_le_12/E1898543151481110_1) | $x^4+x+6y^3+y+1=0$ | 69 | 11.58 | Quadratic norm | [PDF](l_le_12/E1898543151481110_1/E1898543151481110_1.pdf) | [Lean](l_le_12/E1898543151481110_1/Solution.lean) |
| [E949271575740555_2](l_le_12/E949271575740555_2) | $x^4+x+6y^3+y-1=0$ | 69 | 11.58 | Quadratic norm | [PDF](l_le_12/E949271575740555_2/E949271575740555_2.pdf) | [Lean](l_le_12/E949271575740555_2/Solution.lean) |
| [E379708630296222_5](l_le_12/E379708630296222_5) | $x^4+x+6y^3-y+1=0$ | 69 | 11.58 | Quadratic norm | [PDF](l_le_12/E379708630296222_5/E379708630296222_5.pdf) | [Lean](l_le_12/E379708630296222_5/Solution.lean) |
| [E189854315148111_10](l_le_12/E189854315148111_10) | $x^4+x+6y^3-y-1=0$ | 69 | 11.58 | Quadratic norm | [PDF](l_le_12/E189854315148111_10/E189854315148111_10.pdf) | [Lean](l_le_12/E189854315148111_10/Solution.lean) |
| [E1645404064616962_1](l_le_12/E1645404064616962_1) | $x^4+xy+6y^3+1=0$ | 69 | 11.58 | Quadratic norm | [PDF](l_le_12/E1645404064616962_1/E1645404064616962_1.pdf) | [Lean](l_le_12/E1645404064616962_1/Solution.lean) |
| [E68487875888610_1](l_le_12/E68487875888610_1) | $6x^4+x+y^3+y+1=0$ | 109 | 11.58 | Quadratic graph | [PDF](l_le_12/E68487875888610_1/E68487875888610_1.pdf) | [Lean](l_le_12/E68487875888610_1/Solution.lean) |
| [E34243937944305_2](l_le_12/E34243937944305_2) | $6x^4+x+y^3+y-1=0$ | 109 | 11.58 | Cubic graph | [PDF](l_le_12/E34243937944305_2/E34243937944305_2.pdf) | [Lean](l_le_12/E34243937944305_2/Solution.lean) |
| [E169476618655547086_1](l_le_12/E169476618655547086_1) | $x^4+xy+7y^3+1=0$ | 77 | 11.81 | Quadratic graph | [PDF](l_le_12/E169476618655547086_1/E169476618655547086_1.pdf) | [Lean](l_le_12/E169476618655547086_1/Solution.lean) |
| [E11070852_1](l_le_12/E11070852_1) | $x^4+2xy+x+y^3+2=0$ | 36 | 12 | Quadratic norm | [PDF](l_le_12/E11070852_1/E11070852_1.pdf) | [Lean](l_le_12/E11070852_1/Solution.lean) |
| [E34653732_1](l_le_12/E34653732_1) | $x^4+x+y^3+2y^2+2=0$ | 36 | 12 | Quadratic norm | [PDF](l_le_12/E34653732_1/E34653732_1.pdf) | [Lean](l_le_12/E34653732_1/Solution.lean) |
| [E1331996_5](l_le_12/E1331996_5) | $x^4+xy^2+y^3-y+2=0$ | 36 | 12 | Quadratic norm | [PDF](l_le_12/E1331996_5/E1331996_5.pdf) | [Lean](l_le_12/E1331996_5/Solution.lean) |
| [E980766_53](l_le_12/E980766_53) | $-x^4+2x+y^3+2y^2+1=0$ | 37 | 12 | Quadratic norm | [PDF](l_le_12/E980766_53/E980766_53.pdf) | [Lean](l_le_12/E980766_53/Solution.lean) |
| [E30706875_2](l_le_12/E30706875_2) | $x^4+2x+y^3+4y-1=0$ | 37 | 12 | Quadratic norm | [PDF](l_le_12/E30706875_2/E30706875_2.pdf) | [Lean](l_le_12/E30706875_2/Solution.lean) |
| [E22108950_1](l_le_12/E22108950_1) | $x^4+4x+y^3+2y+1=0$ | 37 | 12 | Quadratic norm | [PDF](l_le_12/E22108950_1/E22108950_1.pdf) | [Lean](l_le_12/E22108950_1/Solution.lean) |
| [E884358_23](l_le_12/E884358_23) | $x^4+4x+y^3-y^2+1=0$ | 37 | 12 | Quadratic norm | [PDF](l_le_12/E884358_23/E884358_23.pdf) | [Lean](l_le_12/E884358_23/Solution.lean) |
| [E3029745_2](l_le_12/E3029745_2) | $x^4+x^2y+x+y^3+y-1=0$ | 37 | 12 | Quadratic norm | [PDF](l_le_12/E3029745_2/E3029745_2.pdf) | [Lean](l_le_12/E3029745_2/Solution.lean) |
| [E88708750_1](l_le_12/E88708750_1) | $x^4+xy+y^3+4y+1=0$ | 37 | 12 | Quadratic norm | [PDF](l_le_12/E88708750_1/E88708750_1.pdf) | [Lean](l_le_12/E88708750_1/Solution.lean) |
| [E155188452_1](l_le_12/E155188452_1) | $x^4+x+2y^3+y^2+2=0$ | 40 | 12 | Quadratic norm | [PDF](l_le_12/E155188452_1/E155188452_1.pdf) | [Lean](l_le_12/E155188452_1/Solution.lean) |
| [E26989296_5](l_le_12/E26989296_5) | $x^4+x+2y^3-y+4=0$ | 40 | 12 | Quartic and quadratic graphs | [PDF](l_le_12/E26989296_5/E26989296_5.pdf) | [Lean](l_le_12/E26989296_5/Solution.lean) |
| [E146192020_1](l_le_12/E146192020_1) | $x^4+xy+2y^3+y+2=0$ | 40 | 12 | Quadratic graph | [PDF](l_le_12/E146192020_1/E146192020_1.pdf) | [Lean](l_le_12/E146192020_1/Solution.lean) |
| [E7309601_20](l_le_12/E7309601_20) | $x^4+xy+2y^3-y-2=0$ | 40 | 12 | Quadratic norm | [PDF](l_le_12/E7309601_20/E7309601_20.pdf) | [Lean](l_le_12/E7309601_20/Solution.lean) |
| [E65786409_2](l_le_12/E65786409_2) | $x^4+xy+2x+2y^3-1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E65786409_2/E65786409_2.pdf) | [Lean](l_le_12/E65786409_2/Solution.lean) |
| [E365480050_1](l_le_12/E365480050_1) | $x^4+xy+2y^3+2y+1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E365480050_1/E365480050_1.pdf) | [Lean](l_le_12/E365480050_1/Solution.lean) |
| [E14619202_25](l_le_12/E14619202_25) | $x^4+xy+2y^3-2y+1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E14619202_25/E14619202_25.pdf) | [Lean](l_le_12/E14619202_25/Solution.lean) |
| [E219288030_1](l_le_12/E219288030_1) | $x^4+xy+x+2y^3+y+1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E219288030_1/E219288030_1.pdf) | [Lean](l_le_12/E219288030_1/Solution.lean) |
| [E109644015_2](l_le_12/E109644015_2) | $x^4+xy+x+2y^3+y-1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E109644015_2/E109644015_2.pdf) | [Lean](l_le_12/E109644015_2/Solution.lean) |
| [E7309601_18](l_le_12/E7309601_18) | $x^4+xy-2x+2y^3-1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E7309601_18/E7309601_18.pdf) | [Lean](l_le_12/E7309601_18/Solution.lean) |
| [E73096010_3](l_le_12/E73096010_3) | $x^4+xy-x+2y^3+y+1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E73096010_3/E73096010_3.pdf) | [Lean](l_le_12/E73096010_3/Solution.lean) |
| [E36548005_6](l_le_12/E36548005_6) | $x^4+xy-x+2y^3+y-1=0$ | 41 | 12 | Quadratic norm | [PDF](l_le_12/E36548005_6/E36548005_6.pdf) | [Lean](l_le_12/E36548005_6/Solution.lean) |
| [E155914499_4](l_le_12/E155914499_4) | $x^4+4xy+y^3-2=0$ | 42 | 12 | Quadratic norm | [PDF](l_le_12/E155914499_4/E155914499_4.pdf) | [Lean](l_le_12/E155914499_4/Solution.lean) |
| [E172941738_53](l_le_12/E172941738_53) | $-x^4+x+y^3+4y^2+1=0$ | 43 | 12 | Quadratic norm | [PDF](l_le_12/E172941738_53/E172941738_53.pdf) | [Lean](l_le_12/E172941738_53/Solution.lean) |
| [E455444370_1](l_le_12/E455444370_1) | $x^4+4x+2y^3+y+1=0$ | 43 | 12 | Quadratic graph | [PDF](l_le_12/E455444370_1/E455444370_1.pdf) | [Lean](l_le_12/E455444370_1/Solution.lean) |
| [E179082495_2](l_le_12/E179082495_2) | $x^4+8x+y^3+y-1=0$ | 43 | 12 | Quadratic norm | [PDF](l_le_12/E179082495_2/E179082495_2.pdf) | [Lean](l_le_12/E179082495_2/Solution.lean) |
| [E9165912114_1](l_le_12/E9165912114_1) | $x^4+x+y^3+4y^2+1=0$ | 43 | 12 | Quadratic norm | [PDF](l_le_12/E9165912114_1/E9165912114_1.pdf) | [Lean](l_le_12/E9165912114_1/Solution.lean) |
| [E4582956057_2](l_le_12/E4582956057_2) | $x^4+x+y^3+4y^2-1=0$ | 43 | 12 | Cubic graph | [PDF](l_le_12/E4582956057_2/E4582956057_2.pdf) | [Lean](l_le_12/E4582956057_2/Solution.lean) |
| [E12794531250_1](l_le_12/E12794531250_1) | $x^4+x+y^3+8y+1=0$ | 43 | 12 | Quadratic graph | [PDF](l_le_12/E12794531250_1/E12794531250_1.pdf) | [Lean](l_le_12/E12794531250_1/Solution.lean) |
| [E62109375_206](l_le_12/E62109375_206) | $x^4+x-y^3+8y-1=0$ | 43 | 12 | Quadratic graph | [PDF](l_le_12/E62109375_206/E62109375_206.pdf) | [Lean](l_le_12/E62109375_206/Solution.lean) |
| [E62412747_2](l_le_12/E62412747_2) | $x^4+x^2y+x+2y^3-1=0$ | 43 | 12 | Quadratic norm | [PDF](l_le_12/E62412747_2/E62412747_2.pdf) | [Lean](l_le_12/E62412747_2/Solution.lean) |
| [E79854252_1](l_le_12/E79854252_1) | $2x^4+x+y^3+y^2+2=0$ | 48 | 12 | Cubic graph | [PDF](l_le_12/E79854252_1/E79854252_1.pdf) | [Lean](l_le_12/E79854252_1/Solution.lean) |
| [E3471924_25](l_le_12/E3471924_25) | $2x^4+x+y^3-2y+2=0$ | 48 | 12 | Cubic graph | [PDF](l_le_12/E3471924_25/E3471924_25.pdf) | [Lean](l_le_12/E3471924_25/Solution.lean) |
| [E867981_92](l_le_12/E867981_92) | $2x^4+x+y^3-y^2-2=0$ | 48 | 12 | Quadratic norm | [PDF](l_le_12/E867981_92/E867981_92.pdf) | [Lean](l_le_12/E867981_92/Solution.lean) |
| [E45135012_1](l_le_12/E45135012_1) | $2x^4+xy+x+y^3+2=0$ | 48 | 12 | Quadratic graph | [PDF](l_le_12/E45135012_1/E45135012_1.pdf) | [Lean](l_le_12/E45135012_1/Solution.lean) |
| [E11283753_4](l_le_12/E11283753_4) | $2x^4+xy+x+y^3-2=0$ | 48 | 12 | Quadratic norm | [PDF](l_le_12/E11283753_4/E11283753_4.pdf) | [Lean](l_le_12/E11283753_4/Solution.lean) |
| [E15045004_3](l_le_12/E15045004_3) | $2x^4+xy-x+y^3+2=0$ | 48 | 12 | Quadratic norm | [PDF](l_le_12/E15045004_3/E15045004_3.pdf) | [Lean](l_le_12/E15045004_3/Solution.lean) |
| [E3761251_12](l_le_12/E3761251_12) | $2x^4+xy-x+y^3-2=0$ | 48 | 12 | Quadratic norm | [PDF](l_le_12/E3761251_12/E3761251_12.pdf) | [Lean](l_le_12/E3761251_12/Solution.lean) |
| [E2806544_1](l_le_12/E2806544_1) | $x^5+xy+y^3+4=0$ | 48 | 12 | Quadratic graph | [PDF](l_le_12/E2806544_1/E2806544_1.pdf) | [Lean](l_le_12/E2806544_1/Solution.lean) |
| [E53972_45](l_le_12/E53972_45) | $x^5-2x+y^3-y+2=0$ | 48 | 12 | Quadratic norm | [PDF](l_le_12/E53972_45/E53972_45.pdf) | [Lean](l_le_12/E53972_45/Solution.lean) |
| [E215888_13](l_le_12/E215888_13) | $x^5-xy+y^3+4=0$ | 48 | 12 | Quadratic graph | [PDF](l_le_12/E215888_13/E215888_13.pdf) | [Lean](l_le_12/E215888_13/Solution.lean) |
| [E8679810_23](l_le_12/E8679810_23) | $2x^4+x+y^3-y^2+y+1=0$ | 49 | 12 | Quadratic graph | [PDF](l_le_12/E8679810_23/E8679810_23.pdf) | [Lean](l_le_12/E8679810_23/Solution.lean) |
| [E112837530_1](l_le_12/E112837530_1) | $2x^4+xy+x+y^3+y+1=0$ | 49 | 12 | Quadratic norm | [PDF](l_le_12/E112837530_1/E112837530_1.pdf) | [Lean](l_le_12/E112837530_1/Solution.lean) |
| [E22567506_5](l_le_12/E22567506_5) | $2x^4+xy+x+y^3-y+1=0$ | 49 | 12 | Cubic graph | [PDF](l_le_12/E22567506_5/E22567506_5.pdf) | [Lean](l_le_12/E22567506_5/Solution.lean) |
| [E188062550_1](l_le_12/E188062550_1) | $2x^4+xy+y^3+2y+1=0$ | 49 | 12 | Quadratic norm | [PDF](l_le_12/E188062550_1/E188062550_1.pdf) | [Lean](l_le_12/E188062550_1/Solution.lean) |
| [E94031275_2](l_le_12/E94031275_2) | $2x^4+xy+y^3+2y-1=0$ | 49 | 12 | Cubic and quadratic graphs | [PDF](l_le_12/E94031275_2/E94031275_2.pdf) | [Lean](l_le_12/E94031275_2/Solution.lean) |
| [E173017546_1](l_le_12/E173017546_1) | $2x^4+xy+y^3+y^2+1=0$ | 49 | 12 | Cubic graph | [PDF](l_le_12/E173017546_1/E173017546_1.pdf) | [Lean](l_le_12/E173017546_1/Solution.lean) |
| [E37612510_3](l_le_12/E37612510_3) | $2x^4+xy-x+y^3+y+1=0$ | 49 | 12 | Cubic graph | [PDF](l_le_12/E37612510_3/E37612510_3.pdf) | [Lean](l_le_12/E37612510_3/Solution.lean) |
| [E2631135_2](l_le_12/E2631135_2) | $x^5+xy+x+y^3+y-1=0$ | 49 | 12 | Quadratic norm | [PDF](l_le_12/E2631135_2/E2631135_2.pdf) | [Lean](l_le_12/E2631135_2/Solution.lean) |
| [E2280317_4](l_le_12/E2280317_4) | $x^5+2xy+y^3-2=0$ | 50 | 12 | Quadratic norm | [PDF](l_le_12/E2280317_4/E2280317_4.pdf) | [Lean](l_le_12/E2280317_4/Solution.lean) |
| [E918323898_1](l_le_12/E918323898_1) | $2x^4+x+y^3+2y^2+1=0$ | 51 | 12 | Cubic graph | [PDF](l_le_12/E918323898_1/E918323898_1.pdf) | [Lean](l_le_12/E918323898_1/Solution.lean) |
| [E1084976250_1](l_le_12/E1084976250_1) | $2x^4+x+y^3+4y+1=0$ | 51 | 12 | Quadratic graph | [PDF](l_le_12/E1084976250_1/E1084976250_1.pdf) | [Lean](l_le_12/E1084976250_1/Solution.lean) |
| [E35297894_5](l_le_12/E35297894_5) | $2x^4+xy^2+y^3-y+1=0$ | 51 | 12 | Quadratic norm | [PDF](l_le_12/E35297894_5/E35297894_5.pdf) | [Lean](l_le_12/E35297894_5/Solution.lean) |
| [E50598750_1](l_le_12/E50598750_1) | $x^5+x+y^3+4y+1=0$ | 51 | 12 | Quadratic graph | [PDF](l_le_12/E50598750_1/E50598750_1.pdf) | [Lean](l_le_12/E50598750_1/Solution.lean) |
| [E16866250_3](l_le_12/E16866250_3) | $x^5-x+y^3+4y+1=0$ | 51 | 12 | Quartic graph | [PDF](l_le_12/E16866250_3/E16866250_3.pdf) | [Lean](l_le_12/E16866250_3/Solution.lean) |
| [E2633415_212](l_le_12/E2633415_212) | $-x^4+x+2y^4+y-2=0$ | 54 | 12 | Quadratic graph | [PDF](l_le_12/E2633415_212/E2633415_212.pdf) | [Lean](l_le_12/E2633415_212/Solution.lean) |
| [E357608172_5](l_le_12/E357608172_5) | $2x^4+x+2y^3-y+2=0$ | 54 | 12 | Quadratic graph | [PDF](l_le_12/E357608172_5/E357608172_5.pdf) | [Lean](l_le_12/E357608172_5/Solution.lean) |
| [E357911801580_1](l_le_12/E357911801580_1) | $x^4+x+4y^3+y+2=0$ | 54 | 12 | Quadratic norm | [PDF](l_le_12/E357911801580_1/E357911801580_1.pdf) | [Lean](l_le_12/E357911801580_1/Solution.lean) |
| [E77547557009_4](l_le_12/E77547557009_4) | $x^4+xy+4y^3-2=0$ | 54 | 12 | Quartic graph | [PDF](l_le_12/E77547557009_4/E77547557009_4.pdf) | [Lean](l_le_12/E77547557009_4/Solution.lean) |
| [E15800490_53](l_le_12/E15800490_53) | $-x^4+2x+2y^4+y+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E15800490_53/E15800490_53.pdf) | [Lean](l_le_12/E15800490_53/Solution.lean) |
| [E178804086_23](l_le_12/E178804086_23) | $2x^4+x+2y^3-y^2+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E178804086_23/E178804086_23.pdf) | [Lean](l_le_12/E178804086_23/Solution.lean) |
| [E3874088530_1](l_le_12/E3874088530_1) | $2x^4+xy+2y^3+y+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E3874088530_1/E3874088530_1.pdf) | [Lean](l_le_12/E3874088530_1/Solution.lean) |
| [E1937044265_2](l_le_12/E1937044265_2) | $2x^4+xy+2y^3+y-1=0$ | 55 | 12 | Quartic graph | [PDF](l_le_12/E1937044265_2/E1937044265_2.pdf) | [Lean](l_le_12/E1937044265_2/Solution.lean) |
| [E2324453118_1](l_le_12/E2324453118_1) | $2x^4+xy+x+2y^3+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E2324453118_1/E2324453118_1.pdf) | [Lean](l_le_12/E2324453118_1/Solution.lean) |
| [E774817706_3](l_le_12/E774817706_3) | $2x^4+xy-x+2y^3+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E774817706_3/E774817706_3.pdf) | [Lean](l_le_12/E774817706_3/Solution.lean) |
| [E268433851185_2](l_le_12/E268433851185_2) | $x^4+2x+4y^3+y-1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E268433851185_2/E268433851185_2.pdf) | [Lean](l_le_12/E268433851185_2/Solution.lean) |
| [E411598571817_2](l_le_12/E411598571817_2) | $x^4+x+4y^3+y^2-1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E411598571817_2/E411598571817_2.pdf) | [Lean](l_le_12/E411598571817_2/Solution.lean) |
| [E35791180158_23](l_le_12/E35791180158_23) | $x^4+x+4y^3-y^2+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E35791180158_23/E35791180158_23.pdf) | [Lean](l_le_12/E35791180158_23/Solution.lean) |
| [E17895590079_46](l_le_12/E17895590079_46) | $x^4+x+4y^3-y^2-1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E17895590079_46/E17895590079_46.pdf) | [Lean](l_le_12/E17895590079_46/Solution.lean) |
| [E465285342054_1](l_le_12/E465285342054_1) | $x^4+xy+x+4y^3+1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E465285342054_1/E465285342054_1.pdf) | [Lean](l_le_12/E465285342054_1/Solution.lean) |
| [E232642671027_2](l_le_12/E232642671027_2) | $x^4+xy+x+4y^3-1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E232642671027_2/E232642671027_2.pdf) | [Lean](l_le_12/E232642671027_2/Solution.lean) |
| [E77547557009_6](l_le_12/E77547557009_6) | $x^4+xy-x+4y^3-1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E77547557009_6/E77547557009_6.pdf) | [Lean](l_le_12/E77547557009_6/Solution.lean) |
| [E54201381_2](l_le_12/E54201381_2) | $x^5+xy+x+2y^3-1=0$ | 55 | 12 | Quadratic norm | [PDF](l_le_12/E54201381_2/E54201381_2.pdf) | [Lean](l_le_12/E54201381_2/Solution.lean) |
| [E9484662741870_1](l_le_12/E9484662741870_1) | $2x^4+x+4y^3+y+1=0$ | 69 | 12 | Quadratic norm | [PDF](l_le_12/E9484662741870_1/E9484662741870_1.pdf) | [Lean](l_le_12/E9484662741870_1/Solution.lean) |
| [E147441654110_3](l_le_12/E147441654110_3) | $x^5-x+4y^3+y+1=0$ | 69 | 12 | Quartic graph | [PDF](l_le_12/E147441654110_3/E147441654110_3.pdf) | [Lean](l_le_12/E147441654110_3/Solution.lean) |
| [E114892895_2](l_le_12/E114892895_2) | $2x^5+xy+y^3+y-1=0$ | 79 | 12 | Quadratic graph | [PDF](l_le_12/E114892895_2/E114892895_2.pdf) | [Lean](l_le_12/E114892895_2/Solution.lean) |
| [E121907931450_1](l_le_12/E121907931450_1) | $4x^4+x+y^3+2y+1=0$ | 79 | 12 | Quadratic graph | [PDF](l_le_12/E121907931450_1/E121907931450_1.pdf) | [Lean](l_le_12/E121907931450_1/Solution.lean) |
| [E4876317258_23](l_le_12/E4876317258_23) | $4x^4+x+y^3-y^2+1=0$ | 79 | 12 | Cubic graph | [PDF](l_le_12/E4876317258_23/E4876317258_23.pdf) | [Lean](l_le_12/E4876317258_23/Solution.lean) |
| [E105653540590_1](l_le_12/E105653540590_1) | $4x^4+xy+y^3+y+1=0$ | 79 | 12 | Cubic graph | [PDF](l_le_12/E105653540590_1/E105653540590_1.pdf) | [Lean](l_le_12/E105653540590_1/Solution.lean) |
| [E21130708118_5](l_le_12/E21130708118_5) | $4x^4+xy+y^3-y+1=0$ | 79 | 12 | Cubic graph | [PDF](l_le_12/E21130708118_5/E21130708118_5.pdf) | [Lean](l_le_12/E21130708118_5/Solution.lean) |
| [E10565354059_10](l_le_12/E10565354059_10) | $4x^4+xy+y^3-y-1=0$ | 79 | 12 | Quadratic norm | [PDF](l_le_12/E10565354059_10/E10565354059_10.pdf) | [Lean](l_le_12/E10565354059_10/Solution.lean) |
| [E2366793637_2](l_le_12/E2366793637_2) | $2x^5+xy+2y^3-1=0$ | 85 | 12 | Quadratic graph | [PDF](l_le_12/E2366793637_2/E2366793637_2.pdf) | [Lean](l_le_12/E2366793637_2/Solution.lean) |
| [E186951934_1](l_le_12/E186951934_1) | $2x^5+xy+y^4+1=0$ | 85 | 12 | Quadratic norm | [PDF](l_le_12/E186951934_1/E186951934_1.pdf) | [Lean](l_le_12/E186951934_1/Solution.lean) |
| [E2511303387870_1](l_le_12/E2511303387870_1) | $4x^4+x+2y^3+y+1=0$ | 85 | 12 | Cubic graph | [PDF](l_le_12/E2511303387870_1/E2511303387870_1.pdf) | [Lean](l_le_12/E2511303387870_1/Solution.lean) |
| [E2176462936154_1](l_le_12/E2176462936154_1) | $4x^4+xy+2y^3+1=0$ | 85 | 12 | Quadratic norm | [PDF](l_le_12/E2176462936154_1/E2176462936154_1.pdf) | [Lean](l_le_12/E2176462936154_1/Solution.lean) |
| [E20141644294063095990_1](l_le_12/E20141644294063095990_1) | $x^4+x+8y^3+y+1=0$ | 85 | 12 | Quadratic norm | [PDF](l_le_12/E20141644294063095990_1/E20141644294063095990_1.pdf) | [Lean](l_le_12/E20141644294063095990_1/Solution.lean) |
| [E4028328858812619198_5](l_le_12/E4028328858812619198_5) | $x^4+x+8y^3-y+1=0$ | 85 | 12 | Quadratic norm | [PDF](l_le_12/E4028328858812619198_5/E4028328858812619198_5.pdf) | [Lean](l_le_12/E4028328858812619198_5/Solution.lean) |
| [E2014164429406309599_10](l_le_12/E2014164429406309599_10) | $x^4+x+8y^3-y-1=0$ | 85 | 12 | Quadratic norm | [PDF](l_le_12/E2014164429406309599_10/E2014164429406309599_10.pdf) | [Lean](l_le_12/E2014164429406309599_10/Solution.lean) |
| [E17456091721521349858_1](l_le_12/E17456091721521349858_1) | $x^4+xy+8y^3+1=0$ | 85 | 12 | Quadratic graph | [PDF](l_le_12/E17456091721521349858_1/E17456091721521349858_1.pdf) | [Lean](l_le_12/E17456091721521349858_1/Solution.lean) |
| [E85784374_1](l_le_12/E85784374_1) | $x^6+xy+2y^3+1=0$ | 85 | 12 | Quadratic norm | [PDF](l_le_12/E85784374_1/E85784374_1.pdf) | [Lean](l_le_12/E85784374_1/Solution.lean) |
| [E96191221685552745_2](l_le_12/E96191221685552745_2) | $8x^4+x+y^3+y-1=0$ | 141 | 12 | Cubic graph | [PDF](l_le_12/E96191221685552745_2/E96191221685552745_2.pdf) | [Lean](l_le_12/E96191221685552745_2/Solution.lean) |

## Contents of a folder

```
h_le_34/E49131_20/
├── README.md         the equation, its size and length, and the method
├── E49131_20.pdf     a self-contained proof
├── E49131_20.tex     the LaTeX source of the PDF
├── Challenge.lean    the statement in Lean, with the proof replaced by sorry
├── Solution.lean     the proof in Lean, which needs only Mathlib
└── comparator.json   configuration of comparator
```

Apart from its imports, a `Challenge.lean` consists of one theorem, for example

```lean
theorem E49131_20 : ¬ ∃ x y : ℤ, x^4 + 2*x + y^3 - y - 2 = 0 := by
  sorry
```

To trust a Lean proof, it is enough to read its `Challenge.lean`: comparator checks that `Solution.lean` proves exactly this statement, using only the standard axioms `propext`, `Quot.sound` and `Classical.choice`.

The PDF proofs do not depend on a computer. They contain all identities and tables needed to check every step by hand, so the proofs of the larger graph certificates are long.

## Checking the proofs

The Lean files are written for Lean 4.34.0 and the version of Mathlib fixed in `lakefile.toml`. Each `Solution.lean` is independent of the others and needs only Mathlib.

```
lake exe cache get                                    # download the compiled Mathlib
lake build h_le_34.E49131_20.Challenge h_le_34.E49131_20.Solution
lake env /path/to/comparator h_le_34/E49131_20/comparator.json
```

See the README of [comparator](https://github.com/leanprover/comparator) for running the last command in a sandbox.

A quadratic norm proof usually compiles in less than a minute. A graph proof takes from a few minutes to many hours, and may need more than 10 GB of memory, so the large files are best compiled one at a time.

## Size, length and names

If the polynomial $P(x,y)$ consists of monomials with integer coefficients $a_1,\dots,a_k$ and degrees $d_1,\dots,d_k$, then the size and the length of the equation $P(x,y)=0$ are

$$h(P)=\sum_{i=1}^k |a_i| 2^{d_i},\qquad l(P)=\sum_{i=1}^k \bigl(\log_2|a_i|+d_i\bigr).$$

The name of an equation encodes its polynomial, following Section 8.4 of [Grechuk and Wilcox, *Polynomial Diophantine equations: a systematic approach*, Springer, 2024]. If $P(x,y)=\sum_{i,j} c_{ij}x^iy^j$, put

$$q(P)=\prod_{i,j} p_{2^i3^j}^{c_{ij}},$$

where $p_n$ is the $n$-th prime, so that $p_1=2$. This is a rational number, and $P$ can be recovered from it. The equations $\pm P(\pm x,\pm y)=0$ have the same integer solutions up to sign; among them (and the equations with $x$ and $y$ exchanged, if they have the same degree) we take the one with the largest $q$. This is the equation in the tables, in `Challenge.lean` and in the PDF, and its name is `E` followed by the numerator and the denominator of $q$. For example, $x^4+2x+y^3-y-2=0$ has $q = 2^{-2}\cdot3^{2}\cdot5^{-1}\cdot53\cdot103 = 49131/20$, so it is named `E49131_20`.

The paper may write an equation in an equivalent form, with $x$ or $y$ replaced by $-x$ or $-y$, or with the two sides exchanged.

## Use of AI

The certificates were found by computer search, and the Lean proofs were written with the help of AI tools. The correctness of the results does not depend on these tools: every proof is checked by the Lean kernel, and comparator checks that the proved statements are those of `Challenge.lean`. See also [formalization.yaml](formalization.yaml).

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

<!-- ## License

TODO: choose the licences. 
The Lean code is released under the Apache License 2.0, and the PDF and LaTeX files under CC BY 4.0.-->
