import Mathlib.Data.Int.Basic
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Data.ZMod.Factorial
import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

-- The equation -x^4 + x^2 + x + y^3 - y + 3 = 0 has no integer solutions.
theorem E17304_265 : ¬ ∃ x y : ℤ, -x^4 + x^2 + x + y^3 - y + 3 = 0 := by
  sorry
