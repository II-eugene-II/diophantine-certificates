import Lean.Elab.Command
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity

-- The equation x^5 - x + 4*y^3 + y + 1 = 0 has no integer solutions.
theorem E147441654110_3 : ¬ ∃ x y : ℤ, x^5 - x + 4*y^3 + y + 1 = 0 := by
  sorry
