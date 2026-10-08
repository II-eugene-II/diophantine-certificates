import Lean.Elab.Command
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic

-- The equation x^4 + x + 2*y^3 - y + 3 = 0 has no integer solutions.
theorem E13494648_5 : ¬ ∃ x y : ℤ, x^4 + x + 2*y^3 - y + 3 = 0 := by
  sorry
