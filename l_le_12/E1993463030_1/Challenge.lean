import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Factorization.Induction

-- The equation 3*x^4 + x*y + y^3 + y + 1 = 0 has no integer solutions.
theorem E1993463030_1 : ¬ ∃ x y : ℤ, 3*x^4 + x*y + y^3 + y + 1 = 0 := by
  sorry
