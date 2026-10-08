import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Factorization.Induction

-- The equation -x^4 + 2*x + 2*y^4 + y + 1 = 0 has no integer solutions.
theorem E15800490_53 : ¬ ∃ x y : ℤ, -x^4 + 2*x + 2*y^4 + y + 1 = 0 := by
  sorry
