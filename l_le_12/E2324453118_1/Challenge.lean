import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Factorization.Induction

-- The equation 2*x^4 + x*y + x + 2*y^3 + 1 = 0 has no integer solutions.
theorem E2324453118_1 : ¬ ∃ x y : ℤ, 2*x^4 + x*y + x + 2*y^3 + 1 = 0 := by
  sorry
