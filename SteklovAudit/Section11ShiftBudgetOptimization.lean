-- From hourly continuation 34 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib

/-! Scalar algebraic lemmas for the spectral-shift error budget.
    These are CANDIDATES, not compiler-checked. No assertion about tetrahedral operators. -/
namespace SteklovAudit

/-- Exact factorization underlying the sharp scalar optimization. -/
theorem cubic_factor (x : ℝ) :
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2) := by
  ring

/-- Elementary nonnegative polynomial, with equality at x = 1. -/
theorem cubic_nonnegative (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x ^ 3 - 3 * x + 2 := by
  rw [cubic_factor]
  exact mul_nonneg (sq_nonneg _) (by linarith)

/-- Multiplicative form of the optimal shift tradeoff. -/
theorem shift_tradeoff (x : ℝ) (hx : 0 < x) :
    3 * x ≤ x ^ 3 + 2 := by
  have h : 0 ≤ (x - 1) ^ 2 * (x + 2) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [sq_nonneg (x - 1)]
end SteklovAudit
