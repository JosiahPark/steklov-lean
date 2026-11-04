-- From hourly continuation 33 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-! Continuation 32. Scalar algebraic consequences ONLY. No claim that the
 tetrahedral DtN comparison hypotheses have been established. not compiled at the time. -/
namespace SteklovAudit

theorem asymptotic_squeeze_scalar (target center windowError transferError : ℝ)
    (hLower : center - windowError - transferError ≤ target)
    (hUpper : target ≤ center + windowError + transferError) :
    |target - center| ≤ windowError + transferError := by
  rw [abs_le]
  constructor <;> linarith

theorem shifted_quadratic_difference (a b L δ : ℝ) :
    (a * (L + δ)^2 + b * (L + δ)) - (a * L^2 + b * L) =
      2*a*L*δ + a*δ^2 + b*δ := by
  ring

end SteklovAudit
