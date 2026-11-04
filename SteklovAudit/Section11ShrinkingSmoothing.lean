-- From hourly continuation 36 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-! Continuation 36. not compiled at the time candidate; the analytic convolution theorem is NOT formalized. -/
namespace SteklovAudit

theorem monotone_shift_squeeze {f : ℝ → ℝ} (hf : Monotone f)
    (x h : ℝ) (hh : 0 ≤ h) :
    f (x - h) ≤ f x ∧ f x ≤ f (x + h) := by
  constructor
  · exact hf (sub_le_self x hh)
  · exact hf (le_add_of_nonneg_right hh)

theorem quadratic_shift_right (a b x h : ℝ) :
    a * (x + h)^2 + b * (x + h) - (a * x^2 + b * x) =
      (2 * a * x + b) * h + a * h^2 := by
  ring

theorem quadratic_shift_left (a b x h : ℝ) :
    a * (x - h)^2 + b * (x - h) - (a * x^2 + b * x) =
      -(2 * a * x + b) * h + a * h^2 := by
  ring
end SteklovAudit
