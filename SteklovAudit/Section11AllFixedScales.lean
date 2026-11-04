-- From hourly continuation 37 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-! Continuation 37: not compiled at the time algebraic scaffolding only. -/
namespace SteklovAudit

theorem quadratic_fixed_shift_plus (a b L h : ℝ) :
    (a * (L + h)^2 + b * (L + h)) - (a * L^2 + b * L) =
      2 * a * L * h + a * h^2 + b * h := by
  ring

theorem quadratic_fixed_shift_minus (a b L h : ℝ) :
    (a * (L - h)^2 + b * (L - h)) - (a * L^2 + b * L) =
      -(2 * a * L * h) + a * h^2 - b * h := by
  ring

theorem monotone_fixed_window {N : ℝ → ℝ} (hN : Monotone N)
    (L h t : ℝ) (hh : 0 ≤ h) (htlo : -1 ≤ t) (hthi : t ≤ 1) :
    N (L - h - h*t) ≤ N L ∧ N L ≤ N (L + h - h*t) := by
  constructor
  · apply hN
    nlinarith
  · apply hN
    nlinarith
end SteklovAudit
