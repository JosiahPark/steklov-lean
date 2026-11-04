-- From hourly continuation 38 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-! Continuation 38. Scalar scaffolding ONLY; not compiled and not a formalization
of the asymptotic smoothing theorem. -/
namespace SteklovAudit

theorem shift_linear_normalized (a b c L h : ℝ) :
    (a * (L + h)^2 + c * (L + h)) - (a * L^2 + b * L) =
      (2*a*h + c-b)*L + a*h^2 + c*h := by
  ring

theorem shift_linear_normalized_minus (a b c L h : ℝ) :
    (a * (L - h)^2 + c * (L - h)) - (a * L^2 + b * L) =
      (-2*a*h + c-b)*L + a*h^2 - c*h := by
  ring

theorem monotone_window_order {N : ℝ → ℝ} (hN : Monotone N)
    (L h t : ℝ) (hh : 0 ≤ h) (htlo : -1 ≤ t) (hthi : t ≤ 1) :
    N (L - h - h*t) ≤ N L ∧ N L ≤ N (L + h - h*t) := by
  constructor
  · apply hN
    nlinarith
  · apply hN
    nlinarith
end SteklovAudit
