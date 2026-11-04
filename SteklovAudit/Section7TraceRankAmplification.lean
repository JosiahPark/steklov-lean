-- From hourly continuation 27 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-!
# Section 7: finite-rank trace amplification of Hilbert--Schmidt errors

Scalar algebra supporting the independently proved matrix inequality
|Tr(P T P)|² ≤ rank(P) ‖T P‖_HS².
This module does NOT formalize the matrix theorem or tetrahedral estimates.
-/
namespace SteklovAudit

theorem trace_budget_scalar (r e : ℝ) (hr : 0 ≤ r) (he : 0 ≤ e) :
    0 ≤ r * e := mul_nonneg hr he

theorem trace_budget_saturation (r x : ℝ) :
    (r*x)^2 = r*(r*x^2) := by ring

theorem trace_budget_quadratic (r t k : ℝ) :
    r * (t*k)^2 = r*t^2*k^2 := by ring

end SteklovAudit
