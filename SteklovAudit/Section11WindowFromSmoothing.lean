-- From hourly continuation 41 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
-- not compiled at the time candidate; scalar algebra, not tetrahedral verification.
import Mathlib
namespace SteklovAudit

theorem quadratic_window_difference (a b L h : ℝ) :
    (a*(L+2*h)^2+b*(L+2*h)) -
      (a*(L-2*h)^2+b*(L-2*h)) =
    8*a*L*h+4*b*h := by ring

theorem window_bound_from_four_sided_squeeze
    (nlo nhi slo shi : ℝ)
    (hlo : slo ≤ nlo) (hhi : nhi ≤ shi) :
    nhi - nlo ≤ shi - slo := by linarith

end SteklovAudit
