-- From hourly continuation 35 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib

/-! Continuation 35. Not compiled at the time: no Lean executable in runtime.
The actual floor-counting and convolution counterexample is proved in the report,
not formalized here. These are only polynomial identities used by that proof. -/
namespace SteklovAudit

theorem centered_square_identity (L s : ℝ) :
    (L + s)^2 = L^2 + 2 * L * s + s^2 := by
  ring

theorem shifted_linear_amplitude (L s : ℝ) :
    (L + s) * (L - s) = L^2 - s^2 := by
  ring

end SteklovAudit
