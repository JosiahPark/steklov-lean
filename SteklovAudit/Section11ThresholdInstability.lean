-- From hourly continuation 33 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-! Continuation 33: elementary scalar lemmas only. not compiled at the time.
The finite-dimensional spectral counterexample is proved in the report,
not represented as a Lean theorem here. -/
namespace SteklovAudit

theorem threshold_gap_positive (n : ℕ) (hn : 0 < n) :
    (0 : ℚ) < (1 : ℚ) / n :=
  one_div_pos.mpr (by exact_mod_cast hn)

theorem threshold_hs_square (n : ℕ) (hn : 0 < n) :
    (n : ℚ) * ((1 : ℚ) / n)^2 = (1 : ℚ) / n := by
  have hne : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [div_pow, one_pow, mul_one_div, sq, ← div_div, div_self hne]

end SteklovAudit
