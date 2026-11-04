-- From hourly continuation 42 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
namespace SteklovAudit
-- not compiled at the time scalar lemmas. Operator-level statement remains mathematical only.
theorem weighted_gap_square (a b L s : ℝ)
    (ha : a ≤ L) (hb : L+s ≤ b) (hs : 0 ≤ s) :
    s^2 ≤ (b-a)^2 := by
  have h : s ≤ b-a := by linarith
  nlinarith [sq_nonneg (b-a-s)]

theorem weighted_tail_bound (d t s : ℝ) (ht : 0 ≤ t)
    (hs : 0 ≤ s) (hgap : s ≤ t) : s^2 ≤ t^2 := by
  nlinarith [sq_nonneg (t-s)]
end SteklovAudit
