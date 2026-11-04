-- From hourly continuation 39 (Steklov_All_Continuations_02-43 archive). Compiled in CI from here on;
-- scalar lemmas only, see the module text for what is NOT formalized.
import Mathlib
/-! Continuation 39. Scalar proof components only. -/

namespace SteklovAudit

-- The full matrix/spectral-projection theorem is NOT represented by these scalar lemmas.
theorem spectral_gap_square (d δ : ℝ) (hδ : 0 ≤ δ) (hd : δ ≤ d) : δ ^ 2 ≤ d ^ 2 := by
  nlinarith [sq_nonneg (d - δ)]

theorem leakage_budget (r q e d δ : ℝ)
    (h : r ≤ q + e + d / δ ^ 2)
    (hδ : 0 < δ) : δ ^ 2 * (r - q - e) ≤ d := by
  have hs : 0 < δ ^ 2 := by positivity
  have h' : r - q - e ≤ d / δ ^ 2 := by linarith
  have h'' := (le_div_iff₀ hs).mp h'
  linarith

end SteklovAudit
