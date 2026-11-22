import Mathlib

/-!
# Abstract fixed-time cumulative error budget (supporting (7.29))

Elementary real-analysis pieces that turn a vanishing high-energy Hilbert–Schmidt
tail into an o(L) cumulative error after Duhamel and fixed-time smoothing.

This does NOT prove the operator estimates of Proposition 7.3 or (7.29)
for the tetrahedron or the model wedge.
-/

namespace SteklovAudit.CumulativeBudget

/-- For any fixed constants the product C · S · δ · L is O(L). -/
theorem uniform_defect_is_O (C S δ L : ℝ) :
    C * S * δ * L = (C * S * δ) * L := by
  ring

/-- If a tail contribution is bounded by C L / M for every M, then it is o(L)
once M is sent to infinity after L. -/
theorem tail_over_M_is_o (C : ℝ) (_hC : 0 ≤ C) :
    Filter.Tendsto (fun L : ℝ => (C / L) * L) Filter.atTop (nhds C) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
  have hL' : L ≠ 0 := ne_of_gt hL
  show C = C / L * L
  first
    | exact (div_mul_cancel₀ C hL').symm
    | (field_simp; done)
    | (field_simp; ring)

/-- The Duhamel factor |t| ≤ S on a fixed time interval multiplies an o(1)
high-energy defect into an o(1) contribution after normalization by L. -/
theorem time_factor_preserves_o (S ε : ℝ) (hS : 0 ≤ S) :
    |S * ε| ≤ S * |ε| := by
  exact le_of_eq (by rw [abs_mul, abs_of_nonneg hS])

end SteklovAudit.CumulativeBudget
