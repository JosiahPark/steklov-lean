import Mathlib

/-!
# Cusp barrier support for the uniform localized Hilbert–Schmidt estimate (7.2)

Real-analytic inequalities behind the edge-cusp barrier in the proof of Lemma 7.1 / (7.2).
In normalized edge coordinates the comparison function
`w(r, θ, z) = r^β · d(z)^{-β} · cos(γ (θ - α₀/2))` is superharmonic in a thin cusp when
`1/2 < β < γ < ν = π/α₀`: the transverse Laplacian gives a negative term of order `r^{β-2}`,
and the longitudinal term, of order `r^β`, is dominated by it as `r → 0`.

* `transverse_coeff_neg`: `β² - γ² < 0` when `0 ≤ β < γ` (the sign condition `0 ≤ β` is
  needed: for `β = -3`, `γ = -2` the difference is positive).
* `longitudinal_subordinate`: for `C ≥ 0`, `δ > 0` there is `r₀ > 0` with
  `C r^β ≤ δ r^{β-2}` for all `0 < r ≤ r₀` (any real `β`).
* `admissible_exponents_nonempty`: for every `α₀ ∈ (0, π)` there are `β, γ` with
  `1/2 < β < γ < π/α₀`.

The integrability of the weight `r^{2β-2}` for `β > 1/2` is already
`UniformHS71.integral_rpow_two_beta_sub_two`, and the Hilbert–Schmidt bound from a pointwise
`L²` majorant is `UniformHS71.hs2_le_of_pointwise`; neither is repeated here.

What this file does NOT prove: no harmonic function, maximum principle, Sobolev estimate or
Dirichlet-to-Neumann operator is constructed; (7.2), (7.29), (7.38)/(7.45), (9.1), every
[H1]–[H6] input and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.CuspBarrierSupport

/-- The leading transverse coefficient is negative when `0 ≤ β < γ`. -/
theorem transverse_coeff_neg (β γ : ℝ) (hβ : 0 ≤ β) (h : β < γ) :
    β ^ 2 - γ ^ 2 < 0 := by
  nlinarith [mul_pos (sub_pos.mpr h) (by linarith : (0 : ℝ) < γ + β)]

/-- Longitudinal contamination is dominated by the transverse term near `r = 0`. -/
theorem longitudinal_subordinate (C δ β : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      C * r ^ β ≤ δ * r ^ (β - 2) := by
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨min 1 (δ / (C + 1)), lt_min one_pos (div_pos hδ hC1), fun r hr hrle => ?_⟩
  have hr1 : r ≤ 1 := le_trans hrle (min_le_left _ _)
  have hrd : r ≤ δ / (C + 1) := le_trans hrle (min_le_right _ _)
  have hrC : r * (C + 1) ≤ δ := (le_div_iff₀ hC1).mp hrd
  have hsq : r ^ 2 ≤ r := by nlinarith
  have hCr : C * r ^ 2 ≤ δ := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hC1.le, sq_nonneg r]
  have hsplit : r ^ β = r ^ (2 : ℕ) * r ^ (β - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have hpos : 0 ≤ r ^ (β - 2) := Real.rpow_nonneg hr.le _
  calc C * r ^ β = (C * r ^ 2) * r ^ (β - 2) := by rw [hsplit]; ring
    _ ≤ δ * r ^ (β - 2) := mul_le_mul_of_nonneg_right hCr hpos

/-- The admissible range `1/2 < β < γ < π/α₀` is nonempty for every `α₀ ∈ (0, π)`. -/
theorem admissible_exponents_nonempty (α₀ : ℝ) (hα : 0 < α₀) (hα' : α₀ < Real.pi) :
    ∃ β γ : ℝ, 1 / 2 < β ∧ β < γ ∧ γ < Real.pi / α₀ := by
  have hν : 1 < Real.pi / α₀ := (one_lt_div hα).mpr hα'
  exact ⟨3 / 4, 7 / 8, by norm_num, by norm_num, by linarith⟩

end SteklovAudit.CuspBarrierSupport
