import Mathlib

/-!
# The `1/t` cancellation in the cumulative Fourier integral (roadmap item G130)

If a propagated defect satisfies `|g t| ≤ |t| · ε` (the shape of G129's `duhamel_entry_le`) and the
Fourier weight satisfies `|w t| · |t| ≤ C` (a weight of size `1/t`), then the integrand is bounded by
`C ε` and `fourier_cancel_le` gives `|∫_{−T}^{T} w g| ≤ 2 T C ε`. No integrability hypothesis is
needed (`intervalIntegral.norm_integral_le_of_norm_le_const`; a non-integrable integrand has integral
`0`). `inv_weight_ok` checks that the weight `w t = t⁻¹` meets the hypothesis with `C = 1`, so it is
not vacuous; `eps_nonneg_of_bound` records that the defect hypothesis forces `ε ≥ 0`.

What this file does NOT prove: the defect bound `|g t| ≤ |t| ε` for the actual tetrahedron–wedge
comparison, the size of `ε`, the choice of window `T`, (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.FourierOneOverT

/-- The defect hypothesis forces `ε ≥ 0`. -/
theorem eps_nonneg_of_bound (g : ℝ → ℝ) (ε : ℝ) (hg : ∀ t, |g t| ≤ |t| * ε) : 0 ≤ ε := by
  have h1 := hg 1
  have h2 : 0 ≤ |g 1| := abs_nonneg _
  rw [abs_one, one_mul] at h1
  linarith

/-- **G130.** `|g t| ≤ |t| ε` and `|w t| |t| ≤ C` give `|∫_{−T}^{T} w g| ≤ 2 T C ε`. -/
theorem fourier_cancel_le (g w : ℝ → ℝ) (ε C T : ℝ) (hT : 0 ≤ T)
    (hg : ∀ t, |g t| ≤ |t| * ε) (hw : ∀ t, |w t| * |t| ≤ C) :
    |∫ t in (-T)..T, w t * g t| ≤ 2 * T * C * ε := by
  have hε : 0 ≤ ε := eps_nonneg_of_bound g ε hg
  have hpt : ∀ t, |w t * g t| ≤ C * ε := by
    intro t
    rw [abs_mul]
    have h1 : |w t| * |g t| ≤ |w t| * (|t| * ε) :=
      mul_le_mul_of_nonneg_left (hg t) (abs_nonneg _)
    have h2 : |w t| * |t| * ε ≤ C * ε := mul_le_mul_of_nonneg_right (hw t) hε
    nlinarith
  have hb : ‖∫ t in (-T)..T, w t * g t‖ ≤ C * ε * |T - -T| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => by
      rw [Real.norm_eq_abs]
      exact hpt t)
  rw [Real.norm_eq_abs] at hb
  have hab : |T - -T| = 2 * T := by
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]
    ring
  rw [hab] at hb
  linarith

/-- The weight `w t = t⁻¹` satisfies `|w t| · |t| ≤ 1` (so the hypothesis is not vacuous). -/
theorem inv_weight_ok (t : ℝ) : |t⁻¹| * |t| ≤ 1 := by
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · rw [abs_inv, inv_mul_cancel₀ (abs_ne_zero.mpr h)]

/-- **G130**, the `1/t` weight: `|∫_{−T}^{T} t⁻¹ g t| ≤ 2 T ε`. -/
theorem fourier_cancel_inv (g : ℝ → ℝ) (ε T : ℝ) (hT : 0 ≤ T) (hg : ∀ t, |g t| ≤ |t| * ε) :
    |∫ t in (-T)..T, t⁻¹ * g t| ≤ 2 * T * ε := by
  have h := fourier_cancel_le g (fun t => t⁻¹) ε 1 T hT hg inv_weight_ok
  simpa using h

end SteklovAudit.FourierOneOverT
