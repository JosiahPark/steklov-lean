import Mathlib

/-!
# Lemma 7.1' checklist: elementary inequalities (`UniformHS71`)

Concrete real inequalities used in the written proof of the uniform localized
Hilbert–Schmidt bound (7.2'). Items are appended one per run, following ROADMAP.md §A.

This file does NOT prove Lemma 7.1' itself, any Hilbert–Schmidt estimate for the
Dirichlet-to-Neumann operator, or the main theorem (Theorem 1.3 / 11.1). It contains only
scalar inequalities; no analytic hypotheses are introduced.
-/

namespace SteklovAudit.UniformHS71

/-- A1. For `λ ≥ 1` and `L ≥ 0`: `(λ⁻¹ + L)² ≤ (1 + L)²`. -/
theorem inv_add_sq_le_one_add_sq (lam L : ℝ) (hlam : 1 ≤ lam) (hL : 0 ≤ L) :
    (lam⁻¹ + L) ^ 2 ≤ (1 + L) ^ 2 := by
  have hpos : 0 < lam := by linarith
  have h0 : 0 < lam⁻¹ := inv_pos.mpr hpos
  have hmul : lam⁻¹ * lam = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have h1 : lam⁻¹ ≤ 1 := by nlinarith
  have hsub : 0 ≤ 1 - lam⁻¹ := by linarith
  have hsum : 0 ≤ 1 + lam⁻¹ + 2 * L := by linarith
  have key : (1 + L) ^ 2 - (lam⁻¹ + L) ^ 2 = (1 - lam⁻¹) * (1 + lam⁻¹ + 2 * L) := by ring
  nlinarith [mul_nonneg hsub hsum]

/-- A2. For `λ > 0`: `C (1 + λL)² · λ⁻² = C (λ⁻¹ + L)²`. -/
theorem scaled_sq_mul_inv_sq (C lam L : ℝ) (hlam : 0 < lam) :
    C * (1 + lam * L) ^ 2 * lam⁻¹ ^ 2 = C * (lam⁻¹ + L) ^ 2 := by
  have h : lam ≠ 0 := ne_of_gt hlam
  have e : lam⁻¹ + L = (1 + lam * L) * lam⁻¹ := by
    rw [add_mul, one_mul, mul_comm lam L, mul_assoc, mul_inv_cancel₀ h, mul_one]
  rw [e]
  ring

/-- A2, division form: `C (1 + λL)² / λ² = C (λ⁻¹ + L)²` for `λ > 0`. -/
theorem scaled_sq_div_sq (C lam L : ℝ) (hlam : 0 < lam) :
    C * (1 + lam * L) ^ 2 / lam ^ 2 = C * (lam⁻¹ + L) ^ 2 := by
  rw [div_eq_mul_inv, ← inv_pow]
  exact scaled_sq_mul_inv_sq C lam L hlam

end SteklovAudit.UniformHS71
