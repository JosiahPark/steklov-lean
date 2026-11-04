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

/-- A3. For `λ > 0`: `t / λ ≤ L ↔ t ≤ λ L`. -/
theorem div_le_iff_le_scaled (lam t L : ℝ) (hlam : 0 < lam) :
    t / lam ≤ L ↔ t ≤ lam * L := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hne
  have e : lam * (t / lam) = t := by
    rw [div_eq_mul_inv, mul_comm t, ← mul_assoc, hinv, one_mul]
  constructor
  · intro h
    calc t = lam * (t / lam) := e.symm
      _ ≤ lam * L := mul_le_mul_of_nonneg_left h hlam.le
  · intro h
    have h2 : lam * (t / lam) ≤ lam * L := by rw [e]; exact h
    first
      | exact le_of_mul_le_mul_left h2 hlam
      | nlinarith

/-- A3, spectral form. Over a finite spectrum `T` (indexed by `s`) and any weights `g`,
the indicator sums agree: `1_[0,L](λ⁻¹T) = 1_[0,λL](T)`. Only the upper cut changes; the
lower cut `0 ≤ ·` is invariant since `λ > 0`. -/
theorem indicator_sum_scaled {ι : Type*} (s : Finset ι) (T g : ι → ℝ) (lam L : ℝ)
    (hlam : 0 < lam) :
    (∑ i ∈ s, if 0 ≤ T i / lam ∧ T i / lam ≤ L then g i else 0) =
      ∑ i ∈ s, if 0 ≤ T i ∧ T i ≤ lam * L then g i else 0 := by
  refine Finset.sum_congr rfl ?_
  intro i _
  have hu := div_le_iff_le_scaled lam (T i) L hlam
  have hl : 0 ≤ T i / lam ↔ 0 ≤ T i := by
    have := div_le_iff_le_scaled lam (T i) 0 hlam
    constructor
    · intro h0
      by_contra hneg
      push_neg at hneg
      have h1 : T i ≤ lam * 0 := by rw [mul_zero]; exact hneg.le
      have h2 : T i / lam ≤ 0 := this.mpr h1
      have h3 : T i / lam = 0 := le_antisymm h2 h0
      have h4 : T i = lam * (T i / lam) := by
        rw [div_eq_mul_inv, mul_comm (T i), ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlam),
          one_mul]
      rw [h3, mul_zero] at h4
      linarith
    · intro h0
      rw [div_eq_mul_inv]
      exact mul_nonneg h0 (inv_nonneg.mpr hlam.le)
  by_cases h : 0 ≤ T i ∧ T i ≤ lam * L
  · rw [if_pos ⟨hl.mpr h.1, hu.mpr h.2⟩, if_pos h]
  · have h' : ¬ (0 ≤ T i / lam ∧ T i / lam ≤ L) := fun h' => h ⟨hl.mp h'.1, hu.mp h'.2⟩
    rw [if_neg h', if_neg h]

/-- A5. Gradient-scaling cancellation: for `λ > 0`, `λ⁻¹ · C · (λ · G) = C · G`. -/
theorem gradient_scaling_cancel (C G lam : ℝ) (hlam : 0 < lam) :
    lam⁻¹ * C * (lam * G) = C * G := by
  have h : lam ≠ 0 := ne_of_gt hlam
  calc lam⁻¹ * C * (lam * G) = (lam⁻¹ * lam) * (C * G) := by ring
    _ = C * G := by rw [inv_mul_cancel₀ h, one_mul]

/-- A5, division form: `C · (λ · G) / λ = C · G` for `λ > 0`. -/
theorem gradient_scaling_div (C G lam : ℝ) (hlam : 0 < lam) :
    C * (lam * G) / lam = C * G := by
  have h : lam ≠ 0 := ne_of_gt hlam
  rw [div_eq_mul_inv]
  calc C * (lam * G) * lam⁻¹ = (lam * lam⁻¹) * (C * G) := by ring
    _ = C * G := by rw [mul_inv_cancel₀ h, one_mul]

/-- A5, inequality form: if a gradient quantity `g` satisfies `g ≤ λ G` (the rescaled
gradient bound, supplied as a hypothesis), then `λ⁻¹ · C · g ≤ C · G` for `C ≥ 0`, `λ > 0`. -/
theorem scaled_gradient_bound (C G g lam : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hg : g ≤ lam * G) :
    lam⁻¹ * C * g ≤ C * G := by
  have hk : 0 ≤ lam⁻¹ * C := mul_nonneg (inv_nonneg.mpr hlam.le) hC
  calc lam⁻¹ * C * g ≤ lam⁻¹ * C * (lam * G) := mul_le_mul_of_nonneg_left hg hk
    _ = C * G := gradient_scaling_cancel C G lam hlam

end SteklovAudit.UniformHS71
