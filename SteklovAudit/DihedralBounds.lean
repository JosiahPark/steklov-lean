import Mathlib
import SteklovAudit.DihedralIntegrable
import SteklovAudit.RightAngleCalibration

/-!
# C9, C10: quantitative bounds and monotonicity of the dihedral coefficient

Roadmap items C9 and C10, for `c_α = MainConditional.dihedralCoeff α` (formula (1.4)):

* C9 `dihedralCoeff_le`: `c_α ≤ 4(π − α) / (π α²)` for `0 < α < π`, from the pointwise bound
  `DihedralIntegrable.integrand_bound` and `∫₀^∞ e^{−αv} dv = 1/α` (`ioi_integral_exp_neg_mul`);
  `dihedralCoeff_tetra_le` at `α₀ = arccos(1/3)`.
* C10 `integrand_antitone`: for `v > 0` the integrand is antitone in `α` on `(0, π)`;
  `dihedralCoeff_antitone`: `α ≤ β ⇒ c_β ≤ c_α` on `(0, π)`; with C3 (`c_{π/2} = 1/(2π)`) and
  `α₀ < π/2` this gives `dihedralCoeff_tetra_ge`: `1/(2π) ≤ c_{α₀}`.

What this file does NOT prove: the exact value of `c_{α₀}`, any hypothesis H1–H6 of
`MainConditional`, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.DihedralBounds

open MeasureTheory SteklovAudit.MainConditional

/-- `∫₀^∞ e^{−αv} dv = 1/α` for `α > 0`. -/
theorem ioi_integral_exp_neg_mul (α : ℝ) (h0 : 0 < α) :
    ∫ v in Set.Ioi (0 : ℝ), Real.exp (-α * v) = 1 / α := by
  have h : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(α * x)) =
      α⁻¹ • ∫ x in Set.Ioi (α * 0), Real.exp (-x) :=
    integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 h0
  first
    | (rw [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one] at h
       simp_rw [neg_mul]
       rw [h, one_div])
    | (rw [integral_exp_mul_Ioi (by linarith : -α < 0) 0]; simp)
    | (rw [integral_exp_mul_Ioi (by linarith : -α < 0) 0]; field_simp)

/-- C9. `c_α ≤ 4(π − α) / (π α²)` for `0 < α < π`. -/
theorem dihedralCoeff_le (α : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) :
    dihedralCoeff α ≤ 4 * (Real.pi - α) / (Real.pi * α ^ 2) := by
  unfold dihedralCoeff
  have hb : 0 < Real.pi - α := by linarith
  have hpi := Real.pi_pos
  have hint := DihedralIntegrable.integrableOn_dihedral α h0 hπ
  have hg : IntegrableOn (fun v : ℝ => 4 * (Real.pi - α) / α * Real.exp (-α * v))
      (Set.Ioi 0) := by
    first
      | exact Integrable.const_mul (exp_neg_integrableOn_Ioi 0 h0) (4 * (Real.pi - α) / α)
      | exact (exp_neg_integrableOn_Ioi 0 h0).const_mul (4 * (Real.pi - α) / α)
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) ≤
        4 * (Real.pi - α) / α * Real.exp (-α * v) := by
    intro v hv
    have h := (DihedralIntegrable.integrand_bound α (Real.pi - α) v h0 hb hv).2
    rwa [show α + (Real.pi - α) = Real.pi by ring] at h
  have hle : ∫ v in Set.Ioi (0 : ℝ),
      Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) ≤
      ∫ v in Set.Ioi (0 : ℝ), 4 * (Real.pi - α) / α * Real.exp (-α * v) := by
    first
      | exact setIntegral_mono_on hint hg measurableSet_Ioi hpt
      | exact set_integral_mono_on hint hg measurableSet_Ioi hpt
  have hval : ∫ v in Set.Ioi (0 : ℝ), 4 * (Real.pi - α) / α * Real.exp (-α * v) =
      4 * (Real.pi - α) / α * (1 / α) := by
    first
      | rw [MeasureTheory.integral_const_mul, ioi_integral_exp_neg_mul α h0]
      | rw [MeasureTheory.integral_mul_left, ioi_integral_exp_neg_mul α h0]
  rw [hval] at hle
  calc _ ≤ (1 / Real.pi) * (4 * (Real.pi - α) / α * (1 / α)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * (Real.pi - α) / (Real.pi * α ^ 2) := by
        first | (field_simp; ring) | field_simp | (rw [div_mul_div_comm]; ring)

/-- C9 at the tetrahedral angle. -/
theorem dihedralCoeff_tetra_le :
    dihedralCoeff tetraAngle ≤ 4 * (Real.pi - tetraAngle) / (Real.pi * tetraAngle ^ 2) :=
  dihedralCoeff_le _ tetraAngle_mem.1 tetraAngle_mem.2

/-- C10. The integrand is antitone in `α` on `(0, π)` for `v > 0`. -/
theorem integrand_antitone (α β v : ℝ) (h0 : 0 < α) (hαβ : α ≤ β) (hπ : β < Real.pi)
    (hv : 0 < v) :
    Real.sinh ((Real.pi - β) * v) / (Real.cosh (Real.pi * v) * Real.sinh (β * v)) ≤
      Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) := by
  have hC := Real.cosh_pos (Real.pi * v)
  have hsa : 0 < Real.sinh (α * v) := Real.sinh_pos_iff.mpr (mul_pos h0 hv)
  have hsb : 0 < Real.sinh (β * v) := Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)
  have hnb : 0 ≤ Real.sinh ((Real.pi - β) * v) :=
    (Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)).le
  have hnum : Real.sinh ((Real.pi - β) * v) ≤ Real.sinh ((Real.pi - α) * v) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by linarith) hv.le)
  have hden : Real.sinh (α * v) ≤ Real.sinh (β * v) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hαβ hv.le)
  have hD1 : 0 < Real.cosh (Real.pi * v) * Real.sinh (β * v) := mul_pos hC hsb
  have hD2 : 0 < Real.cosh (Real.pi * v) * Real.sinh (α * v) := mul_pos hC hsa
  rw [div_le_div_iff₀ hD1 hD2]
  have h1 : Real.sinh ((Real.pi - β) * v) * Real.sinh (α * v) ≤
      Real.sinh ((Real.pi - α) * v) * Real.sinh (β * v) :=
    mul_le_mul hnum hden hsa.le (le_trans hnb hnum)
  have h2 := mul_le_mul_of_nonneg_left h1 hC.le
  nlinarith [h2]

/-- C10. `c` is antitone on `(0, π)`. -/
theorem dihedralCoeff_antitone (α β : ℝ) (h0 : 0 < α) (hαβ : α ≤ β) (hπ : β < Real.pi) :
    dihedralCoeff β ≤ dihedralCoeff α := by
  unfold dihedralCoeff
  have hA := DihedralIntegrable.integrableOn_dihedral α h0 (by linarith)
  have hB := DihedralIntegrable.integrableOn_dihedral β (by linarith) hπ
  have hle : ∫ v in Set.Ioi (0 : ℝ),
      Real.sinh ((Real.pi - β) * v) / (Real.cosh (Real.pi * v) * Real.sinh (β * v)) ≤
      ∫ v in Set.Ioi (0 : ℝ),
      Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) := by
    first
      | exact setIntegral_mono_on hB hA measurableSet_Ioi
          (fun v hv => integrand_antitone α β v h0 hαβ hπ hv)
      | exact set_integral_mono_on hB hA measurableSet_Ioi
          (fun v hv => integrand_antitone α β v h0 hαβ hπ hv)
  exact mul_le_mul_of_nonneg_left hle (one_div_pos.mpr Real.pi_pos).le

/-- C10 with C3: `1/(2π) ≤ c_{α₀}`, since `α₀ < π/2`. -/
theorem dihedralCoeff_tetra_ge : 1 / (2 * Real.pi) ≤ dihedralCoeff tetraAngle := by
  have hlt : tetraAngle < Real.pi / 2 := by
    unfold tetraAngle
    first
      | exact Real.arccos_lt_pi_div_two.mpr (by norm_num)
      | (rw [Real.arccos_eq_pi_div_two_sub_arcsin]
         linarith [Real.arcsin_pos.mpr (show (0 : ℝ) < 1 / 3 by norm_num)])
  rw [← RightAngleCalibration.dihedralCoeff_right_angle]
  exact dihedralCoeff_antitone _ _ tetraAngle_mem.1 hlt.le (by linarith [Real.pi_pos])

end SteklovAudit.DihedralBounds
