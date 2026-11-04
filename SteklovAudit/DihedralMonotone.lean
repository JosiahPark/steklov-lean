import Mathlib
import SteklovAudit.DihedralPositive
import SteklovAudit.RightAngleCalibration

/-!
# D2: the dihedral invariant is antitone, and a lower bound at the tetrahedral angle

Roadmap item D2. Proved here:

* `integrand_anti`: for `0 < α ≤ β < π` and `v > 0`, `f_β(v) ≤ f_α(v)` (numerator
  `sinh((π−α)v)` decreases and denominator `sinh(αv)` increases in `α`);
* `dihedralCoeff_anti`: hence `c_β ≤ c_α` (sharper edges carry a larger edge invariant);
* `tetraAngle_le_right`: the tetrahedral angle `arccos(1/3)` is at most `π/2`;
* `dihedralCoeff_tetra_ge`: with the right-angle calibration C3, `c_{α₀} ≥ c_{π/2} = 1/(2π)`;
* `edge_coeff_ge`: the second coefficient of (11.4) satisfies `6 a c_{α₀} ≥ 3a/π` for `a ≥ 0`.

What this file does NOT prove: an upper bound or a numerical value of `c_{α₀}`; strict
monotonicity; any hypothesis `[H1]`–`[H6]`; the main theorem (Theorem 1.3 / 11.1). The hypothesis
count in STATUS.md is not changed.
-/

namespace SteklovAudit.DihedralMonotone

open MeasureTheory SteklovAudit.MainConditional SteklovAudit.DihedralPositive

/-- Pointwise antitonicity of the integrand of (1.4) in the angle. -/
theorem integrand_anti (α β v : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < Real.pi) (hv : 0 < v) :
    f β v ≤ f α v := by
  unfold f
  have hC : 0 < Real.cosh (Real.pi * v) := Real.cosh_pos _
  have hSa : 0 < Real.sinh (α * v) := Real.sinh_pos_iff.mpr (mul_pos hα hv)
  have hSb : 0 < Real.sinh (β * v) := Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)
  have hnb : 0 ≤ Real.sinh ((Real.pi - β) * v) :=
    (Real.sinh_pos_iff.mpr (mul_pos (by linarith) hv)).le
  have hnum : Real.sinh ((Real.pi - β) * v) ≤ Real.sinh ((Real.pi - α) * v) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by linarith) hv.le)
  have hden : Real.sinh (α * v) ≤ Real.sinh (β * v) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hαβ hv.le)
  have hDa : 0 < Real.cosh (Real.pi * v) * Real.sinh (α * v) := mul_pos hC hSa
  have hDb : 0 < Real.cosh (Real.pi * v) * Real.sinh (β * v) := mul_pos hC hSb
  have key : Real.sinh ((Real.pi - β) * v) * (Real.cosh (Real.pi * v) * Real.sinh (α * v)) ≤
      Real.sinh ((Real.pi - α) * v) * (Real.cosh (Real.pi * v) * Real.sinh (β * v)) := by
    calc Real.sinh ((Real.pi - β) * v) * (Real.cosh (Real.pi * v) * Real.sinh (α * v))
        ≤ Real.sinh ((Real.pi - α) * v) * (Real.cosh (Real.pi * v) * Real.sinh (α * v)) :=
          mul_le_mul_of_nonneg_right hnum hDa.le
      _ ≤ Real.sinh ((Real.pi - α) * v) * (Real.cosh (Real.pi * v) * Real.sinh (β * v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden hC.le) (le_trans hnb hnum)
  rw [div_le_iff₀ hDb, div_mul_eq_mul_div, le_div_iff₀ hDa]
  exact key

/-- D2. `c_β ≤ c_α` for `0 < α ≤ β < π`. -/
theorem dihedralCoeff_anti (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < Real.pi) :
    dihedralCoeff β ≤ dihedralCoeff α := by
  rw [dihedralCoeff_eq, dihedralCoeff_eq]
  refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr Real.pi_pos).le
  exact setIntegral_mono_on (integrableOn_f β (by linarith) hβ)
    (integrableOn_f α hα (by linarith)) measurableSet_Ioi
    (fun v hv => integrand_anti α β v hα hαβ hβ hv)

/-- The tetrahedral angle is at most a right angle. -/
theorem tetraAngle_le_right : tetraAngle ≤ Real.pi / 2 := by
  unfold tetraAngle
  exact Real.arccos_le_pi_div_two.mpr (by norm_num)

/-- D2. `c_{α₀} ≥ c_{π/2} = 1/(2π)`. -/
theorem dihedralCoeff_tetra_ge : 1 / (2 * Real.pi) ≤ dihedralCoeff tetraAngle := by
  rw [← RightAngleCalibration.dihedralCoeff_right_angle]
  exact dihedralCoeff_anti _ _ tetraAngle_mem.1 tetraAngle_le_right
    (by linarith [Real.pi_pos])

/-- D2. The second coefficient of (11.4) is at least `3a/π`. -/
theorem edge_coeff_ge (a : ℝ) (ha : 0 ≤ a) :
    3 * a / Real.pi ≤ 6 * a * dihedralCoeff tetraAngle := by
  have h := dihedralCoeff_tetra_ge
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e : 3 * a / Real.pi = 6 * a * (1 / (2 * Real.pi)) := by
    first
      | (field_simp; ring)
      | field_simp
      | ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by linarith)

end SteklovAudit.DihedralMonotone
