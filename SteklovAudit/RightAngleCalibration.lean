import Mathlib
import SteklovAudit.MainConditional

/-!
# Right-angle calibration of the dihedral invariant (roadmap item C3)

Proves ∫₀^∞ sech(πv) dv = 1/2 by the fundamental theorem of calculus on (0, ∞) with the
antiderivative gd(v) = 2 arctan(exp(πv)) / π, whose derivative is 1 / cosh(πv) ≥ 0. Hence the
dihedral invariant (1.4) at α = π/2 is c_{π/2} = 1/(2π). Along the way it proves that the
integrand of (1.4) at α = π/2 is integrable on (0, ∞), so for this angle the Bochner integral
in MainConditional.dihedralCoeff is not Mathlib's junk value 0.

What this file does NOT prove:
* Integrability of the (1.4) integrand for general 0 < α < π (roadmap item C2), in particular
  at the tetrahedral angle arccos(1/3); only α = π/2 is treated.
* Any hypothesis H1–H6 of MainConditional, or the main theorem (Theorem 1.3 / 11.1).
-/

namespace SteklovAudit.RightAngleCalibration

open MeasureTheory Filter Topology

/-- The antiderivative of sech(πv): gd(v) = 2 arctan(exp(πv)) / π. -/
noncomputable def gd (v : ℝ) : ℝ := 2 * Real.arctan (Real.exp (Real.pi * v)) / Real.pi

theorem hasDerivAt_gd (v : ℝ) : HasDerivAt gd (1 / Real.cosh (Real.pi * v)) v := by
  have h1 : HasDerivAt (fun v : ℝ => Real.pi * v) Real.pi v := by
    simpa using (hasDerivAt_id v).const_mul Real.pi
  have h4 := ((h1.exp.arctan).const_mul 2).div_const Real.pi
  show HasDerivAt (fun v => 2 * Real.arctan (Real.exp (Real.pi * v)) / Real.pi) _ v
  refine h4.congr_deriv ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hE : Real.exp (Real.pi * v) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.cosh_eq, Real.exp_neg]
  first
    | (field_simp; ring)
    | field_simp

theorem sech_pi_nonneg (v : ℝ) : 0 ≤ 1 / Real.cosh (Real.pi * v) :=
  (one_div_pos.mpr (Real.cosh_pos _)).le

theorem tendsto_gd : Tendsto gd atTop (𝓝 1) := by
  have hexp : Tendsto (fun v : ℝ => Real.exp (Real.pi * v)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
  have harc : Tendsto (fun v : ℝ => Real.arctan (Real.exp (Real.pi * v))) atTop
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hexp
  have h := (harc.const_mul 2).div_const Real.pi
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e : 2 * (Real.pi / 2) / Real.pi = 1 := by
    first
      | (field_simp; ring)
      | field_simp
  rw [e] at h
  exact h

theorem gd_zero : gd 0 = 1 / 2 := by
  unfold gd
  rw [mul_zero, Real.exp_zero, Real.arctan_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  first
    | (field_simp; ring)
    | field_simp

/-- sech(πv) is integrable on (0, ∞). -/
theorem integrableOn_sech_pi :
    IntegrableOn (fun v : ℝ => 1 / Real.cosh (Real.pi * v)) (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_gd x) (fun x _ => sech_pi_nonneg x)
    tendsto_gd

/-- ∫₀^∞ sech(πv) dv = 1/2. -/
theorem integral_sech_pi : ∫ v in Set.Ioi (0 : ℝ), 1 / Real.cosh (Real.pi * v) = 1 / 2 := by
  have h : ∫ v in Set.Ioi (0 : ℝ), 1 / Real.cosh (Real.pi * v) = 1 - gd 0 :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hasDerivAt_gd x)
      (fun x _ => sech_pi_nonneg x) tendsto_gd
  rw [h, gd_zero]
  norm_num

theorem sinh_ne_zero_of_pos (x : ℝ) (hx : 0 < x) : Real.sinh x ≠ 0 := by
  have h : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.sinh_eq]
  intro h0
  linarith

/-- At α = π/2 the integrand of (1.4) equals sech(πv) on (0, ∞). -/
theorem integrand_right_angle :
    Set.EqOn (fun v : ℝ => Real.sinh ((Real.pi - Real.pi / 2) * v) /
        (Real.cosh (Real.pi * v) * Real.sinh (Real.pi / 2 * v)))
      (fun v : ℝ => 1 / Real.cosh (Real.pi * v)) (Set.Ioi 0) := by
  intro v hv
  have hv' : 0 < v := hv
  have e : (Real.pi - Real.pi / 2) * v = Real.pi / 2 * v := by ring
  have hs : Real.sinh (Real.pi / 2 * v) ≠ 0 :=
    sinh_ne_zero_of_pos _ (mul_pos (by positivity) hv')
  show Real.sinh ((Real.pi - Real.pi / 2) * v) /
      (Real.cosh (Real.pi * v) * Real.sinh (Real.pi / 2 * v)) = 1 / Real.cosh (Real.pi * v)
  rw [e, mul_comm (Real.cosh _) _, ← div_div, div_self hs]

/-- C2 at α = π/2: the integrand of (1.4) is integrable on (0, ∞). -/
theorem integrableOn_dihedral_right_angle :
    IntegrableOn (fun v : ℝ => Real.sinh ((Real.pi - Real.pi / 2) * v) /
        (Real.cosh (Real.pi * v) * Real.sinh (Real.pi / 2 * v))) (Set.Ioi 0) :=
  integrableOn_sech_pi.congr_fun integrand_right_angle.symm measurableSet_Ioi

/-- C3. Right-angle calibration: c_{π/2} = 1/(2π). -/
theorem dihedralCoeff_right_angle :
    SteklovAudit.MainConditional.dihedralCoeff (Real.pi / 2) = 1 / (2 * Real.pi) := by
  unfold SteklovAudit.MainConditional.dihedralCoeff
  rw [setIntegral_congr_fun measurableSet_Ioi integrand_right_angle, integral_sech_pi]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  first
    | (field_simp; ring)
    | field_simp
    | ring

end SteklovAudit.RightAngleCalibration
