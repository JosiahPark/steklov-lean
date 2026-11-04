import Mathlib
import SteklovAudit.DihedralBounds
import SteklovAudit.DihedralBracket

/-!
# A closed form at α = π/3 and a sharper upper bound for the tetrahedral edge coefficient

At `α = π/3` the integrand of (1.4) is `sinh(2πv/3)/(cosh(πv) sinh(πv/3)) = 2w/(w² − w + 1)` with
`w = e^{2πv/3}`, which has the elementary antiderivative `(2√3/π) arctan((2w − 1)/√3)`. Hence

* `dihedralCoeff_pi_div_three`: `c_{π/3} = 2√3/(3π) = 2/(π√3) ≈ 0.3676`.

Since `c` is antitone on `(0, π)` (C10, `DihedralBounds.dihedralCoeff_antitone`) and `π/3 < α₀`
(C11, `DihedralBracket.pi_div_three_lt_tetraAngle`), this improves the upper bound `24/π² ≈ 2.43` of C11:

* `dihedralCoeff_tetra_bracket_third`: `1/(2π) ≤ c_{α₀} ≤ 2√3/(3π)`;
* `dihedralCoeff_tetra_decimal`: `0.158 < c_{α₀} < 0.368`.

The paper's value (1.5), `c_{α₀} ≈ 0.26941`, lies in this interval. The paper says its decimals are not
certified; this module certifies only the interval above, not the decimals.

What this module does NOT prove: the decimals in (1.5), Theorem 1.1, or any hypothesis H1–H6.
-/

namespace SteklovAudit.DihedralThird

open MeasureTheory Set Filter Topology SteklovAudit.MainConditional

/-- `wThird(v) = e^{2πv/3}`. -/
noncomputable def wThird (v : ℝ) : ℝ := Real.exp (2 * Real.pi * v / 3)

/-- Antiderivative `G(v) = (2√3/π) arctan((2w − 1)/√3)`. -/
noncomputable def GThird (v : ℝ) : ℝ :=
  2 * Real.sqrt 3 / Real.pi * Real.arctan ((2 * wThird v - 1) / Real.sqrt 3)

theorem integrand_third (v : ℝ) (hv : 0 < v) :
    Real.sinh ((Real.pi - Real.pi / 3) * v) / (Real.cosh (Real.pi * v) * Real.sinh (Real.pi / 3 * v)) =
      2 * wThird v / (wThird v ^ 2 - wThird v + 1) := by
  obtain ⟨u, hu⟩ : ∃ u, u = Real.pi * v / 3 := ⟨_, rfl⟩
  have a1 : (Real.pi - Real.pi / 3) * v = 2 * u := by rw [hu]; ring
  have a2 : Real.pi * v = 3 * u := by rw [hu]; ring
  have a3 : Real.pi / 3 * v = u := by rw [hu]; ring
  have a4 : 2 * Real.pi * v / 3 = 2 * u := by rw [hu]; ring
  rw [a1, a2, a3, wThird, a4]
  have hu0 : 0 < u := by rw [hu]; have := Real.pi_pos; positivity
  set y := Real.exp u with hy
  have hy1 : 1 < y := Real.one_lt_exp_iff.mpr hu0
  have hy0 : 0 < y := by linarith
  have e2 : Real.exp (2 * u) = y ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (3 * u) = y ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.sinh_eq, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, Real.exp_neg, Real.exp_neg, e2, e3, ← hy]
  have h1 : y - y⁻¹ ≠ 0 := by
    have : y⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy1
    linarith
  have h2 : y ^ 4 - y ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg (y ^ 2 - 1)]
  have h3 : y ^ 3 + (y ^ 3)⁻¹ ≠ 0 := by positivity
  have h4 : y ^ 2 - 1 ≠ 0 := by nlinarith
  have h5 : y ^ 2 - (y ^ 2)⁻¹ ≠ 0 := by
    have h6 : 1 < y ^ 2 := by nlinarith
    have : (y ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h6
    linarith
  field_simp
  rw [eq_div_iff (by nlinarith [sq_nonneg (y ^ 2 - 1)])]
  ring


theorem hasDerivAt_G (v : ℝ) : HasDerivAt GThird (2 * wThird v / (wThird v ^ 2 - wThird v + 1)) v := by
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hw : HasDerivAt wThird (wThird v * (2 * Real.pi / 3)) v := by
    have := ((hasDerivAt_id v).const_mul (2 * Real.pi / 3)).exp
    convert this using 1
    · funext x; simp [wThird]; ring_nf
    · simp [wThird]; ring_nf
  have hg : HasDerivAt (fun x => (2 * wThird x - 1) / Real.sqrt 3)
      (2 * (wThird v * (2 * Real.pi / 3)) / Real.sqrt 3) v :=
    ((hw.const_mul 2).sub_const 1).div_const _
  have := (hg.arctan).const_mul (2 * Real.sqrt 3 / Real.pi)
  show HasDerivAt (fun y => 2 * Real.sqrt 3 / Real.pi * Real.arctan ((2 * wThird y - 1) / Real.sqrt 3)) _ v
  convert this using 1
  have hp := Real.pi_pos
  have hq : wThird v ^ 2 - wThird v + 1 ≠ 0 := by nlinarith [sq_nonneg (wThird v - 1 / 2)]
  have hq' : 1 - wThird v + wThird v ^ 2 ≠ 0 := by nlinarith [sq_nonneg (wThird v - 1 / 2)]
  have h3 : (3 : ℝ) + (2 * wThird v - 1) ^ 2 ≠ 0 := by positivity
  have h3' : 1 + (2 * wThird v - 1) ^ 2 / 3 ≠ 0 := by positivity
  rw [div_pow, hs2]
  field_simp
  rw [div_eq_iff (by nlinarith [sq_nonneg (wThird v - 1 / 2)])]
  ring

theorem GThird_zero : GThird 0 = Real.sqrt 3 / 3 := by
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  rw [GThird, wThird, mul_zero, zero_div, Real.exp_zero, show (2 * 1 - 1 : ℝ) / Real.sqrt 3 = (Real.sqrt 3)⁻¹ by norm_num, Real.arctan_inv_sqrt_three]
  have := Real.pi_pos
  field_simp
  ring

theorem tendsto_G : Tendsto GThird atTop (𝓝 (Real.sqrt 3)) := by
  have hw : Tendsto wThird atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_id.const_mul_atTop (by positivity : (0:ℝ) < 2 * Real.pi)).atTop_div_const (by norm_num))
  have hg : Tendsto (fun x => (2 * wThird x - 1) / Real.sqrt 3) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-1) (hw.const_mul_atTop (by norm_num))).atTop_div_const
      (by positivity)
  have ha := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hg
  have := ha.const_mul (2 * Real.sqrt 3 / Real.pi)
  have e : 2 * Real.sqrt 3 / Real.pi * (Real.pi / 2) = Real.sqrt 3 := by
    have := Real.pi_pos
    field_simp
  rw [e] at this
  exact this


theorem integral_third :
    ∫ v in Ioi (0:ℝ), 2 * wThird v / (wThird v ^ 2 - wThird v + 1) = 2 * Real.sqrt 3 / 3 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (hasDerivAt_G 0).continuousAt.continuousWithinAt
    (fun v _ => hasDerivAt_G v) (fun v _ => ?_) tendsto_G, GThird_zero]
  · ring
  · have : 0 < wThird v := Real.exp_pos _
    have : 0 < wThird v ^ 2 - wThird v + 1 := by nlinarith [sq_nonneg (wThird v - 1 / 2)]
    positivity

/-- `c_{π/3} = 2√3/(3π) = 2/(π√3)`. -/
theorem dihedralCoeff_pi_div_three :
    dihedralCoeff (Real.pi / 3) = 2 * Real.sqrt 3 / (3 * Real.pi) := by
  unfold dihedralCoeff
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v (hv : 0 < v) => integrand_third v hv),
    integral_third]
  have := Real.pi_pos
  field_simp


/-- `c_{α₀} ≤ c_{π/3} = 2√3/(3π)`, by antitonicity and `π/3 < α₀`. -/
theorem dihedralCoeff_tetra_le_third : dihedralCoeff tetraAngle ≤ 2 * Real.sqrt 3 / (3 * Real.pi) := by
  rw [← dihedralCoeff_pi_div_three]
  exact DihedralBounds.dihedralCoeff_antitone _ _ (by have := Real.pi_pos; positivity)
    DihedralBracket.pi_div_three_lt_tetraAngle.le tetraAngle_mem.2

/-- Bracket for the tetrahedral edge coefficient: `1/(2π) ≤ c_{α₀} ≤ 2√3/(3π)`. -/
theorem dihedralCoeff_tetra_bracket_third :
    1 / (2 * Real.pi) ≤ dihedralCoeff tetraAngle ∧
      dihedralCoeff tetraAngle ≤ 2 * Real.sqrt 3 / (3 * Real.pi) :=
  ⟨DihedralBounds.dihedralCoeff_tetra_ge, dihedralCoeff_tetra_le_third⟩

theorem upper_num : 2 * Real.sqrt 3 / (3 * Real.pi) < 0.368 := by
  have hp := Real.pi_gt_d2
  have hs : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem lower_num : (0.158 : ℝ) < 1 / (2 * Real.pi) := by
  have hp := Real.pi_lt_d2
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- Decimal form: `0.158 < c_{α₀} < 0.368` (the paper's (1.5) gives ≈ 0.26941). -/
theorem dihedralCoeff_tetra_decimal :
    (0.158 : ℝ) < dihedralCoeff tetraAngle ∧ dihedralCoeff tetraAngle < 0.368 :=
  ⟨lower_num.trans_le dihedralCoeff_tetra_bracket_third.1,
    dihedralCoeff_tetra_bracket_third.2.trans_lt upper_num⟩

end SteklovAudit.DihedralThird
