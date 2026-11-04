import Mathlib
import SteklovAudit.MainConditional

/-!
# Section 3: the inverse sector operator and its trace (the elementary steps)

Section 3 of the paper computes `I_α = Tr(B_α − B_π)` through the Kontorovich–Lebedev transform.
The operator statements (the transform, (3.3), trace-class convergence of (3.7)) need the Macdonald
functions `K_{iv}`, which are not in Mathlib. This module proves every step of Section 3.1–3.2 that
is a statement about real or complex numbers:

* (3.2) → (3.6): the endpoint matrix `[[coth x, csch x], [csch x, coth x]]` has eigenvalues
  `coth x ± csch x = coth(x/2), tanh(x/2)` (`endpoint_eigen_plus`, `endpoint_eigen_minus`);
* (3.4)–(3.5): the gamma step `π Γ(1/2 − iv) Γ(1/2 + iv) / 4 = π² / (4 cosh πv)`
  (`gamma_reflection_imag`, `norm_identity_constant`); the double integral (3.5) itself is not
  formalized;
* (3.7) → (3.8): the rank-one weight `(2/π²) sinh(πv) · π²/(4 cosh πv) = tanh(πv)/2`
  (`rank_one_weight`);
* signs: the even perturbation is positive and the odd one negative for `0 < α < π`
  (`even_pos`, `odd_neg`), as asserted after (3.8);
* (3.8): the summed absolute integrand is `tanh(πv)(csch αv − csch πv)` (`abs_parity_sum`);
* (3.9): summing the two parity traces gives `tanh(πv)(coth αv − coth πv)` (`parity_trace_sum`),
  which equals `sinh((π − α)v)/(cosh(πv) sinh(αv))` (`coth_form`); hence
  `dihedralCoeff α = (1/π) ∫₀^∞ tanh(πv)(coth αv − coth πv) dv` (`dihedralCoeff_coth_form`);
* the integrand of (3.9) tends to `(π − α)/α` as `v → 0⁺` (`integrand_tendsto_zero`).

What this module does NOT prove: that `B_α − B_π` is trace class, that its trace is the integral
(3.9) (Theorem 1.1), the norm identity (3.4) for `K_{iv}`, or anything in Sections 3.3 onward.
-/

namespace SteklovAudit.SectorTrace

open Filter Topology SteklovAudit.MainConditional

/-- `coth x = cosh x / sinh x`. -/
noncomputable def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- `csch x = 1 / sinh x`. -/
noncomputable def csch (x : ℝ) : ℝ := 1 / Real.sinh x


theorem sinh_ne (x : ℝ) (hx : 0 < x) : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'

theorem endpoint_eigen_plus (x : ℝ) (hx : 0 < x) : coth x + csch x = coth (x / 2) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by ring⟩
  have hy : 0 < y := by linarith
  have hs := sinh_ne y hy
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  unfold coth csch
  rw [show 2 * y / 2 = y by ring, Real.sinh_two_mul, Real.cosh_two_mul, ← add_div,
    div_eq_div_iff (by simp [hs, hc]) hs]
  linear_combination (-Real.sinh y) * Real.cosh_sq y

theorem endpoint_eigen_minus (x : ℝ) (hx : 0 < x) : coth x - csch x = Real.tanh (x / 2) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by ring⟩
  have hy : 0 < y := by linarith
  have hs := sinh_ne y hy
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  unfold coth csch
  rw [show 2 * y / 2 = y by ring, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul,
    div_sub_div_same, div_eq_div_iff (by simp [hs, hc]) hc]
  linear_combination (Real.cosh y) * Real.cosh_sq y

theorem multiplier_sum (y : ℝ) (hy : 0 < y) : coth y + Real.tanh y = 2 * coth (2 * y) := by
  have hs := sinh_ne y hy
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  unfold coth
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp

theorem multiplier_diff (y : ℝ) (hy : 0 < y) : coth y - Real.tanh y = 2 * csch (2 * y) := by
  have hs := sinh_ne y hy
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  unfold coth csch
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  field_simp
  linear_combination Real.cosh_sq y


theorem rank_one_weight (v : ℝ) :
    2 / Real.pi ^ 2 * Real.sinh (Real.pi * v) * (Real.pi ^ 2 / (4 * Real.cosh (Real.pi * v))) =
      1 / 2 * Real.tanh (Real.pi * v) := by
  have hc := (Real.cosh_pos (Real.pi * v)).ne'
  have hp := Real.pi_pos.ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

theorem coth_strictAnti {a b : ℝ} (ha : 0 < a) (hab : a < b) : coth b < coth a := by
  unfold coth
  have hsa := Real.sinh_pos_iff.mpr ha
  have hsb := Real.sinh_pos_iff.mpr (ha.trans hab)
  rw [div_lt_div_iff₀ hsb hsa]
  have h := Real.sinh_sub b a
  have hpos : 0 < Real.sinh (b - a) := Real.sinh_pos_iff.mpr (by linarith)
  nlinarith

theorem tanh_lt_tanh {a b : ℝ} (hab : a < b) : Real.tanh a < Real.tanh b := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)]
  have h := Real.sinh_sub b a
  have hpos : 0 < Real.sinh (b - a) := Real.sinh_pos_iff.mpr (by linarith)
  nlinarith

/-- Even angular multiplier (3.6): `m_{α,+}(v) = coth(αv/2)`. -/
noncomputable def mPlus (α v : ℝ) : ℝ := coth (α * v / 2)
/-- Odd angular multiplier (3.6): `m_{α,−}(v) = tanh(αv/2)`. -/
noncomputable def mMinus (α v : ℝ) : ℝ := Real.tanh (α * v / 2)

theorem even_pos (α v : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) (hv : 0 < v) :
    0 < mPlus α v - mPlus Real.pi v := by
  unfold mPlus
  have := coth_strictAnti (a := α * v / 2) (b := Real.pi * v / 2) (by positivity)
    (by nlinarith)
  linarith

theorem odd_neg (α v : ℝ) (hπ : α < Real.pi) (hv : 0 < v) :
    mMinus α v - mMinus Real.pi v < 0 := by
  unfold mMinus
  have := tanh_lt_tanh (a := α * v / 2) (b := Real.pi * v / 2) (by nlinarith)
  linarith

theorem parity_trace_sum (α v : ℝ) (h0 : 0 < α) (hv : 0 < v) :
    1 / 2 * Real.tanh (Real.pi * v) * (mPlus α v - mPlus Real.pi v) +
      1 / 2 * Real.tanh (Real.pi * v) * (mMinus α v - mMinus Real.pi v) =
      Real.tanh (Real.pi * v) * (coth (α * v) - coth (Real.pi * v)) := by
  have h1 := multiplier_sum (α * v / 2) (by positivity)
  have h2 := multiplier_sum (Real.pi * v / 2) (by have := Real.pi_pos; positivity)
  rw [show 2 * (α * v / 2) = α * v by ring] at h1
  rw [show 2 * (Real.pi * v / 2) = Real.pi * v by ring] at h2
  unfold mPlus mMinus
  linear_combination (1 / 2 * Real.tanh (Real.pi * v)) * h1 -
    (1 / 2 * Real.tanh (Real.pi * v)) * h2

theorem coth_form (α v : ℝ) (h0 : 0 < α) (hv : 0 < v) :
    Real.tanh (Real.pi * v) * (coth (α * v) - coth (Real.pi * v)) =
      Real.sinh ((Real.pi - α) * v) / (Real.cosh (Real.pi * v) * Real.sinh (α * v)) := by
  have hsa := sinh_ne (α * v) (by positivity)
  have hsp := sinh_ne (Real.pi * v) (by have := Real.pi_pos; positivity)
  have hc := (Real.cosh_pos (Real.pi * v)).ne'
  unfold coth
  rw [Real.tanh_eq_sinh_div_cosh, show (Real.pi - α) * v = Real.pi * v - α * v by ring,
    Real.sinh_sub]
  field_simp

theorem abs_parity_sum (α v : ℝ) (h0 : 0 < α) (hπ : α < Real.pi) (hv : 0 < v) :
    1 / 2 * Real.tanh (Real.pi * v) * |mPlus α v - mPlus Real.pi v| +
      1 / 2 * Real.tanh (Real.pi * v) * |mMinus α v - mMinus Real.pi v| =
      Real.tanh (Real.pi * v) * (csch (α * v) - csch (Real.pi * v)) := by
  rw [abs_of_pos (even_pos α v h0 hπ hv), abs_of_neg (odd_neg α v hπ hv)]
  have h1 := multiplier_diff (α * v / 2) (by positivity)
  have h2 := multiplier_diff (Real.pi * v / 2) (by have := Real.pi_pos; positivity)
  rw [show 2 * (α * v / 2) = α * v by ring] at h1
  rw [show 2 * (Real.pi * v / 2) = Real.pi * v by ring] at h2
  unfold mPlus mMinus
  linear_combination (1 / 2 * Real.tanh (Real.pi * v)) * h1 -
    (1 / 2 * Real.tanh (Real.pi * v)) * h2


theorem tendsto_sinh_div (c : ℝ) :
    Tendsto (fun v : ℝ => Real.sinh (c * v) / v) (𝓝[≠] 0) (𝓝 c) := by
  have hd : HasDerivAt (fun v : ℝ => Real.sinh (c * v)) (Real.cosh (c * 0) * (c * 1)) 0 :=
    ((hasDerivAt_id 0).const_mul c).sinh
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  simp only [mul_zero, Real.cosh_zero, Real.sinh_zero, sub_zero, zero_add, one_mul, mul_one,
    smul_eq_mul] at hd
  refine hd.congr' (Eventually.of_forall fun v => ?_)
  simp [div_eq_inv_mul]

theorem integrand_tendsto_zero (α : ℝ) (h0 : 0 < α) :
    Tendsto (fun v : ℝ => Real.sinh ((Real.pi - α) * v) /
      (Real.cosh (Real.pi * v) * Real.sinh (α * v))) (𝓝[>] 0) (𝓝 ((Real.pi - α) / α)) := by
  have hcosh : Tendsto (fun v : ℝ => Real.cosh (Real.pi * v)) (𝓝[≠] 0) (𝓝 1) := by
    have : Continuous fun v : ℝ => Real.cosh (Real.pi * v) :=
      Real.continuous_cosh.comp (continuous_const.mul continuous_id)
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hq := (tendsto_sinh_div (Real.pi - α)).div (hcosh.mul (tendsto_sinh_div α))
    (by simp [h0.ne'])
  rw [one_mul] at hq
  refine (hq.congr' ?_).mono_left (nhdsWithin_mono _ fun v (hv : 0 < v) => hv.ne')
  filter_upwards [self_mem_nhdsWithin] with v (hv : v ≠ 0)
  have hs : Real.sinh (α * v) ≠ 0 := by
    intro h
    have := Real.sinh_injective (h.trans Real.sinh_zero.symm)
    simp [h0.ne', hv] at this
  simp only [Pi.div_apply]
  field_simp


theorem gamma_reflection_imag (v : ℝ) :
    Complex.Gamma (1 / 2 + v * Complex.I) * Complex.Gamma (1 / 2 - v * Complex.I) =
      (Real.pi : ℂ) / (Real.cosh (Real.pi * v) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + v * Complex.I)
  rw [show (1 : ℂ) - (1 / 2 + v * Complex.I) = 1 / 2 - v * Complex.I by ring] at h
  rw [h]
  congr 1
  rw [show (Real.pi : ℂ) * (1 / 2 + v * Complex.I) =
      ((Real.pi * v : ℝ) : ℂ) * Complex.I + Real.pi / 2 by push_cast; ring,
    Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

theorem norm_identity_constant (v : ℝ) :
    (Real.pi : ℂ) * (Complex.Gamma (1 / 2 - v * Complex.I) * Complex.Gamma (1 / 2 + v * Complex.I)) / 4 =
      ((Real.pi ^ 2 / (4 * Real.cosh (Real.pi * v)) : ℝ) : ℂ) := by
  rw [mul_comm (Complex.Gamma _), gamma_reflection_imag]
  have hc : (Real.cosh (Real.pi * v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  push_cast
  field_simp

/-- (3.9), first form: `dihedralCoeff α = (1/π) ∫₀^∞ tanh(πv)(coth αv − coth πv) dv`. -/
theorem dihedralCoeff_coth_form (α : ℝ) (h0 : 0 < α) :
    dihedralCoeff α = 1 / Real.pi * ∫ v in Set.Ioi (0 : ℝ),
      Real.tanh (Real.pi * v) * (coth (α * v) - coth (Real.pi * v)) := by
  unfold dihedralCoeff
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun v (hv : 0 < v) => (coth_form α v h0 hv).symm)

end SteklovAudit.SectorTrace
