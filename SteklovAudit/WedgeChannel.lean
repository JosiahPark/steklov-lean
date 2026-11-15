import Mathlib
import SteklovAudit.SectorTrace

/-!
# Continuation 176: two-channel bounds for the low-axial-frequency wedge form (scalar part)

Continuation 176 (2026-11-10) bounds a face-only variational model on a straight wedge of opening
`α > 0` at axial frequency `κ`, with `m = |κ| e^t`, split into the symmetric channel `s = (f+g)/√2`
and the antisymmetric channel `d = (f-g)/√2`. The angular minimization in its Theorem 176.1 leads to
the endpoint matrix whose eigenvalues are `m tanh(αm/2)` and `m coth(αm/2)`; that eigenvalue step is
already `SectorTrace.endpoint_eigen_minus` / `endpoint_eigen_plus`. This file proves the scalar rest:

* `channel_sum`, `channel_difference`: the `√2` channel change preserves `f² + g²`, and
  `(f-g)² = 2 d²`;
* Theorem 176.2: `x/(1+x) ≤ tanh x ≤ x` (`div_one_add_le_tanh`, `tanh_le_id`) for `x ≥ 0`, and
  `1/x ≤ coth x ≤ 1 + 1/x` (`inv_le_coth`, `coth_le_one_add_inv`) for `x > 0`;
* in multiplier form: `αm²/(2+αm) ≤ m tanh(αm/2) ≤ αm²/2` (`sym_lower`, `sym_upper`, `m ≥ 0`) and
  `2/α ≤ m coth(αm/2) ≤ 2/α + m` (`anti_lower`, `anti_upper`, `m > 0`);
* `channel_lower`: the pointwise two-channel lower bound of 176.2;
* `antisym_physical`: the scalar step of Corollary 176.3.

What this file does NOT prove: the variational Theorem 176.1 itself (the angular minimization,
Sobolev traces, the infimum over extensions), any statement about integrals in `t`, the `m = 0`
extensions (here `coth 0 = 0` by Lean's convention, so the antisymmetric bounds are stated for
`m > 0`), and any comparison with the Dirichlet-to-Neumann operator of the tetrahedron. It moves no
[H…] input; Theorem 1.3 / 11.1 remains conditional on named inputs.
-/

namespace SteklovAudit.WedgeChannel

open SteklovAudit.SectorTrace

/-- `(f+g)/√2` and `(f-g)/√2` preserve `f² + g²`. -/
theorem channel_sum (f g : ℝ) :
    ((f + g) / Real.sqrt 2) ^ 2 + ((f - g) / Real.sqrt 2) ^ 2 = f ^ 2 + g ^ 2 := by
  rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- `(f-g)² = 2 d²` with `d = (f-g)/√2`. -/
theorem channel_difference (f g : ℝ) :
    (f - g) ^ 2 = 2 * ((f - g) / Real.sqrt 2) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- `sinh x ≤ x cosh x` for `x ≥ 0` (the derivative of `x cosh x - sinh x` is `x sinh x`). -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y * Real.cosh y - Real.sinh y) (y * Real.sinh y) y := by
    intro y
    have h1 := ((hasDerivAt_id' y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
    first
      | exact h1.congr_deriv (by ring)
      | (convert h1 using 1; ring)
  have hmono : MonotoneOn (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 0 < y := by
        first
          | simpa using hy
          | (rw [interior_Ici] at hy; exact hy)
      rw [(hd y).deriv]
      exact mul_nonneg hy'.le (Real.sinh_nonneg_iff.mpr hy'.le)
  have key := hmono (Set.left_mem_Ici) (Set.mem_Ici.mpr hx) hx
  simp only [Real.sinh_zero, Real.cosh_zero, zero_mul, sub_zero] at key
  linarith

/-- `x cosh x ≤ (1 + x) sinh x` for `x ≥ 0` (from `e^{2x} ≥ 1 + 2x`). -/
theorem mul_cosh_le {x : ℝ} (hx : 0 ≤ x) : x * Real.cosh x ≤ (1 + x) * Real.sinh x := by
  have hee : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h2 : x + x + 1 ≤ Real.exp x * Real.exp x := by
    rw [← Real.exp_add]; exact Real.add_one_le_exp (x + x)
  have he' : 0 < Real.exp (-x) := Real.exp_pos _
  have h3 : Real.exp (-x) * (Real.exp x * Real.exp x) = Real.exp x := by
    rw [← mul_assoc, mul_comm (Real.exp (-x)), hee, one_mul]
  have h4 := mul_le_mul_of_nonneg_left h2 he'.le
  rw [Real.sinh_eq, Real.cosh_eq]
  nlinarith [h3, h4, hee]

/-- 176.2: `tanh x ≤ x` for `x ≥ 0`. -/
theorem tanh_le_id {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  exact sinh_le_mul_cosh hx

/-- 176.2: `x / (1 + x) ≤ tanh x` for `x ≥ 0`. -/
theorem div_one_add_le_tanh {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_div_iff₀ (by linarith) (Real.cosh_pos x)]
  nlinarith [mul_cosh_le hx]

/-- 176.2: `1 / x ≤ coth x` for `x > 0`. -/
theorem inv_le_coth {x : ℝ} (hx : 0 < x) : 1 / x ≤ coth x := by
  unfold coth
  rw [div_le_div_iff₀ hx (Real.sinh_pos_iff.mpr hx)]
  nlinarith [sinh_le_mul_cosh hx.le]

/-- 176.2: `coth x ≤ 1 + 1 / x` for `x > 0`. -/
theorem coth_le_one_add_inv {x : ℝ} (hx : 0 < x) : coth x ≤ 1 + 1 / x := by
  have e : 1 + 1 / x = (x + 1) / x := by rw [add_div, div_self hx.ne']
  rw [e]
  unfold coth
  rw [div_le_div_iff₀ (Real.sinh_pos_iff.mpr hx) hx]
  nlinarith [mul_cosh_le hx.le]

variable {α m : ℝ}

/-- `m · 1/(αm/2) = 2/α`. -/
theorem m_mul_inv (hα : 0 < α) (hm : 0 < m) : m * (1 / (α * m / 2)) = 2 / α := by
  have hα0 : α ≠ 0 := hα.ne'
  have hm0 : m ≠ 0 := hm.ne'
  first
    | (field_simp; ring)
    | field_simp

/-- 176.2, symmetric channel, lower bound (valid at `m = 0`). -/
theorem sym_lower (hα : 0 < α) (hm : 0 ≤ m) :
    α * m ^ 2 / (2 + α * m) ≤ m * Real.tanh (α * m / 2) := by
  have h := div_one_add_le_tanh (x := α * m / 2) (by positivity)
  rw [div_le_iff₀ (by positivity)] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * m)]

/-- 176.2, symmetric channel, upper bound. -/
theorem sym_upper (hα : 0 < α) (hm : 0 ≤ m) : m * Real.tanh (α * m / 2) ≤ α * m ^ 2 / 2 := by
  have h := mul_le_mul_of_nonneg_left (tanh_le_id (x := α * m / 2) (by positivity)) hm
  nlinarith [h]

/-- 176.2, antisymmetric channel: the `κ`-independent gap `2/α`. -/
theorem anti_lower (hα : 0 < α) (hm : 0 < m) : 2 / α ≤ m * coth (α * m / 2) := by
  have h := mul_le_mul_of_nonneg_left (inv_le_coth (x := α * m / 2) (by positivity)) hm.le
  have e := m_mul_inv hα hm
  linarith [h, e]

/-- 176.2, antisymmetric channel, upper bound. -/
theorem anti_upper (hα : 0 < α) (hm : 0 < m) : m * coth (α * m / 2) ≤ 2 / α + m := by
  have h := mul_le_mul_of_nonneg_left (coth_le_one_add_inv (x := α * m / 2) (by positivity)) hm.le
  have e := m_mul_inv hα hm
  nlinarith [h, e]

/-- 176.2, pointwise two-channel lower bound. -/
theorem channel_lower (hα : 0 < α) (hm : 0 < m) (s d : ℝ) :
    α * m ^ 2 / (2 + α * m) * s ^ 2 + 2 / α * d ^ 2 ≤
      m * Real.tanh (α * m / 2) * s ^ 2 + m * coth (α * m / 2) * d ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right (sym_lower hα hm.le) (sq_nonneg s)
  have h2 := mul_le_mul_of_nonneg_right (anti_lower hα hm) (sq_nonneg d)
  linarith

/-- Corollary 176.3, scalar step: `W ≤ e^b D` and `Q ≥ (2/α) D` give `Q ≥ (2e^{-b}/α) W`. -/
theorem antisym_physical {b W D Q : ℝ} (hα : 0 < α) (hW : W ≤ Real.exp b * D)
    (hQ : 2 / α * D ≤ Q) : 2 * Real.exp (-b) / α * W ≤ Q := by
  have hc : 0 ≤ 2 * Real.exp (-b) / α := by positivity
  have h1 := mul_le_mul_of_nonneg_left hW hc
  have hee : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add]; simp
  have h2 : 2 * Real.exp (-b) / α * (Real.exp b * D) = 2 / α * D := by
    calc 2 * Real.exp (-b) / α * (Real.exp b * D)
        = 2 / α * D * (Real.exp (-b) * Real.exp b) := by ring
      _ = 2 / α * D := by rw [hee, mul_one]
  linarith

end SteklovAudit.WedgeChannel
