import Mathlib

/-!
# F2.2 Half-plane Dirichlet-to-Neumann symbol

Roadmap item F2.2 (Foundations), in real form. For `k, φ ∈ ℝ` put
`u k φ x y = cos (k x + φ) · exp (-|k| y)` (the real part of `e^{i(kx+φ)} e^{-|k|y}`; `φ = -π/2`
gives the sine). This file proves, by explicit derivatives:

* `u_xx + u_yy = 0` everywhere (`laplacian_u`), with each derivative given by a `HasDerivAt`
  statement (`hasDerivAt_u_x`, `hasDerivAt_u_xx`, `hasDerivAt_u_y`, `hasDerivAt_u_yy`);
* the boundary relation on `y = 0`: `-∂_y u (x, 0) = |k| · u (x, 0)` (`dtn_symbol`), i.e. the
  half-plane Dirichlet-to-Neumann map acts on `cos (k x + φ)` as multiplication by `|k|`;
* decay: `u k φ x y → 0` as `y → ∞` when `k ≠ 0` (`tendsto_u_atTop`).

What this file does NOT prove: that `u` is the unique bounded harmonic extension, that the DtN map
is the Fourier multiplier `|k|` on `L²` or `H^{1/2}`, or anything about wedges, the tetrahedron,
`[H1]`–`[H6]`, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.Foundations.HalfPlaneDtN

open Real Filter

/-- `cos (k x + φ) · exp (-|k| y)`. -/
noncomputable def u (k φ x y : ℝ) : ℝ := cos (k * x + φ) * exp (-|k| * y)

theorem hasDerivAt_u_x (k φ x y : ℝ) :
    HasDerivAt (fun s => u k φ s y) (-sin (k * x + φ) * (k * 1) * exp (-|k| * y)) x :=
  ((((hasDerivAt_id' x).const_mul k).add_const φ).cos).mul_const (exp (-|k| * y))

theorem hasDerivAt_u_xx (k φ x y : ℝ) :
    HasDerivAt (fun s => -sin (k * s + φ) * (k * 1) * exp (-|k| * y))
      (-(cos (k * x + φ) * (k * 1)) * (k * 1) * exp (-|k| * y)) x :=
  (((((hasDerivAt_id' x).const_mul k).add_const φ).sin.neg).mul_const (k * 1)).mul_const
    (exp (-|k| * y))

theorem hasDerivAt_u_y (k φ x y : ℝ) :
    HasDerivAt (fun t => u k φ x t) (cos (k * x + φ) * (exp (-|k| * y) * (-|k| * 1))) y :=
  (((hasDerivAt_id' y).const_mul (-|k|)).exp).const_mul (cos (k * x + φ))

theorem hasDerivAt_u_yy (k φ x y : ℝ) :
    HasDerivAt (fun t => cos (k * x + φ) * (exp (-|k| * t) * (-|k| * 1)))
      (cos (k * x + φ) * (exp (-|k| * y) * (-|k| * 1) * (-|k| * 1))) y :=
  ((((hasDerivAt_id' y).const_mul (-|k|)).exp).mul_const (-|k| * 1)).const_mul
    (cos (k * x + φ))

/-- **F2.2.** `u_xx + u_yy = 0`. -/
theorem laplacian_u (k φ x y : ℝ) :
    -(cos (k * x + φ) * (k * 1)) * (k * 1) * exp (-|k| * y)
      + cos (k * x + φ) * (exp (-|k| * y) * (-|k| * 1) * (-|k| * 1)) = 0 := by
  have hk : |k| * |k| = k * k := abs_mul_abs_self k
  linear_combination (cos (k * x + φ) * exp (-|k| * y)) * hk

/-- **F2.2.** Dirichlet-to-Neumann symbol: `-∂_y u (x, 0) = |k| · u (x, 0)`. -/
theorem dtn_symbol (k φ x : ℝ) :
    HasDerivAt (fun t => u k φ x t) (-(|k| * u k φ x 0)) 0 :=
  (hasDerivAt_u_y k φ x 0).congr_deriv (by
    simp only [u, mul_zero, Real.exp_zero]
    ring)

/-- **F2.2.** For `k ≠ 0` the extension decays as `y → ∞`. -/
theorem tendsto_u_atTop (k φ x : ℝ) (hk : k ≠ 0) :
    Tendsto (fun y => u k φ x y) atTop (nhds 0) := by
  have hpos : 0 < |k| := abs_pos.mpr hk
  have h1 : Tendsto (fun y : ℝ => -|k| * y) atTop atBot := by
    first
      | exact tendsto_id.const_mul_atTop_of_neg (by linarith)
      | (have h := tendsto_id.const_mul_atTop hpos
         have h' := tendsto_neg_atTop_atBot.comp h
         simpa [Function.comp, neg_mul] using h')
  have h2 : Tendsto (fun y : ℝ => exp (-|k| * y)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 := h2.const_mul (cos (k * x + φ))
  rw [mul_zero] at h3
  exact h3

end SteklovAudit.Foundations.HalfPlaneDtN
