import Mathlib

/-!
# F2.1 Disk Steklov eigenfunctions in polar coordinates

Roadmap item F2.1 (Foundations). For a real exponent `α` put
`u α r θ = r ^ α * cos (α θ)` and `v α r θ = r ^ α * sin (α θ)` (real power `r ^ α`, `r > 0`).
This file proves, by explicit derivatives in `r` and `θ`:

* the polar Laplacian vanishes: `u_rr + u_r / r + u_θθ / r² = 0` for `r > 0`
  (`laplacian_polar_u`, `laplacian_polar_v`), with each derivative given by a `HasDerivAt`
  statement (`hasDerivAt_u_r`, `hasDerivAt_u_rr`, `hasDerivAt_u_θ`, `hasDerivAt_u_θθ`, and the
  same for `v`);
* the Steklov condition on the unit circle: `∂_r u (1, θ) = α · u (1, θ)` and likewise for `v`
  (`steklov_u`, `steklov_v`).

For `α = n ∈ ℕ` these are the disk Steklov eigenfunctions `rⁿ cos nθ`, `rⁿ sin nθ` with eigenvalue
`n`. For non-integer `α` they are the analogous harmonic functions on a sector.

What this file does NOT prove: harmonicity in Cartesian coordinates (the polar form of the
Laplacian is used as a formula, not derived), regularity at `r = 0`, completeness of these
functions, or anything about a Dirichlet-to-Neumann operator as an operator. Nothing about the
paper's tetrahedron, `[H1]`–`[H6]`, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.Foundations.DiskSteklov

open Real

/-- `r ^ α cos (α θ)`. -/
noncomputable def u (α r θ : ℝ) : ℝ := r ^ α * cos (α * θ)

/-- `r ^ α sin (α θ)`. -/
noncomputable def v (α r θ : ℝ) : ℝ := r ^ α * sin (α * θ)

/-- Core algebra of the polar Laplacian for `r ^ α · g` with `g_θθ = -α² g`. -/
theorem lap_core (α g : ℝ) {r : ℝ} (hr : 0 < r) :
    α * ((α - 1) * r ^ (α - 1 - 1)) * g + α * r ^ (α - 1) * g / r
      + r ^ α * (-(α ^ 2 * g)) / r ^ 2 = 0 := by
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : r ^ (α - 1) = r ^ α / r := by rw [Real.rpow_sub hr, Real.rpow_one]
  have h2 : r ^ (α - 1 - 1) = r ^ α / r ^ 2 := by
    rw [Real.rpow_sub hr, Real.rpow_one, h1]
    first
      | (field_simp; ring)
      | field_simp
      | rw [div_div, ← sq]
  rw [h2, h1]
  first
    | (field_simp; ring)
    | field_simp

theorem hasDerivAt_u_r (α θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => u α s θ) (α * r ^ (α - 1) * cos (α * θ)) r :=
  (Real.hasDerivAt_rpow_const (p := α) (Or.inl hr.ne')).mul_const (cos (α * θ))

theorem hasDerivAt_u_rr (α θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => α * s ^ (α - 1) * cos (α * θ))
      (α * ((α - 1) * r ^ (α - 1 - 1)) * cos (α * θ)) r :=
  ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hr.ne')).const_mul α).mul_const _

theorem hasDerivAt_u_θ (α r θ : ℝ) :
    HasDerivAt (fun t => u α r t) (r ^ α * (-sin (α * θ) * (α * 1))) θ :=
  (((hasDerivAt_id' θ).const_mul α).cos).const_mul (r ^ α)

theorem hasDerivAt_u_θθ (α r θ : ℝ) :
    HasDerivAt (fun t => r ^ α * (-sin (α * t) * (α * 1)))
      (r ^ α * (-(cos (α * θ) * (α * 1)) * (α * 1))) θ :=
  ((((hasDerivAt_id' θ).const_mul α).sin.neg).mul_const (α * 1)).const_mul (r ^ α)

/-- **F2.1.** `r ^ α cos (α θ)` satisfies `u_rr + u_r / r + u_θθ / r² = 0` for `r > 0`. -/
theorem laplacian_polar_u (α θ : ℝ) {r : ℝ} (hr : 0 < r) :
    α * ((α - 1) * r ^ (α - 1 - 1)) * cos (α * θ) + α * r ^ (α - 1) * cos (α * θ) / r
      + r ^ α * (-(cos (α * θ) * (α * 1)) * (α * 1)) / r ^ 2 = 0 := by
  linear_combination lap_core α (cos (α * θ)) hr

theorem hasDerivAt_v_r (α θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => v α s θ) (α * r ^ (α - 1) * sin (α * θ)) r :=
  (Real.hasDerivAt_rpow_const (p := α) (Or.inl hr.ne')).mul_const (sin (α * θ))

theorem hasDerivAt_v_rr (α θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => α * s ^ (α - 1) * sin (α * θ))
      (α * ((α - 1) * r ^ (α - 1 - 1)) * sin (α * θ)) r :=
  ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hr.ne')).const_mul α).mul_const _

theorem hasDerivAt_v_θ (α r θ : ℝ) :
    HasDerivAt (fun t => v α r t) (r ^ α * (cos (α * θ) * (α * 1))) θ :=
  (((hasDerivAt_id' θ).const_mul α).sin).const_mul (r ^ α)

theorem hasDerivAt_v_θθ (α r θ : ℝ) :
    HasDerivAt (fun t => r ^ α * (cos (α * t) * (α * 1)))
      (r ^ α * (-sin (α * θ) * (α * 1) * (α * 1))) θ :=
  ((((hasDerivAt_id' θ).const_mul α).cos).mul_const (α * 1)).const_mul (r ^ α)

/-- **F2.1.** `r ^ α sin (α θ)` satisfies `v_rr + v_r / r + v_θθ / r² = 0` for `r > 0`. -/
theorem laplacian_polar_v (α θ : ℝ) {r : ℝ} (hr : 0 < r) :
    α * ((α - 1) * r ^ (α - 1 - 1)) * sin (α * θ) + α * r ^ (α - 1) * sin (α * θ) / r
      + r ^ α * (-sin (α * θ) * (α * 1) * (α * 1)) / r ^ 2 = 0 := by
  linear_combination lap_core α (sin (α * θ)) hr

/-- **F2.1.** Steklov condition on the unit circle: `∂_r u (1, θ) = α · u (1, θ)`. -/
theorem steklov_u (α θ : ℝ) : HasDerivAt (fun s => u α s θ) (α * u α 1 θ) 1 :=
  (hasDerivAt_u_r α θ one_pos).congr_deriv (by simp [u, Real.one_rpow])

/-- **F2.1.** Steklov condition on the unit circle: `∂_r v (1, θ) = α · v (1, θ)`. -/
theorem steklov_v (α θ : ℝ) : HasDerivAt (fun s => v α s θ) (α * v α 1 θ) 1 :=
  (hasDerivAt_v_r α θ one_pos).congr_deriv (by simp [v, Real.one_rpow])

end SteklovAudit.Foundations.DiskSteklov
