import Mathlib

/-!
# G142. Affine harmonic functions on `ℝ³` and their face normal derivatives

Roadmap item G142. For `c p q r : ℝ` put `u c p q r x y z = c + p x + q y + r z`. On the reference
tetrahedron of `TetraAffineFlux` (vertices `(1,1,1)`, `(1,−1,−1)`, `(−1,1,−1)`, `(−1,−1,1)`; the face
opposite the vertex `v` has outward unit normal `−v / √3`) this file proves, by explicit derivatives:

* the first partials are `p`, `q`, `r` (`hasDerivAt_u_x`, `hasDerivAt_u_y`, `hasDerivAt_u_z`);
* every pure second partial vanishes, so `Δu = 0` (`second_partials_zero`, `laplacian_zero`);
* the directional derivative along `n` is `p n₁ + q n₂ + r n₃` at every point (`normal_derivative_at`,
  `normal_derivative`), hence constant on each face;
* the four face values `flux` with `n = −v / √3` (`face_flux_values`, e.g. `−(p + q + r) / √3` on the
  face opposite `(1,1,1)`), `face_normal_derivative` linking them to the derivative, and
  `face_flux_sum_zero` (the four values sum to `0`, the discrete divergence theorem for affine `u`,
  all faces having equal area).

What this file does NOT prove: that `u|∂T` lies in the Dirichlet-to-Neumann domain (`H^{1/2}`
traces, weak normal derivative), that the DtN map sends the trace to these values, the Green
identity, Parseval for the four probes, any of `[H1]`–`[H6]`, (7.29), or Theorem 1.3 / 11.1. Those
remain paper steps (`docs/affine-dtn-cutoff.md`).
-/

namespace SteklovAudit.Foundations.AffineHarmonic3D

open Real

/-- The affine function `c + p x + q y + r z`. -/
noncomputable def u (c p q r x y z : ℝ) : ℝ := c + p * x + q * y + r * z

theorem hasDerivAt_u_x (c p q r x y z : ℝ) :
    HasDerivAt (fun s => u c p q r s y z) p x := by
  have h : HasDerivAt (fun s => c + p * s + q * y + r * z) (p * 1) x :=
    ((((hasDerivAt_id' x).const_mul p).const_add c).add_const (q * y)).add_const (r * z)
  rw [mul_one] at h
  exact h

theorem hasDerivAt_u_y (c p q r x y z : ℝ) :
    HasDerivAt (fun t => u c p q r x t z) q y := by
  have h : HasDerivAt (fun t => c + p * x + q * t + r * z) (q * 1) y :=
    (((hasDerivAt_id' y).const_mul q).const_add (c + p * x)).add_const (r * z)
  rw [mul_one] at h
  exact h

theorem hasDerivAt_u_z (c p q r x y z : ℝ) :
    HasDerivAt (fun w => u c p q r x y w) r z := by
  have h : HasDerivAt (fun w => c + p * x + q * y + r * w) (r * 1) z :=
    ((hasDerivAt_id' z).const_mul r).const_add (c + p * x + q * y)
  rw [mul_one] at h
  exact h

/-- Each pure second partial of `u` is `0`. -/
theorem second_partials_zero (c p q r x y z : ℝ) :
    deriv (fun s' => deriv (fun s => u c p q r s y z) s') x = 0 ∧
    deriv (fun t' => deriv (fun t => u c p q r x t z) t') y = 0 ∧
    deriv (fun w' => deriv (fun w => u c p q r x y w) w') z = 0 := by
  have hx : (fun s' => deriv (fun s => u c p q r s y z) s') = fun _ => p :=
    funext fun s' => (hasDerivAt_u_x c p q r s' y z).deriv
  have hy : (fun t' => deriv (fun t => u c p q r x t z) t') = fun _ => q :=
    funext fun t' => (hasDerivAt_u_y c p q r x t' z).deriv
  have hz : (fun w' => deriv (fun w => u c p q r x y w) w') = fun _ => r :=
    funext fun w' => (hasDerivAt_u_z c p q r x y w').deriv
  refine ⟨?_, ?_, ?_⟩
  · first
      | (rw [hx]; exact (hasDerivAt_const x p).deriv)
      | simp [hx]
  · first
      | (rw [hy]; exact (hasDerivAt_const y q).deriv)
      | simp [hy]
  · first
      | (rw [hz]; exact (hasDerivAt_const z r).deriv)
      | simp [hz]

/-- `Δu = 0`. -/
theorem laplacian_zero (c p q r x y z : ℝ) :
    deriv (fun s' => deriv (fun s => u c p q r s y z) s') x
      + deriv (fun t' => deriv (fun t => u c p q r x t z) t') y
      + deriv (fun w' => deriv (fun w => u c p q r x y w) w') z = 0 := by
  obtain ⟨h1, h2, h3⟩ := second_partials_zero c p q r x y z
  simp [h1, h2, h3]

/-- Directional derivative of `u` along `n`, at every parameter `s₀`. -/
theorem normal_derivative_at (c p q r x y z n₁ n₂ n₃ s₀ : ℝ) :
    HasDerivAt (fun s => u c p q r (x + s * n₁) (y + s * n₂) (z + s * n₃))
      (p * n₁ + q * n₂ + r * n₃) s₀ := by
  have hf : (fun s => u c p q r (x + s * n₁) (y + s * n₂) (z + s * n₃))
      = fun s => u c p q r x y z + (p * n₁ + q * n₂ + r * n₃) * s := by
    funext s
    simp only [u]
    ring
  rw [hf]
  have h := ((hasDerivAt_id' s₀).const_mul (p * n₁ + q * n₂ + r * n₃)).const_add
    (u c p q r x y z)
  rw [mul_one] at h
  exact h

theorem normal_derivative (c p q r x y z n₁ n₂ n₃ : ℝ) :
    HasDerivAt (fun s => u c p q r (x + s * n₁) (y + s * n₂) (z + s * n₃))
      (p * n₁ + q * n₂ + r * n₃) 0 :=
  normal_derivative_at c p q r x y z n₁ n₂ n₃ 0

/-- Normal derivative of `u` on the face opposite the vertex `v`, outward normal `−v / √3`. -/
noncomputable def flux (p q r v₁ v₂ v₃ : ℝ) : ℝ :=
  p * (-v₁ / √3) + q * (-v₂ / √3) + r * (-v₃ / √3)

theorem face_normal_derivative (c p q r x y z v₁ v₂ v₃ : ℝ) :
    HasDerivAt (fun s => u c p q r (x + s * (-v₁ / √3)) (y + s * (-v₂ / √3))
      (z + s * (-v₃ / √3))) (flux p q r v₁ v₂ v₃) 0 :=
  normal_derivative c p q r x y z (-v₁ / √3) (-v₂ / √3) (-v₃ / √3)

/-- The four face values of the normal derivative. -/
theorem face_flux_values (p q r : ℝ) :
    flux p q r 1 1 1 = -(p + q + r) / √3 ∧
    flux p q r 1 (-1) (-1) = -(p - q - r) / √3 ∧
    flux p q r (-1) 1 (-1) = -(-p + q - r) / √3 ∧
    flux p q r (-1) (-1) 1 = -(-p - q + r) / √3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold flux; ring)

/-- The four face fluxes sum to `0` (the faces have equal area). -/
theorem face_flux_sum_zero (p q r : ℝ) :
    flux p q r 1 1 1 + flux p q r 1 (-1) (-1) + flux p q r (-1) 1 (-1)
      + flux p q r (-1) (-1) 1 = 0 := by
  unfold flux
  ring

end SteklovAudit.Foundations.AffineHarmonic3D
