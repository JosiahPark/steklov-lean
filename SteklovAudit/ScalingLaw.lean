import Mathlib
import SteklovAudit.MainConditional

/-!
# D4: the side-length dependence of (11.4) is consistent with scaling

Roadmap item D4 (consistency check on the constants of (11.4)). Steklov eigenvalues scale like
inverse length: `σ_k(T_a) = σ_k(T_1) / a`, so the counting functions satisfy `N_a(L) = N_1(aL)`.
Proved here, taking that relation as the definition of `N_a`:

* `weyl_scale`: `realWeylPolynomial (areaCoeff 1) (6c) (aL) = realWeylPolynomial (areaCoeff a) (6ac) L`;
* `law_scaling`: if `N_1` obeys the two-term law with the paper's constants at `a = 1`, then
  `L ↦ N_1(aL)` obeys it with the paper's constants at side `a > 0`. So the factors `a²` in the area
  term and `a` in the edge term of (11.4) are exactly the ones scaling forces, and Theorem 11.1 for
  one side length gives it for all side lengths;
* `law_scaling_iff`: the converse direction as well, so the two statements are equivalent.

What this file does NOT prove: the eigenvalue scaling `σ_k(T_a) = σ_k(T_1)/a` (no
Dirichlet-to-Neumann operator is defined here); any hypothesis `[H1]`–`[H6]`; the main theorem
(Theorem 1.3 / 11.1). The hypothesis count in STATUS.md is not changed.
-/

namespace SteklovAudit.ScalingLaw

open SteklovAudit SteklovAudit.MainConditional

/-- The Weyl polynomial with the paper's constants transforms correctly under `L ↦ aL`. -/
theorem weyl_scale (a c L : ℝ) :
    realWeylPolynomial (areaCoeff 1) (6 * 1 * c) (a * L) =
      realWeylPolynomial (areaCoeff a) (6 * a * c) L := by
  unfold realWeylPolynomial areaCoeff
  ring

/-- Rescaling a sharp law: `HasSharpRealLaw N A B` for `N` at `aL` gives a law in `L`. -/
theorem law_rescale (N : ℝ → ℝ) (A B A' B' a : ℝ) (ha : 0 < a)
    (hpoly : ∀ L, realWeylPolynomial A B (a * L) = realWeylPolynomial A' B' L)
    (h : HasSharpRealLaw N A B) :
    HasSharpRealLaw (fun L => N (a * L)) A' B' := by
  intro δ hδ
  obtain ⟨L₀, hL₀, hL⟩ := h (δ / a) (div_pos hδ ha)
  refine ⟨L₀ / a, div_nonneg hL₀ ha.le, fun L hLL => ?_⟩
  have haL : L₀ ≤ a * L := by
    have h1 := (div_le_iff₀ ha).mp hLL
    linarith
  have e := hL (a * L) haL
  rw [hpoly L] at e
  have hcalc : δ / a * (a * L) = δ * L := by
    have ha0 : a ≠ 0 := ha.ne'
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_mul_eq_mul_div, mul_comm a L, ← mul_assoc, mul_div_assoc, div_self ha0, mul_one])
  show |N (a * L) - realWeylPolynomial A' B' L| ≤ δ * L
  rw [← hcalc]
  exact e

/-- D4. Theorem 11.1 at side `1` implies it at side `a > 0` with the paper's constants. -/
theorem law_scaling (N : ℝ → ℝ) (a c : ℝ) (ha : 0 < a)
    (h : HasSharpRealLaw N (areaCoeff 1) (6 * 1 * c)) :
    HasSharpRealLaw (fun L => N (a * L)) (areaCoeff a) (6 * a * c) :=
  law_rescale N _ _ _ _ a ha (weyl_scale a c) h

/-- D4, converse: the law at side `a > 0` for `L ↦ N(aL)` gives the law at side `1` for `N`. -/
theorem law_unscaling (N : ℝ → ℝ) (a c : ℝ) (ha : 0 < a)
    (h : HasSharpRealLaw (fun L => N (a * L)) (areaCoeff a) (6 * a * c)) :
    HasSharpRealLaw N (areaCoeff 1) (6 * 1 * c) := by
  have hinv : 0 < a⁻¹ := inv_pos.mpr ha
  have hpoly : ∀ L, realWeylPolynomial (areaCoeff a) (6 * a * c) (a⁻¹ * L) =
      realWeylPolynomial (areaCoeff 1) (6 * 1 * c) L := by
    intro L
    have := weyl_scale a c (a⁻¹ * L)
    rw [← this, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have h2 := law_rescale (fun L => N (a * L)) _ _ _ _ a⁻¹ hinv hpoly h
  have h3 : HasSharpRealLaw (fun L => N (a * (a⁻¹ * L))) (areaCoeff 1) (6 * 1 * c) := h2
  have e : (fun L => N (a * (a⁻¹ * L))) = N := by
    funext L
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  rw [e] at h3
  exact h3

/-- D4. The two statements are equivalent. -/
theorem law_scaling_iff (N : ℝ → ℝ) (a c : ℝ) (ha : 0 < a) :
    HasSharpRealLaw N (areaCoeff 1) (6 * 1 * c) ↔
      HasSharpRealLaw (fun L => N (a * L)) (areaCoeff a) (6 * a * c) :=
  ⟨law_scaling N a c ha, law_unscaling N a c ha⟩

end SteklovAudit.ScalingLaw
