import Mathlib

/-!
# Exact integrals on the reference triangle (roadmap item G127)

On the reference triangle `{(s, t) : 0 ≤ s, 0 ≤ t, s + t ≤ 1}`, written as the iterated integral
`∫₀¹ ∫₀^{1−s} f(s, t) dt ds`, the integrals of `1, s, s², s t` are `1/2, 1/6, 1/12, 1/24`
(`tri_int_one`, `tri_int_s`, `tri_int_ss`, `tri_int_st`), computed independently of any quadrature.
The edge-midpoint rule `(1/6) (f(½,0) + f(0,½) + f(½,½))` gives the same four values
(`midpoint_rule_exact_deg2`); by symmetry in `s ↔ t` this covers all monomials of degree ≤ 2.
This is the exactness that `TetraAffineFlux.lean` uses implicitly when it calls its midpoint sums
boundary integrals.

What this file does NOT prove: the surface measure on the faces of the tetrahedron, the change of
variables from a face to the reference triangle, the identification of `TetraAffineFlux.boundaryPair`
with an actual boundary integral, the weak Green identity, or anything about the Dirichlet-to-Neumann
operator, (7.29) or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.TriangleQuadrature

theorem tri_int_one : ∫ s in (0 : ℝ)..1, ∫ _t in (0 : ℝ)..(1 - s), (1 : ℝ) = 1 / 2 := by
  have hin : ∀ s : ℝ, ∫ _t in (0 : ℝ)..(1 - s), (1 : ℝ) = 1 - s := by
    intro s
    simp
  simp only [hin]
  rw [intervalIntegral.integral_sub]
  all_goals first
    | (apply Continuous.intervalIntegrable; fun_prop)
    | (simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]; norm_num)

theorem tri_int_s : ∫ s in (0 : ℝ)..1, ∫ _t in (0 : ℝ)..(1 - s), s = 1 / 6 := by
  have hin : ∀ s : ℝ, ∫ _t in (0 : ℝ)..(1 - s), s = s - s ^ 2 := by
    intro s
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  simp only [hin]
  rw [intervalIntegral.integral_sub]
  all_goals first
    | (apply Continuous.intervalIntegrable; fun_prop)
    | (simp only [integral_id, integral_pow]; norm_num)

theorem tri_int_ss : ∫ s in (0 : ℝ)..1, ∫ _t in (0 : ℝ)..(1 - s), s ^ 2 = 1 / 12 := by
  have hin : ∀ s : ℝ, ∫ _t in (0 : ℝ)..(1 - s), s ^ 2 = s ^ 2 - s ^ 3 := by
    intro s
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  simp only [hin]
  rw [intervalIntegral.integral_sub]
  all_goals first
    | (apply Continuous.intervalIntegrable; fun_prop)
    | (simp only [integral_pow]; norm_num)

theorem tri_int_st : ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..(1 - s), s * t = 1 / 24 := by
  have hin : ∀ s : ℝ,
      ∫ t in (0 : ℝ)..(1 - s), s * t = 1 / 2 * s ^ 3 - s ^ 2 + 1 / 2 * s ^ 1 := by
    intro s
    rw [show (∫ t in (0 : ℝ)..(1 - s), s * t) = s * ∫ t in (0 : ℝ)..(1 - s), t from
      intervalIntegral.integral_const_mul s (fun t => t), integral_id]
    ring
  simp only [hin]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub]
  all_goals first
    | (apply Continuous.intervalIntegrable; fun_prop)
    | (simp only [intervalIntegral.integral_const_mul, integral_pow, integral_id]; norm_num)

/-- The edge-midpoint rule on the reference triangle (weight `1/6` per edge midpoint). -/
noncomputable def edgeMidRule (f : ℝ → ℝ → ℝ) : ℝ :=
  1 / 6 * (f (1 / 2) 0 + f 0 (1 / 2) + f (1 / 2) (1 / 2))

/-- **G127.** The edge-midpoint rule reproduces the four exact integrals above. -/
theorem midpoint_rule_exact_deg2 :
    edgeMidRule (fun _ _ => 1) = 1 / 2 ∧ edgeMidRule (fun s _ => s) = 1 / 6 ∧
      edgeMidRule (fun s _ => s ^ 2) = 1 / 12 ∧ edgeMidRule (fun s t => s * t) = 1 / 24 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold edgeMidRule; norm_num)

/-- Exactness in integral form: the rule equals the iterated integral for `1, s, s², s t`. -/
theorem midpoint_eq_integral :
    edgeMidRule (fun _ _ => 1) = ∫ s in (0 : ℝ)..1, ∫ _t in (0 : ℝ)..(1 - s), (1 : ℝ) ∧
      edgeMidRule (fun s _ => s) = ∫ s in (0 : ℝ)..1, ∫ _t in (0 : ℝ)..(1 - s), s ∧
      edgeMidRule (fun s _ => s ^ 2) = ∫ s in (0 : ℝ)..1, ∫ _t in (0 : ℝ)..(1 - s), s ^ 2 ∧
      edgeMidRule (fun s t => s * t) = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..(1 - s), s * t := by
  obtain ⟨h1, h2, h3, h4⟩ := midpoint_rule_exact_deg2
  rw [tri_int_one, tri_int_s, tri_int_ss, tri_int_st]
  exact ⟨h1, h2, h3, h4⟩

end SteklovAudit.TriangleQuadrature
