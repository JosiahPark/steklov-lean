import Mathlib
import SteklovAudit.PartitionKeptLengthTotal

/-!
# Edge area of the tetrahedral partition (roadmap item K8)

Third step of the explicit partition of `∂T_a` (Josiah's construction, 2026-11-26), toward ledger
input H2 (area additivity) of `MainConditional.lean`. On each of the two faces incident to an edge,
in edge coordinates `(z, r)` (`0 ≤ z ≤ a` along the edge, `r ≥ 0` the distance into the face), the
edge cutoff is the product `χ_e(z, r) = q_ε(z) · θ_γ(r)` with `q_ε = edgeCut` (K7a) and the
transverse cutoff `θ_γ(r) = cos(β(r/γ))` (`transCut`), for a continuous profile `β` (K6).

* `transCut_zero_of_le`: `θ_γ(r) = 0` for `r ≥ 2γ`;
* `transverse_width`: `∫₀^{2γ} θ_γ² = 3γ/2` (substitution `r = γ t` and `∫₀² cos² β = 3/2`);
  `transverse_width_of_le`: the same over `[0, R]` for every `R ≥ 2γ`;
* `edge_strip_mass`: `∫₀ᵃ ∫₀^{2γ} χ_e² dr dz = (a − 3ε) · 3γ/2` (iterated interval integrals,
  using K7b's `edge_kept_length`);
* `edge_area_coeff`, `edge_area_integral`: six edges, two faces each, divided by `4π`:
  `A_edge = 6 · 2 · (a − 3ε)(3γ/2)/(4π) = 18γ(a − 3ε)/(4π)`.

What this file does NOT prove: that these edge coordinates parametrize the faces of the actual
regular tetrahedron isometrically on the strips (the identification of item K4/K12), the pointwise
partition identity (K11), area additivity `AV + AE + AF = |∂T_a|/(4π)` (K10), the ledger input H2
itself, anything about the Dirichlet-to-Neumann operator, H4–H6, or Theorem 1.3 / 11.1. It is real
analysis of explicit functions of two variables on a rectangle.
-/

namespace SteklovAudit.PartitionEdgeArea

open Real SteklovAudit.PartitionProfile SteklovAudit.PartitionKeptLength
  SteklovAudit.PartitionKeptLengthTotal

/-- **K8.** The transverse cutoff `θ_γ(r) = cos(β(r/γ))`. -/
noncomputable def transCut (β : ℝ → ℝ) (γ r : ℝ) : ℝ := cos (β (r / γ))

/-- **K8.** The transverse cutoff vanishes from `2γ` on. -/
theorem transCut_zero_of_le (β : ℝ → ℝ) (h : IsProfile β) {γ r : ℝ} (hγ : 0 < γ)
    (hr : 2 * γ ≤ r) : transCut β γ r = 0 := by
  unfold transCut
  rw [h.2.1 _ (two_le_div hγ hr), cos_pi_div_two]

/-- **K8.** `θ_γ²` is continuous for a continuous profile. -/
theorem transCut_continuous (β : ℝ → ℝ) (hβ : Continuous β) (γ : ℝ) :
    Continuous (fun r => transCut β γ r ^ 2) := by
  show Continuous (fun r => cos (β (r / γ)) ^ 2)
  first
    | exact (continuous_cos.comp (hβ.comp (continuous_id.div_const γ))).pow 2
    | fun_prop

/-- **K8.** Transverse width: `∫₀^{2γ} cos(β(r/γ))² dr = 3γ/2`. -/
theorem transverse_width (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {γ : ℝ}
    (hγ : 0 < γ) : ∫ r in (0 : ℝ)..(2 * γ), transCut β γ r ^ 2 = 3 * γ / 2 := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hc : (∫ r in (0 : ℝ)..(2 * γ), cos (β (r / γ)) ^ 2) =
      γ • ∫ t in (0 : ℝ) / γ..(2 * γ) / γ, cos (β t) ^ 2 :=
    intervalIntegral.integral_comp_div (fun t => cos (β t) ^ 2) hγ0
  have e2 : 2 * γ / γ = 2 := by rw [mul_div_assoc, div_self hγ0, mul_one]
  rw [zero_div, e2, integral_cos_sq β hβ h, smul_eq_mul] at hc
  show (∫ r in (0 : ℝ)..(2 * γ), cos (β (r / γ)) ^ 2) = 3 * γ / 2
  rw [hc]
  ring

/-- **K8.** The transverse width over any `[0, R]` with `R ≥ 2γ` (the cutoff is zero beyond `2γ`). -/
theorem transverse_width_of_le (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {γ R : ℝ}
    (hγ : 0 < γ) (hR : 2 * γ ≤ R) : ∫ r in (0 : ℝ)..R, transCut β γ r ^ 2 = 3 * γ / 2 := by
  have hc := transCut_continuous β hβ γ
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (2 * γ))
    (hc.intervalIntegrable (2 * γ) R)
  have h2 : ∫ r in (2 * γ)..R, transCut β γ r ^ 2 = 0 := by
    have e : ∫ r in (2 * γ)..R, transCut β γ r ^ 2 = ∫ r in (2 * γ)..R, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le hR] at hr
      show transCut β γ r ^ 2 = 0
      simp [transCut_zero_of_le β h hγ hr.1]
    rw [e]
    simp
  rw [← h1, h2, transverse_width β hβ h hγ, add_zero]

/-- **K8.** Mass of the product cutoff on one edge strip of one face:
`∫₀ᵃ ∫₀^{2γ} (q_ε(z) θ_γ(r))² dr dz = (a − 3ε) · 3γ/2`. -/
theorem edge_strip_mass (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a γ : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) (hγ : 0 < γ) :
    ∫ z in (0 : ℝ)..a, ∫ r in (0 : ℝ)..(2 * γ), (edgeCut β ε a z * transCut β γ r) ^ 2 =
      (a - 3 * ε) * (3 * γ / 2) := by
  have inner : ∀ z : ℝ, ∫ r in (0 : ℝ)..(2 * γ), (edgeCut β ε a z * transCut β γ r) ^ 2 =
      edgeCut β ε a z ^ 2 * (3 * γ / 2) := by
    intro z
    simp only [mul_pow]
    rw [intervalIntegral.integral_const_mul, transverse_width β hβ h hγ]
  have e : ∫ z in (0 : ℝ)..a, ∫ r in (0 : ℝ)..(2 * γ), (edgeCut β ε a z * transCut β γ r) ^ 2 =
      ∫ z in (0 : ℝ)..a, edgeCut β ε a z ^ 2 * (3 * γ / 2) := by
    apply intervalIntegral.integral_congr
    intro z _
    exact inner z
  rw [e, intervalIntegral.integral_mul_const, edge_kept_length β hβ h hε ha]

/-- **K8.** Six edges, two incident faces each, normalized by `4π`. -/
theorem edge_area_coeff (a ε γ : ℝ) :
    6 * (2 * ((a - 3 * ε) * (3 * γ / 2))) / (4 * π) = 18 * γ * (a - 3 * ε) / (4 * π) := by
  ring

/-- **K8.** The edge area coefficient of the explicit partition: `18γ(a − 3ε)/(4π)`. -/
theorem edge_area_integral (β : ℝ → ℝ) (hβ : Continuous β) (h : IsProfile β) {ε a γ : ℝ}
    (hε : 0 < ε) (ha : 4 * ε ≤ a) (hγ : 0 < γ) :
    6 * (2 * ∫ z in (0 : ℝ)..a, ∫ r in (0 : ℝ)..(2 * γ),
        (edgeCut β ε a z * transCut β γ r) ^ 2) / (4 * π) =
      18 * γ * (a - 3 * ε) / (4 * π) := by
  rw [edge_strip_mass β hβ h hε ha hγ]
  exact edge_area_coeff a ε γ

end SteklovAudit.PartitionEdgeArea
