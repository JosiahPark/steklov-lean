import Mathlib
import SteklovAudit.TetraAffineFlux
import SteklovAudit.AffineCutoffTail

/-!
# Residual-to-constant link for the affine probes

Instantiates `TetraAffineFlux.residual_energy` (the midpoint pairing, twelve times the normalized
boundary integral, with the flux scaled by `√3 t`) at the four normalized probes `φ₀ = 1`,
`φⱼ = √3 xⱼ`, and converts the result into the constant `16/a²` of `AffineProbeParseval.defect`:
the raw residual energies are `0, 24, 24, 24`; dividing by `12` and by `(√3 t)²` gives `0` and
`2/(3t²)`; their sum is `16/a²` (via `AffineCutoffTail.affine_residual_sum`).

Adapted from a reviewed attachment whose original lemmas only restated `affine_two_over_t_sq` and did
not invoke `residual_energy`.

What this file does NOT prove: that the midpoint pairing equals the boundary integral, that
`fluxResidual` is the residual `R = AJ − JB` of the actual Dirichlet-to-Neumann operator, Parseval for
the probes (the `defect` field of `AffineProbeParseval`), or any of the open gaps (7.2), (7.29),
(7.38)/(7.45), (9.1) or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.ResidualLink

open SteklovAudit.TetraAffineFlux SteklovAudit.AffineCutoffTail

/-- `φ₀ = 1`. -/
noncomputable def phi0 : Affine ℝ := ⟨1, 0, 0, 0⟩
/-- `φ₁ = √3 x`. -/
noncomputable def phi1 : Affine ℝ := ⟨0, Real.sqrt 3, 0, 0⟩
/-- `φ₂ = √3 y`. -/
noncomputable def phi2 : Affine ℝ := ⟨0, 0, Real.sqrt 3, 0⟩
/-- `φ₃ = √3 z`. -/
noncomputable def phi3 : Affine ℝ := ⟨0, 0, 0, Real.sqrt 3⟩

theorem slopes_phi0 : slopes phi0 phi0 = 0 := by
  show (0 : ℝ) * 0 + 0 * 0 + 0 * 0 = 0
  norm_num

theorem slopes_phi1 : slopes phi1 phi1 = 3 := by
  show Real.sqrt 3 * Real.sqrt 3 + 0 * 0 + 0 * 0 = 3
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem slopes_phi2 : slopes phi2 phi2 = 3 := by
  show 0 * 0 + Real.sqrt 3 * Real.sqrt 3 + 0 * 0 = 3
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem slopes_phi3 : slopes phi3 phi3 = 3 := by
  show 0 * 0 + 0 * 0 + Real.sqrt 3 * Real.sqrt 3 = 3
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The constant probe has zero residual energy. -/
theorem residual_energy_phi0 : boundaryPair (fluxResidual phi0) (fluxResidual phi0) = 0 := by
  rw [residual_energy, slopes_phi0]
  first
    | (show (8 : ℝ) * 0 = 0; norm_num)
    | norm_num
    | grind

theorem residual_energy_phi1 : boundaryPair (fluxResidual phi1) (fluxResidual phi1) = 24 := by
  rw [residual_energy, slopes_phi1]
  first
    | (show (8 : ℝ) * 3 = 24; norm_num)
    | norm_num
    | grind

theorem residual_energy_phi2 : boundaryPair (fluxResidual phi2) (fluxResidual phi2) = 24 := by
  rw [residual_energy, slopes_phi2]
  first
    | (show (8 : ℝ) * 3 = 24; norm_num)
    | norm_num
    | grind

theorem residual_energy_phi3 : boundaryPair (fluxResidual phi3) (fluxResidual phi3) = 24 := by
  rw [residual_energy, slopes_phi3]
  first
    | (show (8 : ℝ) * 3 = 24; norm_num)
    | norm_num
    | grind

/-- Normalization: a raw energy of `24` becomes `2/(3t²)` after dividing by `12` and `(√3 t)²`. -/
theorem normalized_energy (a : ℝ) (E : ℝ) (hE : E = 24) :
    E / 12 / (Real.sqrt 3 * tPar a) ^ 2 = 2 / (3 * tPar a ^ 2) := by
  subst hE
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), show (24 : ℝ) / 12 = 2 by norm_num]

/-- The four normalized residual energies sum to the defect constant `16/a²`. -/
theorem residual_defect_constant (a : ℝ) (ha : 0 < a) :
    boundaryPair (fluxResidual phi0) (fluxResidual phi0) / 12 / (Real.sqrt 3 * tPar a) ^ 2 +
      boundaryPair (fluxResidual phi1) (fluxResidual phi1) / 12 / (Real.sqrt 3 * tPar a) ^ 2 +
      boundaryPair (fluxResidual phi2) (fluxResidual phi2) / 12 / (Real.sqrt 3 * tPar a) ^ 2 +
      boundaryPair (fluxResidual phi3) (fluxResidual phi3) / 12 / (Real.sqrt 3 * tPar a) ^ 2 =
      16 / a ^ 2 := by
  rw [residual_energy_phi0, normalized_energy a _ residual_energy_phi1,
    normalized_energy a _ residual_energy_phi2, normalized_energy a _ residual_energy_phi3]
  have h := affine_residual_sum a ha
  have h0 : (0 : ℝ) / 12 / (Real.sqrt 3 * tPar a) ^ 2 = 0 := by simp
  linarith

end SteklovAudit.ResidualLink
