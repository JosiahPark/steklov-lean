import Mathlib
import SteklovAudit.AbstractHSDefect
import SteklovAudit.ReviewCandidates

/-!
# Discharging the named hypothesis of `AbstractHSDefect`

`AbstractHSDefect.localized_hs_defect_bound` assumed the Frobenius contraction of a projection as the
named hypothesis `ProjFrobeniusContraction P K`. `ReviewCandidates.projection_frobenius_contracts`
proves it for every real symmetric idempotent matrix, so the localized bound holds with no extra
hypothesis beyond `P * P = P`, `Pᵀ = P` and the growth bound.

What this file does NOT prove: Lemma 7.1 or (7.2) for any continuum operator, anything about the
tetrahedron's Dirichlet-to-Neumann map, or any of the open gaps (7.2), (7.29), (7.38)/(7.45), (9.1)
or Theorem 1.3 / 11.1. It is still the finite-dimensional toy model.
-/

namespace SteklovAudit.AbstractHSDefectClosed

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The named hypothesis holds for every real symmetric idempotent matrix. -/
theorem projFrobeniusContraction_of_projection (P M : Matrix n n ℝ)
    (hsym : P.transpose = P) (hidem : P * P = P) :
    SteklovAudit.AbstractHSDefect.ProjFrobeniusContraction P M :=
  SteklovAudit.ReviewCandidates.projection_frobenius_contracts P M hsym hidem

/-- `localized_hs_defect_bound` without the named contraction hypothesis. -/
theorem localized_hs_defect_bound_of_projection (K P : Matrix n n ℝ) (C L : ℝ)
    (hP_proj : P * P = P) (hP_sym : P.transpose = P)
    (h_growth : ∑ i, ∑ j, K i j ^ 2 ≤ C * (1 + L) ^ 2) :
    ∑ i, ∑ j, (P * K) i j ^ 2 ≤ C * (1 + L) ^ 2 :=
  SteklovAudit.AbstractHSDefect.localized_hs_defect_bound K P C L hP_proj hP_sym
    (projFrobeniusContraction_of_projection P K hP_sym hP_proj) h_growth

end SteklovAudit.AbstractHSDefectClosed
