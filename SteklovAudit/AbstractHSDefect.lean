import Mathlib

/-!
# Abstract finite-dimensional Hilbert–Schmidt defect under spectral cutoff

Supporting estimate related to the uniform localized Hilbert–Schmidt bound (7.2).

For a real symmetric projection matrix `P` the map M ↦ P M is a contraction
on the Frobenius norm. Consequently a linear growth bound on the full defect
implies the same linear growth on the spectrally localized defect.

The contraction property is NOT proved here: it enters as the explicit named
hypothesis `ProjFrobeniusContraction P K` (the standard proof uses that `I - P`
is positive semidefinite when `P` is a symmetric idempotent).

This is a toy model of the gluing estimate; it does NOT prove Lemma 7.1 or (7.2)
for any continuum operator, the tetrahedron's Dirichlet-to-Neumann map,
or any of the open analytic gaps (7.2), (7.29), (7.38)/(7.45), (9.1).
-/

namespace SteklovAudit.AbstractHSDefect

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Named hypothesis: left multiplication by `P` does not increase the squared
Frobenius norm of `M`. For a symmetric idempotent `P` this is a standard fact,
not proved in this file. -/
def ProjFrobeniusContraction (P M : Matrix n n ℝ) : Prop :=
  ∑ i, ∑ j, (P * M) i j ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2

/-- Localized HS bound under linear growth of the full defect, given the
Frobenius contraction of `P` on `K` as a named hypothesis. -/
theorem localized_hs_defect_bound
    (K P : Matrix n n ℝ) (C L : ℝ)
    (_hP_proj : P * P = P) (_hP_sym : P.transpose = P)
    (hcontract : ProjFrobeniusContraction P K)
    (h_growth : ∑ i, ∑ j, K i j ^ 2 ≤ C * (1 + L) ^ 2) :
    ∑ i, ∑ j, (P * K) i j ^ 2 ≤ C * (1 + L) ^ 2 :=
  le_trans hcontract h_growth

end SteklovAudit.AbstractHSDefect
