import Mathlib
import SteklovAudit.AffineEigenbasisWitness
import SteklovAudit.ReviewExtensions

/-!
# The affine witness from operator data (roadmap item G124)

`AffineEigenbasisWitness` (G121) assumed the two Parseval identities for the four affine probes as
fields. Here they are DERIVED: from a symmetric operator `A` on a domain `D` in a real inner-product
space, a Hilbert basis of eigenvectors lying in `D`, and four probes `u j ∈ D` whose total squared norm
is `4` and whose residuals `A u_j − μ_j u_j` have total squared norm `16/a²`, the witness is built with
overlaps `J i j = ⟨b i, u j⟩` via `ReviewExtensions.spectral_sums_of_operator`.

All of `AffineOperatorData` are named hypotheses. What this file does NOT prove: that the tetrahedron's
Dirichlet-to-Neumann operator is such an operator, that it has an eigenbasis in its domain, that the
affine probes lie in the domain, the two norm identities (see `ResidualLink.lean` and
`AffineParsevalDischarge.lean` for their midpoint-pairing form), or any of the open gaps (7.2), (7.29),
(7.38)/(7.45), (9.1) or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.AffineWitnessFromOperator

open SteklovAudit.AffineCutoffTail SteklovAudit.AffineEigenbasisWitness
  SteklovAudit.ReviewExtensions

/-- Operator data for the four affine probes on the tetrahedron of edge `a`. Every field is a named
hypothesis. -/
structure AffineOperatorData (H ι : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a : ℝ) where
  D : Submodule ℝ H
  A : D →ₗ[ℝ] H
  symm : ∀ u v : D, inner ℝ (A u) (v : H) = inner ℝ (u : H) (A v)
  b : HilbertBasis ι ℝ H
  mem : ∀ i, b i ∈ D
  lam : ι → ℝ
  eig : ∀ i, A ⟨b i, mem i⟩ = lam i • b i
  u : Fin 4 → D
  mass : ∑ j, ‖(u j : H)‖ ^ 2 = 4
  energy : ∑ j, ‖A (u j) - muVec a j • (u j : H)‖ ^ 2 = 16 / a ^ 2

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {a : ℝ}

/-- Both Parseval identities, derived from the operator data. -/
theorem sums_of_data (O : AffineOperatorData H ι a) :
    HasSum (fun p : ι × Fin 4 => (inner ℝ (O.b p.1) (O.u p.2 : H)) ^ 2) 4 ∧
      HasSum (fun p : ι × Fin 4 =>
        (O.lam p.1 - muVec a p.2) ^ 2 * (inner ℝ (O.b p.1) (O.u p.2 : H)) ^ 2) (16 / a ^ 2) :=
  spectral_sums_of_operator O.D O.A O.symm O.b O.mem O.lam O.eig O.u (muVec a) 4 (16 / a ^ 2)
    O.mass O.energy

/-- **G124.** The affine eigenbasis witness built from operator data (fields derived, not assumed). -/
noncomputable def witnessOfOperator (O : AffineOperatorData H ι a) : AffineEigenbasisWitness ι a where
  lam := O.lam
  J := fun i j => inner ℝ (O.b i) (O.u j : H)
  mass := (sums_of_data O).1
  defect := (sums_of_data O).2

theorem witnessOfOperator_lam (O : AffineOperatorData H ι a) : (witnessOfOperator O).lam = O.lam :=
  rfl

theorem witnessOfOperator_J (O : AffineOperatorData H ι a) (i : ι) (j : Fin 4) :
    (witnessOfOperator O).J i j = inner ℝ (O.b i) (O.u j : H) :=
  rfl

/-- The named hypothesis `AffineProbeParseval` of G115, now a consequence of operator data. -/
theorem parseval_of_operator (O : AffineOperatorData H ι a) :
    AffineProbeParseval (witnessOfOperator O).lam (witnessOfOperator O).J a :=
  parseval_of_witness (witnessOfOperator O)

/-- **G124.** The G115 cutoff bound from operator data. -/
theorem cutoff_of_operator (ha : 0 < a) (O : AffineOperatorData H ι a)
    (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) (hL : muAff a < L) :
    |(certOf (parseval_of_operator O)).S F - (certOf (parseval_of_operator O)).Sle F L|
      ≤ 16 * Lf / (a ^ 2 * (L - muAff a)) :=
  cutoff_of_witness ha (witnessOfOperator O) F Lf hLf hF L hL

end SteklovAudit.AffineWitnessFromOperator
