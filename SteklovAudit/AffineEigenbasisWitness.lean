import Mathlib
import SteklovAudit.AffineCutoffTail

/-!
# G121: an eigenbasis witness packaging `AffineProbeParseval`

`AffineEigenbasisWitness a` bundles spectral data for the four affine probes on the tetrahedron of
edge `a` (eigenvalues `lam` and overlaps `J`) with the two Parseval identities that
`AffineCutoffTail.AffineProbeParseval` takes as hypotheses. `parseval_of_witness` repackages a witness
as that hypothesis, and `cutoff_of_witness` restates the G115 cutoff bound in terms of a witness.

This is an interface, not new mathematics: the two identities are still fields of the structure.
They are not derived from `TetraAffineFlux`, from a Steklov eigenbasis or from any
Dirichlet-to-Neumann operator.

What this file does NOT prove: the existence of the Dirichlet-to-Neumann operator or of an orthonormal
Steklov eigenbasis, Parseval for the probes, the value `16/a²` as a spectral sum, or any of the open
gaps (7.2), (7.29), (7.38)/(7.45), (9.1) or Theorem 1.3 / 11.1. The bound in `cutoff_of_witness` is
conditional on a witness being supplied.
-/

namespace SteklovAudit.AffineEigenbasisWitness

open SteklovAudit.AffineCutoffTail

/-- Spectral data for the four affine probes on the tetrahedron of edge `a`:
eigenvalues `lam` of a (hypothetical) orthonormal Steklov eigenbasis, overlaps
`J i j = ⟨ψ_i, φ_j⟩`, and the two Parseval identities, which are assumed, not proved. -/
structure AffineEigenbasisWitness (ι : Type*) (a : ℝ) where
  lam : ι → ℝ
  J : ι → Fin 4 → ℝ
  /-- Total mass of the four probes. -/
  mass : HasSum (fun p : ι × Fin 4 => J p.1 p.2 ^ 2) 4
  /-- Summed squared defect against the affine values `muVec a`. -/
  defect : HasSum (fun p : ι × Fin 4 => (lam p.1 - muVec a p.2) ^ 2 * J p.1 p.2 ^ 2) (16 / a ^ 2)

variable {ι : Type*}

/-- A witness gives the named hypothesis of G115. -/
theorem parseval_of_witness {a : ℝ} (W : AffineEigenbasisWitness ι a) :
    AffineProbeParseval W.lam W.J a :=
  ⟨W.mass, W.defect⟩

/-- The G115 cutoff bound, stated for a witness (still conditional on the witness). -/
theorem cutoff_of_witness {a : ℝ} (ha : 0 < a) (W : AffineEigenbasisWitness ι a)
    (F : ℝ → ℝ) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hF : ∀ x y, |F x - F y| ≤ Lf * |x - y|) (L : ℝ) (hL : muAff a < L) :
    |(certOf (parseval_of_witness W)).S F - (certOf (parseval_of_witness W)).Sle F L|
      ≤ 16 * Lf / (a ^ 2 * (L - muAff a)) :=
  affine_cutoff_tail (parseval_of_witness W) ha F Lf hLf hF L hL

end SteklovAudit.AffineEigenbasisWitness
