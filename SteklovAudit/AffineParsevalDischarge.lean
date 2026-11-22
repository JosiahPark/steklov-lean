import Mathlib
import SteklovAudit.AffineFullTrace
import SteklovAudit.ResidualLink

/-!
# Affine Parseval discharge: mass `4` and defect `16/a²` from the boundary pairing

`AffineWitnessFromOperator.AffineOperatorData` takes the total probe mass `4` and the total residual
energy `16/a²` as fields, and `AffineFullTrace` takes residual orthogonality as `ResidualOrth`.
Here all three are DERIVED from one named identification hypothesis: the Hilbert-space quantities of
the four probes `u_j` equal the corresponding normalized midpoint pairings of the affine traces
`φ₀ = 1, φⱼ = √3 xⱼ` from `TetraAffineFlux` (mass pairing divided by `12`, residual pairing divided by
`12 (√3 t)²`, mixed pairing divided by `12 √3 t`). Then
* `TetraAffineFlux.boundary_mass` gives each normalized mass `1`, total `4` (`mass_sum`);
* `ResidualLink.residual_defect_constant` gives total residual energy `16/a²` (`energy_sum`);
* `TetraAffineFlux.residual_orthogonal` gives orthogonality (`residualOrth_of_identification`).
So `AffineOperatorData` is built from `AffineOperatorPre` plus the identification (`toData`), and the
G115 cutoff bound and the G126 full-trace bound `8B/a²` follow with no spectral sum assumed.

The remaining named hypotheses are: a symmetric operator with a Hilbert basis of eigenvectors in its
domain, the probes in the domain, and `BoundaryIdentification` (which packages the exactness of the
midpoint rule on each face (see `TriangleQuadrature.lean` for the reference-triangle integrals), the
weak Green identity, and the normal derivatives of affine harmonic functions).

What this file does NOT prove: any of those hypotheses for the tetrahedron's Dirichlet-to-Neumann
operator, the spectral theorem passage, or any of the open gaps (7.2), (7.29), (7.38)/(7.45), (9.1) or
Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.AffineParsevalDischarge

open SteklovAudit.TetraAffineFlux SteklovAudit.ResidualLink SteklovAudit.AffineCutoffTail
  SteklovAudit.AffineWitnessFromOperator SteklovAudit.AffineFullTrace

/-- The four affine traces `φ₀, φ₁, φ₂, φ₃`. -/
noncomputable def probe : Fin 4 → Affine ℝ := ![phi0, phi1, phi2, phi3]

theorem mass_phi0 : boundaryPair (traceValue phi0) (traceValue phi0) = (12 : ℝ) := by
  rw [boundary_mass, slopes_phi0]
  first
    | (show (12 : ℝ) * 1 * 1 + 4 * 0 = 12; norm_num)
    | (simp only [phi0]; norm_num)
    | (simp only [phi0]; grind)
    | norm_num [phi0]
    | grind [phi0]

theorem mass_phi1 : boundaryPair (traceValue phi1) (traceValue phi1) = (12 : ℝ) := by
  rw [boundary_mass, slopes_phi1]
  first
    | (show (12 : ℝ) * 0 * 0 + 4 * 3 = 12; norm_num)
    | (simp only [phi1]; norm_num)
    | (simp only [phi1]; grind)
    | norm_num [phi1]
    | grind [phi1]

theorem mass_phi2 : boundaryPair (traceValue phi2) (traceValue phi2) = (12 : ℝ) := by
  rw [boundary_mass, slopes_phi2]
  first
    | (show (12 : ℝ) * 0 * 0 + 4 * 3 = 12; norm_num)
    | (simp only [phi2]; norm_num)
    | (simp only [phi2]; grind)
    | norm_num [phi2]
    | grind [phi2]

theorem mass_phi3 : boundaryPair (traceValue phi3) (traceValue phi3) = (12 : ℝ) := by
  rw [boundary_mass, slopes_phi3]
  first
    | (show (12 : ℝ) * 0 * 0 + 4 * 3 = 12; norm_num)
    | (simp only [phi3]; norm_num)
    | (simp only [phi3]; grind)
    | norm_num [phi3]
    | grind [phi3]

/-- Operator data without the mass and energy fields (all named hypotheses). -/
structure AffineOperatorPre (H ι : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  D : Submodule ℝ H
  A : D →ₗ[ℝ] H
  symm : ∀ u v : D, inner ℝ (A u) (v : H) = inner ℝ (u : H) (A v)
  b : HilbertBasis ι ℝ H
  mem : ∀ i, b i ∈ D
  lam : ι → ℝ
  eig : ∀ i, A ⟨b i, mem i⟩ = lam i • b i
  u : Fin 4 → D

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Named hypothesis: the Hilbert-space norms and pairings of the probes equal the normalized
midpoint pairings of the affine traces on the tetrahedron of edge `a`. -/
structure BoundaryIdentification (P : AffineOperatorPre H ι) (a : ℝ) : Prop where
  norm_u : ∀ j, ‖(P.u j : H)‖ ^ 2 = boundaryPair (traceValue (probe j)) (traceValue (probe j)) / 12
  norm_r : ∀ j, ‖P.A (P.u j) - muVec a j • (P.u j : H)‖ ^ 2 =
    boundaryPair (fluxResidual (probe j)) (fluxResidual (probe j)) / 12 /
      (Real.sqrt 3 * tPar a) ^ 2
  inner_ur : ∀ j, inner ℝ (P.u j : H) (P.A (P.u j) - muVec a j • (P.u j : H)) =
    boundaryPair (fluxResidual (probe j)) (traceValue (probe j)) / 12 / (Real.sqrt 3 * tPar a)

variable {P : AffineOperatorPre H ι} {a : ℝ}

/-- Total probe mass `4`, derived. -/
theorem mass_sum (I : BoundaryIdentification P a) : ∑ j, ‖(P.u j : H)‖ ^ 2 = 4 := by
  rw [Fin.sum_univ_four, I.norm_u 0, I.norm_u 1, I.norm_u 2, I.norm_u 3]
  rw [show probe 0 = phi0 from rfl, show probe 1 = phi1 from rfl, show probe 2 = phi2 from rfl,
    show probe 3 = phi3 from rfl, mass_phi0, mass_phi1, mass_phi2, mass_phi3]
  norm_num

/-- Total residual energy `16/a²`, derived. -/
theorem energy_sum (ha : 0 < a) (I : BoundaryIdentification P a) :
    ∑ j, ‖P.A (P.u j) - muVec a j • (P.u j : H)‖ ^ 2 = 16 / a ^ 2 := by
  rw [Fin.sum_univ_four, I.norm_r 0, I.norm_r 1, I.norm_r 2, I.norm_r 3]
  rw [show probe 0 = phi0 from rfl, show probe 1 = phi1 from rfl, show probe 2 = phi2 from rfl,
    show probe 3 = phi3 from rfl]
  exact residual_defect_constant a ha

/-- The full operator data, with mass and energy derived from the identification. -/
noncomputable def toData (ha : 0 < a) (P : AffineOperatorPre H ι)
    (I : BoundaryIdentification P a) : AffineOperatorData H ι a where
  D := P.D
  A := P.A
  symm := P.symm
  b := P.b
  mem := P.mem
  lam := P.lam
  eig := P.eig
  u := P.u
  mass := mass_sum I
  energy := energy_sum ha I

/-- Residual orthogonality, derived from `TetraAffineFlux.residual_orthogonal`. -/
theorem residualOrth_of_identification (ha : 0 < a) (I : BoundaryIdentification P a) :
    ResidualOrth (toData ha P I) := by
  intro j
  show inner ℝ (P.u j : H) (P.A (P.u j) - muVec a j • (P.u j : H)) = 0
  have h0 : boundaryPair (fluxResidual (probe j)) (traceValue (probe j)) = (0 : ℝ) :=
    residual_orthogonal _ _
  rw [I.inner_ur j, h0]
  simp

/-- Parseval for the four probes (the hypothesis of G115), with no spectral sum assumed. -/
theorem parseval_discharged (ha : 0 < a) (I : BoundaryIdentification P a) :
    AffineProbeParseval (witnessOfOperator (toData ha P I)).lam
      (witnessOfOperator (toData ha P I)).J a :=
  parseval_of_operator (toData ha P I)

/-- The whole centered trace bound `8B/a²` from the operator, the identification and `C¹,¹`
regularity of `F`. -/
theorem full_trace_discharged (ha : 0 < a) (I : BoundaryIdentification P a)
    (F F' : ℝ → ℝ) (B : ℝ) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hL : ∀ x y, |F' x - F' y| ≤ B * |x - y|) :
    |∑' p : ι × Fin 4, (F (P.lam p.1) - F (muVec a p.2)) * ovl (toData ha P I) p.1 p.2 ^ 2|
      ≤ 8 * B / a ^ 2 :=
  (affine_full_trace_le (toData ha P I) (residualOrth_of_identification ha I) F F' B hd hL).2

end SteklovAudit.AffineParsevalDischarge
