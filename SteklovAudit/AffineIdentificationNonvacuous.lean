import Mathlib
import SteklovAudit.AffineSpectralPassageFin

/-!
# G144: `BoundaryIdentification` is satisfiable (definition check)

`AffineParsevalDischarge.BoundaryIdentification` is the one named hypothesis left behind the G126 /
G143 full-trace bound `8 B / a²` in finite dimension. This file shows it is not contradictory: an
explicit symmetric operator on a three-dimensional space, with explicit probes, satisfies it for
every `a`.

Model. Let `e 0, e 1, e 2` be orthonormal, `μ = muAff a` and
`r = √(24 / 12 / (√3 · tPar a)²)`. The operator `blockT e μ r` has matrix
`[[0,0,0],[0,μ,r],[0,r,0]]` in the basis `e`, and the probes are `e 0, e 1, e 1, e 1`. Then
`T (e 0) = 0` (residual `0`, as `phi0` has residual energy `0`), and `T (e 1) − μ e 1 = r e 2`, which
is orthogonal to `e 1` with squared norm `r² = 24 / 12 / (√3 · tPar a)²` (the normalized residual
energy of `phi1, phi2, phi3`). This replaces the roadmap's block model on `Fin 4 × Fin 2`
by a smaller one; it checks the same three fields.

Observation for the F table: `BoundaryIdentification` constrains each probe separately (its mass,
its residual energy, its own mixed pairing) and contains NO cross-probe condition, so the probes
`u 1, u 2, u 3` may even coincide. Any use that needs the probes orthogonal must assume it
separately.

What this file does NOT prove: `BoundaryIdentification` for the tetrahedron's Dirichlet-to-Neumann
operator (the model here is a toy 3×3 matrix with no relation to the DtN map), the
infinite-dimensional spectral theorem, or any of H1–H6, (7.2), (7.29), (7.38)/(7.45), (9.1) or
Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.AffineIdentificationNonvacuous

open SteklovAudit.TetraAffineFlux SteklovAudit.ResidualLink SteklovAudit.AffineCutoffTail
  SteklovAudit.AffineParsevalDischarge SteklovAudit.AffineSpectralPassageFin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The model operator `x ↦ (μ⟪e₁,x⟫ + r⟪e₂,x⟫) e₁ + r⟪e₁,x⟫ e₂`. -/
noncomputable def blockT (e : Fin 3 → E) (μ r : ℝ) : E →ₗ[ℝ] E where
  toFun x := (μ * inner ℝ (e 1) x + r * inner ℝ (e 2) x) • e 1 + (r * inner ℝ (e 1) x) • e 2
  map_add' x y := by
    simp only [inner_add_right]
    first
      | module
      | (simp only [mul_add, add_smul]; abel)
  map_smul' c x := by
    simp only [inner_smul_right, RingHom.id_apply]
    first
      | module
      | (rw [smul_add, smul_smul, smul_smul]; congr 1 <;> congr 1 <;> ring)

theorem blockT_apply (e : Fin 3 → E) (μ r : ℝ) (x : E) :
    blockT e μ r x =
      (μ * inner ℝ (e 1) x + r * inner ℝ (e 2) x) • e 1 + (r * inner ℝ (e 1) x) • e 2 := rfl

/-- The model operator is symmetric, for any vectors `e` and reals `μ r`. -/
theorem blockT_symm (e : Fin 3 → E) (μ r : ℝ) : (blockT e μ r).IsSymmetric := by
  intro x y
  simp only [blockT_apply, inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
  first
    | (rw [real_inner_comm (e 1) x, real_inner_comm (e 2) x]; ring)
    | (rw [real_inner_comm x (e 1), real_inner_comm x (e 2)]; ring)
    | (simp only [real_inner_comm]; ring)

/-- The probes `e 0, e 1, e 1, e 1`. -/
noncomputable def probesOf (e : Fin 3 → E) : Fin 4 → E := ![e 0, e 1, e 1, e 1]

/-- The residual size `r = √(24 / 12 / (√3 · tPar a)²)`. -/
noncomputable def rRes (a : ℝ) : ℝ := Real.sqrt (24 / 12 / (Real.sqrt 3 * tPar a) ^ 2)

theorem rRes_sq (a : ℝ) : rRes a ^ 2 = 24 / 12 / (Real.sqrt 3 * tPar a) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem fin4_cases (j : Fin 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  first
    | (revert j; decide)
    | (fin_cases j <;> simp)
    | omega

variable {e : Fin 3 → E}

theorem e_inner_self (ho : Orthonormal ℝ e) (i : Fin 3) : inner ℝ (e i) (e i) = (1 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, ho.1 i]
  norm_num

theorem blockT_e0 (ho : Orthonormal ℝ e) (μ r : ℝ) : blockT e μ r (e 0) = 0 := by
  have h10 : inner ℝ (e 1) (e 0) = (0 : ℝ) := ho.2 (by decide)
  have h20 : inner ℝ (e 2) (e 0) = (0 : ℝ) := ho.2 (by decide)
  rw [blockT_apply, h10, h20]
  simp

/-- The residual of the probe `e 1`: `T (e 1) − μ e 1 = r e 2`. -/
theorem block_residual (ho : Orthonormal ℝ e) (μ r : ℝ) :
    blockT e μ r (e 1) - μ • e 1 = r • e 2 := by
  have h11 := e_inner_self ho 1
  have h21 : inner ℝ (e 2) (e 1) = (0 : ℝ) := ho.2 (by decide)
  rw [blockT_apply, h11, h21]
  simp only [mul_one, mul_zero, add_zero]
  abel

theorem block_residual_norm (ho : Orthonormal ℝ e) (μ r : ℝ) :
    ‖blockT e μ r (e 1) - μ • e 1‖ ^ 2 = r ^ 2 := by
  rw [block_residual ho, norm_smul, ho.1 2, mul_one, Real.norm_eq_abs, sq_abs]

theorem block_residual_inner (ho : Orthonormal ℝ e) (μ r : ℝ) :
    inner ℝ (e 1) (blockT e μ r (e 1) - μ • e 1) = (0 : ℝ) := by
  have h12 : inner ℝ (e 1) (e 2) = (0 : ℝ) := ho.2 (by decide)
  rw [block_residual ho, inner_smul_right, h12, mul_zero]

/-- The model satisfies `BoundaryIdentification` for every `a`. -/
theorem identification_of_block [FiniteDimensional ℝ E] {n : ℕ} (ho : Orthonormal ℝ e)
    (hn : Module.finrank ℝ E = n) (a : ℝ) :
    BoundaryIdentification
      (preOfSymmetric (blockT_symm e (muAff a) (rRes a)) hn (probesOf e)) a := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    show ‖probesOf e j‖ ^ 2 = boundaryPair (traceValue (probe j)) (traceValue (probe j)) / 12
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · rw [show probesOf e 0 = e 0 from rfl, show probe 0 = phi0 from rfl, mass_phi0, ho.1 0]
      norm_num
    · rw [show probesOf e 1 = e 1 from rfl, show probe 1 = phi1 from rfl, mass_phi1, ho.1 1]
      norm_num
    · rw [show probesOf e 2 = e 1 from rfl, show probe 2 = phi2 from rfl, mass_phi2, ho.1 1]
      norm_num
    · rw [show probesOf e 3 = e 1 from rfl, show probe 3 = phi3 from rfl, mass_phi3, ho.1 1]
      norm_num
  · intro j
    show ‖blockT e (muAff a) (rRes a) (probesOf e j) - muVec a j • probesOf e j‖ ^ 2 =
      boundaryPair (fluxResidual (probe j)) (fluxResidual (probe j)) / 12 /
        (Real.sqrt 3 * tPar a) ^ 2
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · rw [show probesOf e 0 = e 0 from rfl, show probe 0 = phi0 from rfl,
        show muVec a 0 = 0 from rfl, residual_energy_phi0, blockT_e0 ho]
      simp
    · rw [show probesOf e 1 = e 1 from rfl, show probe 1 = phi1 from rfl,
        show muVec a 1 = muAff a from rfl, residual_energy_phi1, block_residual_norm ho, rRes_sq]
    · rw [show probesOf e 2 = e 1 from rfl, show probe 2 = phi2 from rfl,
        show muVec a 2 = muAff a from rfl, residual_energy_phi2, block_residual_norm ho, rRes_sq]
    · rw [show probesOf e 3 = e 1 from rfl, show probe 3 = phi3 from rfl,
        show muVec a 3 = muAff a from rfl, residual_energy_phi3, block_residual_norm ho, rRes_sq]
  · intro j
    show inner ℝ (probesOf e j)
        (blockT e (muAff a) (rRes a) (probesOf e j) - muVec a j • probesOf e j) =
      boundaryPair (fluxResidual (probe j)) (traceValue (probe j)) / 12 / (Real.sqrt 3 * tPar a)
    have h0 : boundaryPair (fluxResidual (probe j)) (traceValue (probe j)) = (0 : ℝ) :=
      residual_orthogonal _ _
    rw [h0, zero_div, zero_div]
    rcases fin4_cases j with rfl | rfl | rfl | rfl
    · rw [show probesOf e 0 = e 0 from rfl, show muVec a 0 = 0 from rfl, blockT_e0 ho]
      simp
    · rw [show probesOf e 1 = e 1 from rfl, show muVec a 1 = muAff a from rfl]
      exact block_residual_inner ho _ _
    · rw [show probesOf e 2 = e 1 from rfl, show muVec a 2 = muAff a from rfl]
      exact block_residual_inner ho _ _
    · rw [show probesOf e 3 = e 1 from rfl, show muVec a 3 = muAff a from rfl]
      exact block_residual_inner ho _ _

/-- `BoundaryIdentification` is satisfiable on `EuclideanSpace ℝ (Fin 3)`, for every `a`. -/
theorem exists_identification (a : ℝ) :
    ∃ (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) (hT : T.IsSymmetric)
      (u : Fin 4 → EuclideanSpace ℝ (Fin 3)),
      BoundaryIdentification (preOfSymmetric hT finrank_euclideanSpace_fin u) a :=
  ⟨_, _, _, identification_of_block (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal
    finrank_euclideanSpace_fin a⟩

end SteklovAudit.AffineIdentificationNonvacuous
