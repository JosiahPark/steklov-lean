import Mathlib

/-!
# Basis independence of the Hilbert–Schmidt sum in finite dimension (roadmap item G131)

Restored on 2026-11-23: these five theorems were first verified at `e837800` in
`HSBasisIndependence.lean`, which G138 (`6dd7e28`) rewrote with the complex-matrix version. The proofs
below are unchanged; only this paragraph is new. Same namespace, no name overlaps with G138.

For a linear map `T : E →ₗ[ℝ] F` between finite-dimensional real inner-product spaces, the sum
`∑ i, ‖T (b i)‖²` over an orthonormal basis `b` of `E` does not depend on `b`.

* `parseval_sq`: `∑ i, ⟪b i, x⟫² = ‖x‖²` for an orthonormal basis `b`.
* `hs_sum_eq_double`: the HS sum equals the double sum `∑ i k, ⟪d k, T (b i)⟫²` for any orthonormal
  basis `d` of `F`.
* `hs_sum_eq_adjoint`: it equals `∑ k, ‖T† (d k)‖²`, an expression without `b`.
* `hs_sum_basis_indep`: two orthonormal bases `b`, `c` of `E` give the same sum.
* `hs_sum_id`: for `T = id` the sum is `dim E` (the statement is not vacuous).

F table text: the HS defect row does not depend on the eigenbasis chosen for the model or the true
operator (finite-dimensional spectral coordinates).

What this file does NOT prove: anything in infinite dimension (Hilbert–Schmidt operators on the
actual boundary space), the HS defect bound itself, (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.HSBasisIndependence

variable {ι κ μ E F : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Parseval for a finite orthonormal basis, in squared real form. -/
theorem parseval_sq (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i, (inner ℝ (b i) x) ^ 2 = ‖x‖ ^ 2 := by
  first
    | (have h := b.sum_inner_mul_inner x x
       rw [real_inner_self_eq_norm_sq] at h
       rw [← h]
       refine Finset.sum_congr rfl fun i _ => ?_
       rw [real_inner_comm x (b i)]
       ring)
    | (rw [← b.repr.norm_map x, EuclideanSpace.norm_eq,
         Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
       refine Finset.sum_congr rfl fun i _ => ?_
       rw [b.repr_apply_apply, Real.norm_eq_abs, sq_abs])

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **G131.** The HS sum over `b` equals the double sum of squared matrix entries in `b`, `d`. -/
theorem hs_sum_eq_double (T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E)
    (d : OrthonormalBasis μ ℝ F) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, ∑ k, (inner ℝ (d k) (T (b i))) ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (parseval_sq d (T (b i))).symm

/-- The HS sum over `b` equals `∑ k, ‖T† (d k)‖²`, which does not involve `b`. -/
theorem hs_sum_eq_adjoint (T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E)
    (d : OrthonormalBasis μ ℝ F) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ k, ‖LinearMap.adjoint T (d k)‖ ^ 2 := by
  rw [hs_sum_eq_double T b d, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← parseval_sq b (LinearMap.adjoint T (d k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.adjoint_inner_right, real_inner_comm (d k) (T (b i))]

/-- **G131.** Basis independence: two orthonormal bases of `E` give the same HS sum. -/
theorem hs_sum_basis_indep (T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E)
    (c : OrthonormalBasis κ ℝ E) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ j, ‖T (c j)‖ ^ 2 := by
  rw [hs_sum_eq_adjoint T b (stdOrthonormalBasis ℝ F),
    hs_sum_eq_adjoint T c (stdOrthonormalBasis ℝ F)]

/-- Non-vacuity: for `T = id` the HS sum is the number of basis vectors. -/
theorem hs_sum_id (b : OrthonormalBasis ι ℝ E) :
    ∑ i, ‖(LinearMap.id : E →ₗ[ℝ] E) (b i)‖ ^ 2 = (Fintype.card ι : ℝ) := by
  have h : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  simp [h]

end SteklovAudit.HSBasisIndependence
