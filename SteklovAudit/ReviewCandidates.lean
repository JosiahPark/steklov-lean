import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Review candidates: Parseval for probes and the Frobenius contraction of a projection

Parseval section: for a real Hilbert basis `b` of `H`, `∑ᵢ ⟨bᵢ, x⟩² = ‖x‖²` (`basis_hasSum_sq`); for a
symmetric operator `A` on a domain `D`, an eigenvector `e` with `A e = λ e` gives
`⟨e, A u − μ u⟩ = (λ − μ) ⟨e, u⟩` (`residual_coordinate`); hence the squared defect
`∑ᵢ (λᵢ − μ)² ⟨bᵢ, u⟩² = ‖r‖²` (`residual_hasSum_sq`), the first moment vanishes when `u ⟂ r`
(`residual_first_moment`), and a finite probe family has total mass `∑ⱼ ‖uⱼ‖²` (`finite_probe_hasSum`).

Projection section: for a real symmetric idempotent matrix `P`, left multiplication by `P` does not
increase the squared Frobenius norm (`projection_frobenius_contracts`). This is the statement that
`AbstractHSDefect.lean` takes as the named hypothesis `ProjFrobeniusContraction`.

What this file does NOT prove: that the tetrahedron's Dirichlet-to-Neumann operator is symmetric on a
domain or has a Hilbert basis of eigenvectors (both enter here only as hypotheses `hA`, `b`, `he`, `hr`),
Lemma 7.1 or (7.2) for any continuum operator, or any of the open gaps (7.2), (7.29), (7.38)/(7.45),
(9.1) or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.ReviewCandidates
open Filter
open scoped Topology
section Parseval
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem basis_hasSum_sq (b : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun i => (inner ℝ (b i) x) ^ 2) (‖x‖ ^ 2) := by
  simpa only [real_inner_comm x, real_inner_self_eq_norm_sq, pow_two]
    using b.hasSum_inner_mul_inner x x
theorem residual_coordinate (D : Submodule ℝ H) (A : D →ₗ[ℝ] H)
    (hA : ∀ u v : D, inner ℝ (A u) (v : H) = inner ℝ (u : H) (A v))
    (e u : D) (lam mu : ℝ) (he : A e = lam • (e : H)) :
    inner ℝ (e : H) (A u - mu • (u : H)) =
      (lam - mu) * inner ℝ (e : H) (u : H) := by
  rw [inner_sub_right, inner_smul_right, ← hA e u, he, real_inner_smul_left]
  ring
theorem residual_hasSum_sq (b : HilbertBasis ι ℝ H) (u r : H)
    (lam : ι → ℝ) (mu : ℝ)
    (hr : ∀ i, inner ℝ (b i) r = (lam i - mu) * inner ℝ (b i) u) :
    HasSum (fun i => (lam i - mu) ^ 2 * (inner ℝ (b i) u) ^ 2) (‖r‖ ^ 2) := by
  simpa only [hr, mul_pow] using basis_hasSum_sq b r
theorem residual_first_moment (b : HilbertBasis ι ℝ H) (u r : H)
    (lam : ι → ℝ) (mu : ℝ)
    (hr : ∀ i, inner ℝ (b i) r = (lam i - mu) * inner ℝ (b i) u)
    (horth : inner ℝ u r = 0) :
    HasSum (fun i => (lam i - mu) * (inner ℝ (b i) u) ^ 2) 0 := by
  have h := b.hasSum_inner_mul_inner u r
  rw [horth] at h
  convert h using 1
  ext i
  rw [hr, real_inner_comm u]
  ring
theorem finite_probe_hasSum {κ : Type*} [Fintype κ] (b : HilbertBasis ι ℝ H)
    (u : κ → H) :
    HasSum (fun p : ι × κ => (inner ℝ (b p.1) (u p.2)) ^ 2) (∑ j, ‖u j‖ ^ 2) := by
  have hs : Summable (fun p : κ × ι => (inner ℝ (b p.2) (u p.1)) ^ 2) :=
    (summable_prod_of_nonneg (fun p => sq_nonneg _)).2
      ⟨fun j => (basis_hasSum_sq b (u j)).summable, (hasSum_fintype _).summable⟩
  have he : (∑' p : κ × ι, (inner ℝ (b p.2) (u p.1)) ^ 2) = ∑ j, ‖u j‖ ^ 2 := by
    rw [hs.tsum_prod]
    simp only [(basis_hasSum_sq b _).tsum_eq, tsum_fintype]
  have hp : HasSum (fun p : κ × ι => (inner ℝ (b p.2) (u p.1)) ^ 2)
      (∑ j, ‖u j‖ ^ 2) := he ▸ hs.hasSum
  exact (Equiv.prodComm ι κ).hasSum_iff.2 hp
end Parseval
section Projection
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n] in
theorem trace_gram (M : Matrix n n ℝ) :
    Matrix.trace (M.transpose * M) = ∑ i, ∑ j, M i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]
theorem projection_frobenius_contracts (P M : Matrix n n ℝ)
    (hsym : P.transpose = P) (hidem : P * P = P) :
    ∑ i, ∑ j, (P * M) i j ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2 := by
  have hgram : (P * M).transpose * (P * M) = M.transpose * P * M := by
    rw [Matrix.transpose_mul, hsym]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc P P, hidem]
  have hcomp : (M - P * M).transpose * (M - P * M) =
      M.transpose * M - M.transpose * P * M := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, hsym]
    noncomm_ring [hidem]
    rw [← Matrix.mul_assoc P P, hidem]
    abel
  have hpos : 0 ≤ ∑ i, ∑ j, (M - P * M) i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← trace_gram, hcomp, Matrix.trace_sub] at hpos
  rw [← trace_gram, ← trace_gram, hgram]
  linarith
end Projection
end SteklovAudit.ReviewCandidates
