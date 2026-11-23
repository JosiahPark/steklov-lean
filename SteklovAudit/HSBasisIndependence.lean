import Mathlib

/-!
# The Hilbert–Schmidt norm does not depend on the orthonormal basis (roadmap item G138)

For a complex matrix `M` put `hsSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2` (the squared HS norm in the given
coordinates). This file shows `hsSq M = Re tr (Mᴴ M)` and that `hsSq` is unchanged by unitary
changes of basis on either side: `hsSq (U * M * V) = hsSq M` for unitary `U`, `V`.

Consequence for the F table: the spectral-coordinate HS norms used in G129/G134 equal the HS norm
of the operator in any orthonormal basis.

What this file does NOT prove: anything in infinite dimensions (HS operators on `L²(∂T)`, trace
class, basis independence for infinite orthonormal bases), anything about the Steklov /
Dirichlet-to-Neumann operator or its eigenbasis, (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.HSBasisIndependence

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Squared Hilbert–Schmidt norm of a complex matrix in the given coordinates. -/
def hsSq (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

theorem re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  have h : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    first
      | rw [Complex.sq_norm, Complex.normSq_apply]
      | rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [h]
  first
    | (show ((starRingEnd ℂ) z * z).re = _
       simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
       ring)
    | (simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
       ring)
    | (simp [Complex.mul_re]; ring)
    | simp [Complex.mul_re]

/-- **G138.** `hsSq` is nonnegative. -/
theorem hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **G138.** `hsSq 0 = 0`. -/
theorem hsSq_zero : hsSq (0 : Matrix m n ℂ) = 0 := by
  simp [hsSq]

/-- **G138.** `hsSq M = Re tr (Mᴴ M)`. -/
theorem hsSq_eq_trace (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  unfold hsSq
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  exact (re_star_mul_self _).symm

variable [DecidableEq m] [DecidableEq n]

theorem unitary_ct_mul_self {U : Matrix m m ℂ}
    (hU : U ∈ Matrix.unitaryGroup m ℂ) : Uᴴ * U = 1 := by
  first
    | exact Matrix.mem_unitaryGroup_iff'.mp hU
    | exact unitary.star_mul_self_of_mem hU
    | exact Unitary.star_mul_self_of_mem hU

theorem unitary_mul_ct_self {U : Matrix m m ℂ}
    (hU : U ∈ Matrix.unitaryGroup m ℂ) : U * Uᴴ = 1 := by
  first
    | exact Matrix.mem_unitaryGroup_iff.mp hU
    | exact unitary.mul_star_self_of_mem hU
    | exact Unitary.mul_star_self_of_mem hU

/-- **G138.** A unitary change of basis on the left leaves `hsSq` unchanged. -/
theorem hsSq_unitary_left {U : Matrix m m ℂ} (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (M : Matrix m n ℂ) : hsSq (U * M) = hsSq M := by
  have h : Uᴴ * U = 1 := unitary_ct_mul_self hU
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ, h, Matrix.one_mul]

/-- **G138.** A unitary change of basis on the right leaves `hsSq` unchanged. -/
theorem hsSq_unitary_right {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (M : Matrix m n ℂ) : hsSq (M * V) = hsSq M := by
  have h : V * Vᴴ = 1 := unitary_mul_ct_self hV
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Matrix.trace (Vᴴ * Mᴴ * (M * V)) = Matrix.trace (Vᴴ * (Mᴴ * M * V)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M * V * Vᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Mᴴ * M) := by rw [Matrix.mul_assoc (Mᴴ * M), h, Matrix.mul_one]

/-- **G138.** Unitary changes of basis on both sides leave `hsSq` unchanged. -/
theorem hsSq_conj_unitary {U : Matrix m m ℂ} (hU : U ∈ Matrix.unitaryGroup m ℂ)
    {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) (M : Matrix m n ℂ) :
    hsSq (U * M * V) = hsSq M := by
  rw [hsSq_unitary_right hV, hsSq_unitary_left hU]

end SteklovAudit.HSBasisIndependence
