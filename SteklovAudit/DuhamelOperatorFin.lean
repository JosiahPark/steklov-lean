import Mathlib
import SteklovAudit.DuhamelSpectral
import SteklovAudit.HSBasisIndependence

/-!
# HS Duhamel bound for matrices given with diagonalizations (roadmap item G139)

A `Diag n` is a unitary `U` with real eigenvalues `ev`; it stands for the self-adjoint matrix
`op = U · diag(ev) · Uᴴ` and its propagator `prop t = U · diag(e^{−it·ev}) · Uᴴ` (no matrix
exponential is used). For `J : Matrix (Fin m) (Fin n) ℂ`, in the coordinates `Jhat = U_Aᴴ J U_B` the
defect `A J − J B` and the propagated difference `e^{−itA} J − J e^{−itB}` are entrywise multiples of
`Jhat` (`defect_coords`, `prop_coords`). With the basis independence of the HS norm (G138) and the
spectral-coordinate bound `duhamel_hs_le` (G129) this gives

  `hsSq (e^{−itA} J − J e^{−itB}) ≤ t² · hsSq (A J − J B)`   (`duhamel_hs_matrix`).

What this file does NOT prove: anything for unbounded operators or infinite dimensions (domains,
strongly continuous groups, HS operators on `L²(∂T)`); anything about the Steklov / DtN operator or
its eigenbasis; the bound `ε(h)` on the defect (the HS defect row of the F table); (7.29), H5, or
Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.DuhamelOperatorFin

open Matrix SteklovAudit.HSBasisIndependence SteklovAudit.DuhamelSpectral

/-- A matrix given with an orthonormal eigenbasis (columns of `U`) and real eigenvalues. -/
structure Diag (n : ℕ) where
  U : Matrix (Fin n) (Fin n) ℂ
  hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ
  ev : Fin n → ℝ

variable {m n : ℕ}

/-- The self-adjoint matrix `U · diag(ev) · Uᴴ`. -/
noncomputable def Diag.op (D : Diag n) : Matrix (Fin n) (Fin n) ℂ :=
  D.U * Matrix.diagonal (fun i => ((D.ev i : ℝ) : ℂ)) * D.Uᴴ

/-- The propagator `e^{−itA} = U · diag(e^{−it·ev}) · Uᴴ`. -/
noncomputable def Diag.prop (D : Diag n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  D.U * Matrix.diagonal (fun i => Complex.exp (((-(t * D.ev i) : ℝ) : ℂ) * Complex.I)) * D.Uᴴ

/-- Generic coordinate identity: conjugating `A J − J B` (with `A`, `B` diagonalized) gives an
entrywise multiple of `Jhat = U_Aᴴ J U_B`. -/
theorem conj_comm_coords (UA : Matrix (Fin m) (Fin m) ℂ) (UB : Matrix (Fin n) (Fin n) ℂ)
    (hA : UAᴴ * UA = 1) (hB : UBᴴ * UB = 1) (d1 : Fin m → ℂ) (d2 : Fin n → ℂ)
    (J : Matrix (Fin m) (Fin n) ℂ) :
    UAᴴ * (UA * Matrix.diagonal d1 * UAᴴ * J - J * (UB * Matrix.diagonal d2 * UBᴴ)) * UB =
      Matrix.of (fun i j => (d1 i - d2 j) * (UAᴴ * J * UB) i j) := by
  have e1 : UAᴴ * (UA * Matrix.diagonal d1 * UAᴴ * J) * UB =
      (UAᴴ * UA) * Matrix.diagonal d1 * (UAᴴ * J * UB) := by
    simp only [Matrix.mul_assoc]
  have e2 : UAᴴ * (J * (UB * Matrix.diagonal d2 * UBᴴ)) * UB =
      (UAᴴ * J * UB) * Matrix.diagonal d2 * (UBᴴ * UB) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2, hA, hB, Matrix.one_mul, Matrix.mul_one]
  ext i j
  first
    | (rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]; ring)
    | (simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]; ring)
    | (simp [Matrix.diagonal_mul, Matrix.mul_diagonal]; ring)

/-- **G139.** The defect `A J − J B` in spectral coordinates. -/
theorem defect_coords (DA : Diag m) (DB : Diag n) (J : Matrix (Fin m) (Fin n) ℂ) :
    DA.Uᴴ * (DA.op * J - J * DB.op) * DB.U =
      Matrix.of (fun i j => (((DA.ev i : ℝ) : ℂ) - ((DB.ev j : ℝ) : ℂ)) * (DA.Uᴴ * J * DB.U) i j) := by
  unfold Diag.op
  exact conj_comm_coords DA.U DB.U (unitary_ct_mul_self DA.hU) (unitary_ct_mul_self DB.hU)
    _ _ J

/-- **G139.** The propagated difference `e^{−itA} J − J e^{−itB}` in spectral coordinates. -/
theorem prop_coords (DA : Diag m) (DB : Diag n) (J : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    DA.Uᴴ * (DA.prop t * J - J * DB.prop t) * DB.U =
      Matrix.of (fun i j => (Complex.exp (((-(t * DA.ev i) : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-(t * DB.ev j) : ℝ) : ℂ) * Complex.I)) * (DA.Uᴴ * J * DB.U) i j) := by
  unfold Diag.prop
  exact conj_comm_coords DA.U DB.U (unitary_ct_mul_self DA.hU) (unitary_ct_mul_self DB.hU)
    _ _ J

/-- `hsSq (Uᴴ M) = hsSq M` for `U Uᴴ = 1`. -/
theorem hsSq_ct_left {U : Matrix (Fin m) (Fin m) ℂ} (h : U * Uᴴ = 1)
    (M : Matrix (Fin m) (Fin n) ℂ) : hsSq (Uᴴ * M) = hsSq M := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc U, h, Matrix.one_mul]

/-- **G139.** Passing to spectral coordinates does not change `hsSq`. -/
theorem hsSq_coords (DA : Diag m) (DB : Diag n) (X : Matrix (Fin m) (Fin n) ℂ) :
    hsSq (DA.Uᴴ * X * DB.U) = hsSq X := by
  rw [hsSq_unitary_right DB.hU, hsSq_ct_left (unitary_mul_ct_self DA.hU)]

theorem hsSq_of_mul (c : Fin m → Fin n → ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    hsSq (Matrix.of (fun i j => c i j * X i j)) = ∑ i, ∑ j, ‖X i j‖ ^ 2 * ‖c i j‖ ^ 2 := by
  unfold hsSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply, norm_mul, mul_pow]
  ring

theorem norm_ofReal_sub_sq (a b : ℝ) : ‖(a : ℂ) - (b : ℂ)‖ ^ 2 = (a - b) ^ 2 := by
  rw [← Complex.ofReal_sub]
  first
    | rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    | rw [Complex.norm_eq_abs, Complex.abs_ofReal, sq_abs]
    | simp [sq_abs]

/-- **G139.** HS Duhamel bound for the operators (not only in spectral coordinates):
`hsSq (e^{−itA} J − J e^{−itB}) ≤ t² · hsSq (A J − J B)`. -/
theorem duhamel_hs_matrix (DA : Diag m) (DB : Diag n) (J : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    hsSq (DA.prop t * J - J * DB.prop t) ≤ t ^ 2 * hsSq (DA.op * J - J * DB.op) := by
  calc hsSq (DA.prop t * J - J * DB.prop t)
      = hsSq (DA.Uᴴ * (DA.prop t * J - J * DB.prop t) * DB.U) := (hsSq_coords DA DB _).symm
    _ = ∑ i, ∑ j, ‖(DA.Uᴴ * J * DB.U) i j‖ ^ 2 *
          ‖Complex.exp (((-(t * DA.ev i) : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-(t * DB.ev j) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
        rw [prop_coords]
        unfold hsSq
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.of_apply, norm_mul, mul_pow]
        ring
    _ ≤ t ^ 2 * ∑ i, ∑ j, ‖(DA.Uᴴ * J * DB.U) i j‖ ^ 2 * (DA.ev i - DB.ev j) ^ 2 :=
        duhamel_hs_le (DA.Uᴴ * J * DB.U) DA.ev DB.ev t
    _ = t ^ 2 * hsSq (DA.Uᴴ * (DA.op * J - J * DB.op) * DB.U) := by
        rw [defect_coords]
        unfold hsSq
        congr 1
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.of_apply, norm_mul, mul_pow, norm_ofReal_sub_sq]
        ring
    _ = t ^ 2 * hsSq (DA.op * J - J * DB.op) := by rw [hsSq_coords]

/-- Non-vacuity: with `J = 0` both sides vanish. -/
theorem duhamel_hs_matrix_zero (DA : Diag m) (DB : Diag n) (t : ℝ) :
    hsSq (DA.prop t * (0 : Matrix (Fin m) (Fin n) ℂ) - 0 * DB.prop t) = 0 := by
  simp [hsSq]

end SteklovAudit.DuhamelOperatorFin
