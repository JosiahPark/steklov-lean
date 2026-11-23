import Mathlib
import SteklovAudit.DuhamelOperatorFin

/-!
# Localized HS Duhamel bound (roadmap item G140)

For matrices given with orthonormal eigenbases (`Diag`, G139) and a localizer `Z = z(B)` that is a
function of `B` (`Zof DB z = U_B · diag(z) · U_Bᴴ`), `Z` commutes with `B` and with `e^{−itB}`, so

  `(e^{−itA} J − J e^{−itB}) Z = e^{−itA} (J Z) − (J Z) e^{−itB}`,

and G139 applied to `J Z` gives `hsSq ((e^{−itA} J − J e^{−itB}) Z) ≤ t² · hsSq ((A J − J B) Z)`
(`duhamel_localized_sq`). Under the named hypothesis `DefectSmall` (the localized defect
`‖(A J − J B) Z_h‖_HS ≤ ε(h)`), the square-root form is `≤ |t| · |ε(h)|` (`duhamel_localized_le`).
`defectSmall_zero` shows the hypothesis is satisfiable (`J = 0`, `ε = 0`).

What this file does NOT prove: the defect bound `DefectSmall` for any actual family (it is the open
HS defect row of the F table and stays a named hypothesis); anything in infinite dimensions or about
the Steklov / DtN operator, its domain or eigenbasis; (7.29), H5, or Theorem 1.3 / 11.1.
-/

namespace SteklovAudit.DuhamelLocalized

open Matrix SteklovAudit.HSBasisIndependence SteklovAudit.DuhamelOperatorFin

variable {m n : ℕ}

/-- A localizer that is a function of `B`: `U_B · diag(z) · U_Bᴴ`. -/
noncomputable def Zof (DB : Diag n) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  DB.U * Matrix.diagonal z * DB.Uᴴ

theorem conj_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (h : Uᴴ * U = 1) (a b : Fin n → ℂ) :
    (U * Matrix.diagonal a * Uᴴ) * (U * Matrix.diagonal b * Uᴴ) =
      U * (Matrix.diagonal a * Matrix.diagonal b) * Uᴴ := by
  calc (U * Matrix.diagonal a * Uᴴ) * (U * Matrix.diagonal b * Uᴴ)
      = U * Matrix.diagonal a * (Uᴴ * U) * Matrix.diagonal b * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal a * Matrix.diagonal b) * Uᴴ := by
        rw [h, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem diagonal_mul_comm (a b : Fin n → ℂ) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal b * Matrix.diagonal a := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  first
    | (congr 1; funext i; ring)
    | simp [mul_comm]

/-- Two functions of the same diagonalized matrix commute. -/
theorem conj_diag_comm (U : Matrix (Fin n) (Fin n) ℂ) (h : Uᴴ * U = 1) (a b : Fin n → ℂ) :
    (U * Matrix.diagonal a * Uᴴ) * (U * Matrix.diagonal b * Uᴴ) =
      (U * Matrix.diagonal b * Uᴴ) * (U * Matrix.diagonal a * Uᴴ) := by
  rw [conj_diag_mul U h a b, conj_diag_mul U h b a, diagonal_mul_comm a b]

/-- **G140.** `e^{−itB}` commutes with `Z = z(B)`. -/
theorem prop_comm_Z (DB : Diag n) (z : Fin n → ℂ) (t : ℝ) :
    DB.prop t * Zof DB z = Zof DB z * DB.prop t := by
  unfold Diag.prop Zof
  exact conj_diag_comm DB.U (unitary_ct_mul_self DB.hU) _ _

/-- **G140.** `B` commutes with `Z = z(B)`. -/
theorem op_comm_Z (DB : Diag n) (z : Fin n → ℂ) :
    DB.op * Zof DB z = Zof DB z * DB.op := by
  unfold Diag.op Zof
  exact conj_diag_comm DB.U (unitary_ct_mul_self DB.hU) _ _

/-- **G140.** Moving a commuting localizer inside the difference. -/
theorem localized_eq (P : Matrix (Fin m) (Fin m) ℂ) (J : Matrix (Fin m) (Fin n) ℂ)
    (Q Z : Matrix (Fin n) (Fin n) ℂ) (hQZ : Q * Z = Z * Q) :
    (P * J - J * Q) * Z = P * (J * Z) - (J * Z) * Q := by
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hQZ]

/-- **G140.** Localized HS Duhamel bound, squared form. -/
theorem duhamel_localized_sq (DA : Diag m) (DB : Diag n) (J : Matrix (Fin m) (Fin n) ℂ)
    (z : Fin n → ℂ) (t : ℝ) :
    hsSq ((DA.prop t * J - J * DB.prop t) * Zof DB z) ≤
      t ^ 2 * hsSq ((DA.op * J - J * DB.op) * Zof DB z) := by
  rw [localized_eq _ _ _ _ (prop_comm_Z DB z t), localized_eq _ _ _ _ (op_comm_Z DB z)]
  exact duhamel_hs_matrix DA DB (J * Zof DB z) t

/-- Named hypothesis: the localized defect `‖(A J − J B) Z_h‖_HS ≤ ε(h)` for `h > 0`. -/
def DefectSmall (DA : Diag m) (DB : Diag n) (J : Matrix (Fin m) (Fin n) ℂ)
    (zh : ℝ → Fin n → ℂ) (ε : ℝ → ℝ) : Prop :=
  ∀ h, 0 < h → hsSq ((DA.op * J - J * DB.op) * Zof DB (zh h)) ≤ ε h ^ 2

/-- **G140.** Under `DefectSmall`, `‖(e^{−itA} J − J e^{−itB}) Z_h‖_HS ≤ |t| · |ε(h)|`. -/
theorem duhamel_localized_le (DA : Diag m) (DB : Diag n) (J : Matrix (Fin m) (Fin n) ℂ)
    (zh : ℝ → Fin n → ℂ) (ε : ℝ → ℝ) (hD : DefectSmall DA DB J zh ε) (t h : ℝ) (hh : 0 < h) :
    Real.sqrt (hsSq ((DA.prop t * J - J * DB.prop t) * Zof DB (zh h))) ≤ |t| * |ε h| := by
  have h1 := duhamel_localized_sq DA DB J (zh h) t
  have h2 := hD h hh
  have h3 : hsSq ((DA.prop t * J - J * DB.prop t) * Zof DB (zh h)) ≤ (|t| * |ε h|) ^ 2 := by
    calc hsSq ((DA.prop t * J - J * DB.prop t) * Zof DB (zh h))
        ≤ t ^ 2 * hsSq ((DA.op * J - J * DB.op) * Zof DB (zh h)) := h1
      _ ≤ t ^ 2 * ε h ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg t)
      _ = (|t| * |ε h|) ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
  have hnn : 0 ≤ |t| * |ε h| := by positivity
  first
    | exact (Real.sqrt_le_sqrt h3).trans_eq (Real.sqrt_sq hnn)
    | exact Real.sqrt_le_iff.mpr ⟨hnn, h3⟩
    | exact (Real.sqrt_le_left hnn).mpr h3

/-- Non-vacuity: `J = 0` satisfies `DefectSmall` with `ε = 0`. -/
theorem defectSmall_zero (DA : Diag m) (DB : Diag n) (zh : ℝ → Fin n → ℂ) :
    DefectSmall DA DB (0 : Matrix (Fin m) (Fin n) ℂ) zh (fun _ => 0) := by
  intro h _
  rw [Matrix.mul_zero, Matrix.zero_mul, sub_self, Matrix.zero_mul, hsSq_zero]
  exact sq_nonneg _

end SteklovAudit.DuhamelLocalized
