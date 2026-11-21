import Mathlib
import SteklovAudit.H5GlobalLipRows
import SteklovAudit.H5TailAudit

/-!
# G97: `massEv` cannot be dropped from the G94 rows

Roadmap item G97. G94 (`H5GlobalLipRowsEv.lean`) derives the G86 row `globalVanish` from an
eventual `O(L)` mass row `massEv` and an `o(L)` defect row `defectSmall`. This file shows the
mass row is a necessary separate input. `bigD L : Data (Fin 1) (Fin 1)` is one-mode cutoff data
with eigenvalues `a = 1 / L`, `b = 0` and overlap `J = L`, so `hs2 J = L ^ 2` (`bigD_hs2J`) and,
for `L ≠ 0`, the defect `K = (1 / L) * L` has `hs2 K = 1` (`bigD_hs2K`). The defect is `o(L)`
(`bigD_defectSmall`), but no eventual linear mass bound holds (`bigD_not_massEv`), and the
unsplit defect/overlap product is exactly `L` (`bigD_prod`), so it is not eventually `≤ L / 2`
(`bigD_not_vanish`): `globalVanish` fails with `Λ = 1` and `η = 1 / 2`.

F table text: an `o(L)` defect alone does not give `globalVanish` (with `Λ = 1`); the mass row
is a necessary separate input.

What this file does NOT prove: `bigD` is a one-mode toy family, not the cutoff data of any
operator, so nothing here says whether `massEv`, `defectSmall` or any other row holds for the
Steklov operator of the tetrahedron. No field is proved for that operator; no DtN operator is
constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5MassEvNeeded

open SteklovAudit SteklovAudit.AbstractTransfer

/-- One-mode data with eigenvalues `1 / L` and `0` and overlap `L`, so that `K = (1 / L) * L`. -/
noncomputable def bigD (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 1 / L
  b := fun _ => 0
  J := fun _ _ => L

/-- **G97.** The overlap mass of `bigD L` is `L ^ 2`. -/
theorem bigD_hs2J (L : ℝ) : hs2 (bigD L).J = L ^ 2 := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one] <;> rfl

/-- **G97.** The defect mass of `bigD L` is `1` for `L ≠ 0`. -/
theorem bigD_hs2K (L : ℝ) (hL : L ≠ 0) : hs2 (bigD L).K = 1 := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  show ((1 / L - 0) * L) ^ 2 = (1 : ℝ)
  first
  | (rw [sub_zero, one_div_mul_cancel hL]; norm_num)
  | (rw [sub_zero, div_mul_cancel₀ (1 : ℝ) hL]; norm_num)
  | (field_simp)
  | simp [hL]

/-- **G97.** The defect of `bigD` is `o(L)`: the G94 row `defectSmall` holds. -/
theorem bigD_defectSmall : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    hs2 (bigD L).K ≤ η * L := by
  intro η hη
  refine ⟨1 / η + 1, fun L hL => ?_⟩
  have hpos : 0 < 1 / η := one_div_pos.mpr hη
  have hL0 : 0 < L := by linarith
  rw [bigD_hs2K L hL0.ne']
  have h1 : η * (1 / η) = 1 := by
    first
    | exact mul_one_div_cancel hη.ne'
    | field_simp
  have h2 : η * (1 / η + 1) ≤ η * L := mul_le_mul_of_nonneg_left hL hη.le
  nlinarith

/-- **G97.** No eventual linear mass bound holds for `bigD`: the G94 row `massEv` fails. -/
theorem bigD_not_massEv : ¬ ∃ m L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L → hs2 (bigD L).J ≤ m * L := by
  rintro ⟨m, L₁, h⟩
  have hL1 : |m| + 1 ≤ max L₁ (|m| + 1) := le_max_right _ _
  have hle := h (max L₁ (|m| + 1)) (le_max_left _ _)
  rw [bigD_hs2J] at hle
  generalize max L₁ (|m| + 1) = L at hL1 hle
  have hm : m ≤ |m| := le_abs_self m
  have hLpos : 0 < L := by linarith [abs_nonneg m]
  nlinarith [mul_le_mul_of_nonneg_left hL1 hLpos.le, mul_le_mul_of_nonneg_left hm hLpos.le]

/-- **G97.** The unsplit defect/overlap product of `bigD L` is `L` for `0 < L`. -/
theorem bigD_prod (L : ℝ) (hL : 0 < L) :
    Real.sqrt (hs2 (bigD L).K * hs2 (bigD L).J) = L := by
  rw [bigD_hs2K L hL.ne', bigD_hs2J, one_mul]
  exact Real.sqrt_sq hL.le

/-- **G97.** The product is not eventually `≤ L / 2`: `globalVanish` fails for `bigD` with
`Λ = 1` and `η = 1 / 2`, although the defect is `o(L)`. -/
theorem bigD_not_vanish : ¬ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    1 * Real.sqrt (hs2 (bigD L).K * hs2 (bigD L).J) ≤ (1 / 2) * L := by
  rintro ⟨L₀, h⟩
  have h1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have hv := h (max L₀ 1) (le_max_left _ _)
  rw [bigD_prod (max L₀ 1) (by linarith)] at hv
  linarith

end SteklovAudit.H5MassEvNeeded
