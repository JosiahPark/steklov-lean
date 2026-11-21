import Mathlib
import SteklovAudit.H5GlobalLipRows
import SteklovAudit.H5TailAudit

/-!
# G93: `δVanish` is the row that carries the `o(L)`

Roadmap item G93. G90 (`H5GlobalLipRows.lean`) derives the G86 row `globalVanish` from three
rows at the linear scale: `massLin`, `defectLin` and `δVanish`. This file shows that the first
two alone give only `O(L)`. `linD L : Data (Fin 1) (Fin 1)` is one-mode cutoff data with
eigenvalues `a = 1`, `b = 0` and overlap `J = √L`, so its defect is `K = √L`. For `L ≥ 1` it
satisfies `massLin` with `m = 1` (`linD_massLin`) and `defectLin` with the constant rate
`δ = 1` (`linD_defectLin`), but the unsplit defect/overlap product is exactly `L`
(`linD_prod`), so it is not eventually `≤ L / 2` (`linD_not_vanish`): the row `globalVanish`
fails with `Λ = 1` and `η = 1 / 2`.

F table text: `massLin` and `defectLin` with a constant `δ = 1` give only `O(L)`; without
`δVanish` the row `globalVanish` fails.

What this file does NOT prove: `linD` is a one-mode toy family, not the cutoff data of any
operator, so nothing here says whether `δVanish` (or any other row) holds for the Steklov
operator of the tetrahedron. No field is proved for that operator; no DtN operator is
constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5DeltaVanishNeeded

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows

/-- One-mode data with eigenvalues `1` and `0` and overlap `√L`, so that `K = √L`. -/
noncomputable def linD (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 1
  b := fun _ => 0
  J := fun _ _ => Real.sqrt L

/-- The overlap mass of `linD L` is `L` for `0 ≤ L`. -/
theorem linD_hs2J (L : ℝ) (hL : 0 ≤ L) : hs2 (linD L).J = L := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  show Real.sqrt L ^ 2 = L
  exact Real.sq_sqrt hL

/-- The defect mass of `linD L` is `L` for `0 ≤ L`. -/
theorem linD_hs2K (L : ℝ) (hL : 0 ≤ L) : hs2 (linD L).K = L := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  show ((1 - 0) * Real.sqrt L) ^ 2 = L
  rw [sub_zero, one_mul]
  exact Real.sq_sqrt hL

/-- **G93.** `linD` satisfies the row `massLin` with `m = 1`. -/
theorem linD_massLin : ∀ L : ℝ, 1 ≤ L → hs2 (linD L).J ≤ 1 * L := by
  intro L hL
  rw [linD_hs2J L (by linarith), one_mul]

/-- **G93.** `linD` satisfies the row `defectLin` with the constant rate `δ = 1`. -/
theorem linD_defectLin : ∀ L : ℝ, 1 ≤ L → hs2 (linD L).K ≤ 1 * L := by
  intro L hL
  rw [linD_hs2K L (by linarith), one_mul]

/-- **G93.** The unsplit defect/overlap product of `linD L` is `L`. -/
theorem linD_prod : ∀ L : ℝ, 0 ≤ L →
    Real.sqrt (hs2 (linD L).K * hs2 (linD L).J) = L := by
  intro L hL
  rw [linD_hs2K L hL, linD_hs2J L hL]
  exact Real.sqrt_mul_self hL

/-- **G93.** The product is not eventually `≤ L / 2`: the row `globalVanish` fails for `linD`
with `Λ = 1` and `η = 1 / 2`, although `massLin` and `defectLin` hold with `m = δ = 1`. -/
theorem linD_not_vanish : ¬ ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    1 * Real.sqrt (hs2 (linD L).K * hs2 (linD L).J) ≤ (1 / 2) * L := by
  rintro ⟨L₀, hL⟩
  have h1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h := hL (max L₀ 1) (le_max_left _ _)
  rw [linD_prod (max L₀ 1) (by linarith)] at h
  linarith

end SteklovAudit.H5DeltaVanishNeeded
