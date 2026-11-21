import Mathlib
import SteklovAudit.H5GlobalLipRowsEv
import SteklovAudit.H5TailAudit

/-!
# G95: the G94 mass row is strictly weaker than the G90 row `massLin`

Roadmap item G95. G94 (`H5GlobalLipRowsEv.lean`) replaced the G90 row
`massLin : ∀ L, 1 ≤ L → hs2 J ≤ m * L` by the eventual row `massEv` (the bound only for
`L ≥ L₁`). This file shows the replacement is strict. `evD L : Data (Fin 1) (Fin 1)` has
eigenvalues `a = b = 0` (so its defect `K` vanishes, `evD_hs2K`) and overlap
`J = √(1 / (L - 1))` for `L < 2`, `J = 0` for `L ≥ 2`. It satisfies the eventual mass row with
`m = 0`, `L₁ = 2` (`evD_massEv`), but no constant `m` gives `hs2 J ≤ m * L` on all of `L ≥ 1`,
because `hs2 J = 1 / (L - 1)` blows up as `L ↓ 1` (`evD_no_massLin`).

F table text: the eventual mass row of G94 admits cutoff data that no G90 `massLin` row (any
`m`) admits; the defect rows hold trivially there (`K = 0`).

What this file does NOT prove: `evD` is a one-mode toy family, not the cutoff data of any
operator, so nothing here says whether `massEv`, `massLin` or any other row holds for the
Steklov operator of the tetrahedron. No field is proved for that operator; no DtN operator is
constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5GlobalLipRowsEvStrict

open SteklovAudit SteklovAudit.AbstractTransfer

/-- One-mode data with zero eigenvalues and overlap `√(1 / (L - 1))` below `L = 2`, zero from
`L = 2` on. -/
noncomputable def evD (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => if L < 2 then Real.sqrt (1 / (L - 1)) else 0

/-- **G95.** The defect of `evD L` vanishes. -/
theorem evD_hs2K (L : ℝ) : hs2 (evD L).K = 0 := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  show ((0 - 0) * (if L < 2 then Real.sqrt (1 / (L - 1)) else 0)) ^ 2 = (0 : ℝ)
  first
  | simp
  | (rw [sub_self, zero_mul]; norm_num)

/-- **G95.** `evD` satisfies the eventual mass row of G94 with `m = 0` and `L₁ = 2`. -/
theorem evD_massEv : ∀ L : ℝ, 2 ≤ L → hs2 (evD L).J ≤ 0 * L := by
  intro L hL
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  show (if L < 2 then Real.sqrt (1 / (L - 1)) else 0) ^ 2 ≤ 0 * L
  first
  | (rw [if_neg (not_lt.mpr hL)]; norm_num)
  | simp [not_lt.mpr hL]

/-- The overlap of `evD (1 + s)` squares to `1 / s` for `0 < s < 1`. -/
theorem evD_J_sq (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (evD (1 + s)).J 0 0 ^ 2 = 1 / s := by
  show (if 1 + s < 2 then Real.sqrt (1 / (1 + s - 1)) else 0) ^ 2 = 1 / s
  rw [if_pos (show 1 + s < 2 by linarith), show 1 + s - 1 = s by ring]
  exact Real.sq_sqrt (one_div_pos.mpr hs).le

/-- **G95.** No constant `m` makes `evD` satisfy the G90 row `massLin`. -/
theorem evD_no_massLin : ¬ ∃ m : ℝ, ∀ L : ℝ, 1 ≤ L → hs2 (evD L).J ≤ m * L := by
  rintro ⟨m, hm⟩
  have hne : 2 * (|m| + 1) ≠ 0 := by positivity
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = 1 / (2 * (|m| + 1)) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; positivity
  have hmul : s * (2 * (|m| + 1)) = 1 := by
    rw [hs_def]
    first
    | exact one_div_mul_cancel hne
    | exact div_mul_cancel₀ 1 hne
    | field_simp
  have hinv : 1 / s = 2 * (|m| + 1) := by
    rw [hs_def]
    first
    | exact one_div_one_div _
    | field_simp
  have hs_le : s ≤ 1 / 2 := by
    nlinarith [mul_nonneg hs.le (abs_nonneg m)]
  have h := hm (1 + s) (by linarith)
  rw [SteklovAudit.H5TailAudit.hs2_fin_one, evD_J_sq s hs (by linarith), hinv] at h
  nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self m)) (show (0 : ℝ) ≤ 1 + s by linarith),
    mul_nonneg (abs_nonneg m) (show (0 : ℝ) ≤ 1 / 2 - s by linarith), abs_nonneg m]

end SteklovAudit.H5GlobalLipRowsEvStrict
