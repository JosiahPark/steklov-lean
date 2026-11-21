import Mathlib
import SteklovAudit.H5GlobalLipRowsPow
import SteklovAudit.H5GlobalLipRows
import SteklovAudit.H5TailAudit

/-!
# G99: the G98 trade-off rows are strictly weaker than the G94 rows

Roadmap item G99. G98 (`H5GlobalLipRowsPow.lean`) replaces the G94 pair (`massEv`: eventual
`O(L)` overlap mass; `defectSmall`: `o(L)` defect) by a pair that may trade powers of `L`.
This file exhibits one-mode cutoff data satisfying the G98 pair with `p = 2` but violating the
G94 mass row. `powD L : Data (Fin 1) (Fin 1)` has eigenvalues `a = 1 / L ^ 2`, `b = 0` and overlap
`J = L`, so `hs2 J = L ^ 2` (`powD_hs2J`) and, for `L ≠ 0`, `hs2 K = 1 / L ^ 2` (`powD_hs2K`).
Then `massPow` holds with `m = 1`, `p = 2` (`powD_massPow`), `defectPow` holds with exponent
`2 - 2 = 0` (`powD_defectPow`), and no eventual linear mass bound holds (`powD_not_massEv`).

F table text: the G98 rows (with `p = 2`) admit cutoff data that no G94 row admits.

What this file does NOT prove: `powD` is a one-mode toy family, not the cutoff data of any
operator. Nothing here says whether `massPow`, `defectPow` (for any `p`) or any other row holds
for the Steklov operator of the tetrahedron; no DtN operator is constructed; (7.29) and
Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5GlobalLipRowsPowStrict

open SteklovAudit SteklovAudit.AbstractTransfer

/-- One-mode data with eigenvalues `1 / L ^ 2` and `0` and overlap `L`. -/
noncomputable def powD (L : ℝ) : Data (Fin 1) (Fin 1) where
  a := fun _ => 1 / L ^ 2
  b := fun _ => 0
  J := fun _ _ => L

/-- **G99.** The overlap mass of `powD L` is `L ^ 2`. -/
theorem powD_hs2J (L : ℝ) : hs2 (powD L).J = L ^ 2 := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one] <;> rfl

/-- **G99.** The defect mass of `powD L` is `1 / L ^ 2` for `L ≠ 0`. -/
theorem powD_hs2K (L : ℝ) (hL : L ≠ 0) : hs2 (powD L).K = 1 / L ^ 2 := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  show ((1 / L ^ 2 - 0) * L) ^ 2 = 1 / L ^ 2
  first
  | (rw [sub_zero]; field_simp; ring)
  | (rw [sub_zero]; field_simp)
  | (field_simp; ring)
  | field_simp

/-- **G99.** The G98 row `massPow` holds for `powD` with `m = 1`, `p = 2`. -/
theorem powD_massPow : ∀ L : ℝ, 1 ≤ L → hs2 (powD L).J ≤ 1 * L ^ (2 : ℝ) := by
  intro L _
  have h : L ^ (2 : ℝ) = L ^ 2 := by
    first
    | exact Real.rpow_two L
    | exact_mod_cast Real.rpow_natCast L 2
    | norm_num
  rw [powD_hs2J, one_mul]
  exact h.symm.le

/-- **G99.** The G98 row `defectPow` holds for `powD` with `p = 2` (exponent `2 - 2 = 0`). -/
theorem powD_defectPow : ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    hs2 (powD L).K ≤ η * L ^ ((2 : ℝ) - 2) := by
  intro η hη
  refine ⟨max 1 (1 / η), fun L hL => ?_⟩
  have h1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have h2 : 1 / η ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  rw [powD_hs2K L hL0.ne', sub_self, Real.rpow_zero, mul_one]
  have h3 : η * (1 / η) = 1 := by
    first
    | exact mul_one_div_cancel hη.ne'
    | field_simp
  have h4 : η * (1 / η) ≤ η * L := mul_le_mul_of_nonneg_left h2 hη.le
  have hηL : 1 ≤ η * L := by linarith
  have h5 : 1 * L ≤ η * L * L := mul_le_mul_of_nonneg_right hηL hL0.le
  have hL2 : 0 < L ^ 2 := by positivity
  have h6 : 1 ≤ η * L ^ 2 := by nlinarith
  first
  | (rw [div_le_iff₀ hL2]; linarith)
  | (rw [div_le_iff hL2]; linarith)
  | (calc 1 / L ^ 2 ≤ (η * L ^ 2) / L ^ 2 := by gcongr
      _ = η := by field_simp)

/-- **G99.** No eventual linear mass bound holds for `powD`: the G94 row `massEv` fails. -/
theorem powD_not_massEv : ¬ ∃ m L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L → hs2 (powD L).J ≤ m * L := by
  rintro ⟨m, L₁, h⟩
  have hL1 : |m| + 1 ≤ max L₁ (|m| + 1) := le_max_right _ _
  have hle := h (max L₁ (|m| + 1)) (le_max_left _ _)
  rw [powD_hs2J] at hle
  generalize max L₁ (|m| + 1) = L at hL1 hle
  have hm : m ≤ |m| := le_abs_self m
  have hLpos : 0 < L := by linarith [abs_nonneg m]
  nlinarith [mul_le_mul_of_nonneg_left hL1 hLpos.le, mul_le_mul_of_nonneg_left hm hLpos.le]

end SteklovAudit.H5GlobalLipRowsPowStrict
