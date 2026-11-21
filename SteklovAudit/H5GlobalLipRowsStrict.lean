import Mathlib
import SteklovAudit.H5GlobalLipRows
import SteklovAudit.H5GlobalVanishNeeded
import SteklovAudit.H5TailAudit

/-!
# G92: the linear-scale rows are sufficient, not necessary, for the G86 inputs

Roadmap item G92. G90 (`H5GlobalLipRows.lean`) derives the G86 inputs `H5bGlobalLipInputs`
(`H5GlobalLip.lean`) from the rows `massLin`, `defectLin`, `δVanish`. This file shows the
converse fails at the level of the mass row: `pdeGlobalLip` is an inhabitant of
`H5bGlobalLipInputs 0 0` (with `Λ = 0`, `F = 0`, `disc = 0`) whose cutoff data are the one-mode
family `pdeD L` of G89 (`H5GlobalVanishNeeded.lean`), and `pdeD_not_massLin` shows that no
constant `m` gives `hs2 (pdeD L).J ≤ m * L` for all `L ≥ 1`, since `hs2 (pdeD L).J = (1 + L) ^ 2`
(`pdeD_hs2J`).

F table text: G86 inputs exist (with `Λ = 0`) whose cutoff data violate `massLin`, so `massLin`
is an extra input of G90, not a consequence of the G86 row.

What this file does NOT prove: `pdeD` is a one-mode toy family, not the cutoff data of any
operator; the witness uses `Λ = 0`, so it says nothing about whether `massLin` holds for the
Steklov operator of the tetrahedron. No field is proved for that operator; no DtN operator is
constructed; (7.29) and Theorem 1.3 / 11.1 remain conditional.
-/

namespace SteklovAudit.H5GlobalLipRowsStrict

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare SteklovAudit.H5SelMin
  SteklovAudit.H5GlobalLip SteklovAudit.H5GlobalLipRows SteklovAudit.H5GlobalVanishNeeded

/-- **G92.** The overlap mass of `pdeD L` is `(1 + L) ^ 2`. -/
theorem pdeD_hs2J (L : ℝ) : hs2 (pdeD L).J = (1 + L) ^ 2 := by
  rw [SteklovAudit.H5TailAudit.hs2_fin_one]
  rfl

/-- **G92.** No linear mass bound holds for `pdeD`: the row `massLin` fails for every `m`. -/
theorem pdeD_not_massLin : ¬ ∃ m : ℝ, ∀ L : ℝ, 1 ≤ L → hs2 (pdeD L).J ≤ m * L := by
  rintro ⟨m, hm⟩
  have hL1 : (1 : ℝ) ≤ max 1 (|m| + 1) := le_max_left _ _
  have hLm : |m| + 1 ≤ max 1 (|m| + 1) := le_max_right _ _
  have h := hm (max 1 (|m| + 1)) hL1
  rw [pdeD_hs2J] at h
  have hL0 : (0 : ℝ) ≤ max 1 (|m| + 1) := by linarith
  have hml : m * max 1 (|m| + 1) ≤ |m| * max 1 (|m| + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self m) hL0
  have hp : 0 ≤ (max 1 (|m| + 1) - (|m| + 1)) * max 1 (|m| + 1) :=
    mul_nonneg (sub_nonneg.2 hLm) hL0
  nlinarith [hml, hp, hL1, abs_nonneg m]

/-- **G92.** G86 inputs (with `Λ = 0`) whose cutoff data are `pdeD L`. -/
noncomputable def pdeGlobalLip :
    H5bGlobalLipInputs (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) where
  nA := fun _ _ _ => 1
  nB := fun _ _ _ => 1
  D := fun _ _ L => pdeD L
  F := fun _ _ _ _ => 0
  disc := fun _ _ _ => 0
  cutoff := by
    intro ε γ L
    first
      | (simp; done)
      | (simp only [sub_self, zero_mul, Finset.sum_const_zero, abs_zero]; exact le_refl _)
  discVanish := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    exact mul_nonneg hη.le hL
  Λ := fun _ _ => 0
  hΛ := fun _ _ => le_refl _
  lip := by
    intro ε γ L x y
    simp
  globalVanish := by
    intro ε γ _ _ η hη
    refine ⟨0, fun L hL => ?_⟩
    have h0 : (0 : ℝ) ≤ η * L := mul_nonneg hη.le hL
    first
      | (rw [zero_mul]; exact h0)
      | (simp only [zero_mul]; exact h0)
      | (show (0 : ℝ) * _ ≤ η * L; rw [zero_mul]; exact h0)
      | simpa using h0

theorem pdeGlobalLip_Λ : pdeGlobalLip.Λ = fun _ _ => 0 := rfl

/-- **G92.** The cutoff data of `pdeGlobalLip` are the one-mode family `pdeD`. -/
theorem pdeGlobalLip_D : pdeGlobalLip.D = fun _ _ L => pdeD L := rfl

end SteklovAudit.H5GlobalLipRowsStrict
