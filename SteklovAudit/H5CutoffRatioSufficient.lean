import Mathlib
import SteklovAudit.H5CutoffInterface

/-!
# Row (i) of the H5 cutoff route from a linear gap and small energy (roadmap item G136)

Row (i) of the H5 cutoff route (`RatioLittleO`, G116) asks that the cutoff ratio
`Lip(F_L) · E_L / (L − μ*(L))` be `o(L)`. This file replaces it by two named inputs:

* `GapLinear Y c L₁`: `0 < c` and `c L ≤ L − μ*(L)` for `L ≥ L₁` (the comparison values keep a
  linear gap below the cutoff);
* `EnergySmall Y`: for every `η > 0`, eventually `Lip(F_L) · E_L ≤ η L²`.

`ratioLittleO_of_gap_energy` shows the two together give (i). `ratio_le_of_gap` records the
intermediate bound `ratio L ≤ Lip L · E_L / (c L)` for `L ≥ max L₁ 1` (under `0 ≤ Lip L · E_L`).

What this file does NOT prove: `GapLinear` or `EnergySmall` for the actual edge family, rows (ii)
and (iii), the existence of such a family, (7.29), H5, or Theorem 1.3 / 11.1. Both inputs are named
hypotheses.
-/

namespace SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff

variable {ι κ : Type*} (Y : H5EdgeFamilyCutoff ι κ)

/-- Named input: the comparison values keep a linear gap `c L` below the cutoff for `L ≥ L₁`. -/
def GapLinear (c L₁ : ℝ) : Prop := 0 < c ∧ ∀ L, L₁ ≤ L → c * L ≤ L - Y.muStar L

/-- Named input: `Lip(F_L) · E_L = o(L²)`. -/
def EnergySmall : Prop :=
  ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → Y.Lip L * (Y.X L).E ≤ η * L ^ 2

/-- **G136.** Under a linear gap, `ratio L ≤ Lip L · E_L / (c L)` for `L ≥ max L₁ 1`
(when `Lip L · E_L ≥ 0`). -/
theorem ratio_le_of_gap {c L₁ : ℝ} (hg : Y.GapLinear c L₁) (L : ℝ) (hL : max L₁ 1 ≤ L)
    (hN : 0 ≤ Y.Lip L * (Y.X L).E) :
    Y.ratio L ≤ Y.Lip L * (Y.X L).E / (c * L) := by
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hL)
  have hcL : 0 < c * L := mul_pos hg.1 hLpos
  have hle : c * L ≤ L - Y.muStar L := hg.2 L hL1
  show Y.Lip L * (Y.X L).E / (L - Y.muStar L) ≤ Y.Lip L * (Y.X L).E / (c * L)
  first
    | exact div_le_div_of_nonneg_left hN hcL hle
    | exact div_le_div_of_le_left hN hcL hle
    | gcongr

/-- **G136.** A linear gap and `Lip · E = o(L²)` give row (i), `RatioLittleO`. -/
theorem ratioLittleO_of_gap_energy {c L₁ : ℝ} (hg : Y.GapLinear c L₁) (he : Y.EnergySmall) :
    Y.RatioLittleO := by
  intro η hη
  obtain ⟨hc, hgap⟩ := hg
  obtain ⟨L₀, hL₀⟩ := he (η * c) (mul_pos hη hc)
  refine ⟨max (max L₁ 1) L₀, fun L hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hone : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL0 : L₀ ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hone
  have hd : c * L ≤ L - Y.muStar L := hgap L hL1
  have hdpos : 0 < L - Y.muStar L := lt_of_lt_of_le (mul_pos hc hLpos) hd
  have hN : Y.Lip L * (Y.X L).E ≤ η * c * L ^ 2 := hL₀ L hL0
  have hextra : 0 ≤ η * L * ((L - Y.muStar L) - c * L) :=
    mul_nonneg (mul_nonneg hη.le hLpos.le) (sub_nonneg.mpr hd)
  show Y.Lip L * (Y.X L).E / (L - Y.muStar L) ≤ η * L
  first
    | (rw [div_le_iff₀ hdpos]; nlinarith [hN, hextra])
    | (rw [div_le_iff hdpos]; nlinarith [hN, hextra])

end SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff
