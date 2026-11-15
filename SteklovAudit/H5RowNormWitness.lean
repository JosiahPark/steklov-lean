import Mathlib
import SteklovAudit.H5Parseval
import SteklovAudit.H5ColCount
import SteklovAudit.H5DiffAudit

/-!
# G48: the normalization structures are satisfiable, including a non-square case

Roadmap item G48.

* `normWitness`, `normWitness_nonempty`: `H5bNormInputs` (G44) is not vacuous. The witness is G24's
  empty family `zData` (no true and no model eigenvalues), so `rowNorm` and `colNorm` hold vacuously.
* `rowNorm_count_neg_one`: for every `H5bRowNormInputs` the count row at `L = -1` reads
  `card ι ≤ Cm · 0`, so the true truncation is empty there. Hence no witness can have `nA = 1` for all
  `L`, and the preferred witness of the roadmap (`nA = 1`, `nB = 2`) is excluded by the count row.
* `gapD`: no true eigenvalues, one model eigenvalue at `0`, `J = 0`.
* `rowNormWitness`, `rowNormWitness_nonsquare`: an `H5bRowNormInputs` (G46) with `nA = 0 < 1 = nB` at
  every `(ε, γ, L)`, gap rate `m2 = 1` (`m2Vanish` with `L₀ = 1 / η`). `rowNorm` is vacuous here
  (`Fin 0`); the gap row and the column Bessel row are the rows actually exercised.
* `rowNormWitness_target`: its smoothed counts satisfy `H5bTarget` (from `h5b_of_rowNorm`).

What this file does NOT prove: the witnesses are test families, not models of the Steklov spectrum;
row or column normalization, the truncation-size gap, and the count, defect, tail and low-count rows
are not proved for any actual coupling or for the Steklov operator of the tetrahedron; that the
paper's `E`, `Emod` equal the smoothed counts is not proved; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5RowNormWitness

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5DiffCount SteklovAudit.H5DiffAudit
open SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval SteklovAudit.H5ColCount

/-- **G48.** `H5bNormInputs` filled by G24's empty family (vacuous normalization). -/
noncomputable def normWitness : H5bNormInputs where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  rowNorm := fun _ _ _ i => by first | exact i.elim0 | exact absurd i.2 (Nat.not_lt_zero _)
  colNorm := fun _ _ _ j => by first | exact j.elim0 | exact absurd j.2 (Nat.not_lt_zero _)
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  count := fun _ _ L => z_count L
  defect := fun _ _ L => z_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ => z_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ => z_lowCount M

/-- **G48.** The two-sided normalization structure is satisfiable. -/
theorem normWitness_nonempty : Nonempty H5bNormInputs := ⟨normWitness⟩

/-- **G48.** The count row forces an empty true truncation at `L = -1`. -/
theorem rowNorm_count_neg_one (W : H5bRowNormInputs) (ε γ : ℝ) : W.nA ε γ (-1) = 0 := by
  have h := W.count ε γ (-1)
  have h0 : W.Cm ε γ * (1 + (-1 : ℝ)) ^ 2 = 0 := by norm_num
  have h1 : (Fintype.card (Fin (W.nA ε γ (-1))) : ℝ) ≤ 0 := h.trans h0.le
  rw [Fintype.card_fin] at h1
  exact_mod_cast le_antisymm h1 (Nat.cast_nonneg _)

/-- No true eigenvalues, one model eigenvalue at `0`, `J = 0`. -/
def gapD : Data (Fin 0) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 0

theorem gapD_colBessel (j : Fin 1) : ∑ i, gapD.J i j ^ 2 ≤ 1 := by
  first | (rw [Fin.sum_univ_zero]; norm_num) | simp

theorem gapD_count (L : ℝ) : (Fintype.card (Fin 0) : ℝ) ≤ 1 * (1 + L) ^ 2 := by
  rw [Fintype.card_fin, Nat.cast_zero, one_mul]
  positivity

theorem gapD_defect (L : ℝ) : hs2 gapD.K ≤ (0 : ℝ) ^ 2 * (1 + L) ^ 2 := by
  first | (unfold hs2; rw [Fin.sum_univ_zero]; norm_num) | simp [hs2]

theorem gapD_tail (M : ℝ) : hs2 (mask (hiE gapD M) gapD.K) ≤ 0 := by
  first | (unfold hs2; rw [Fin.sum_univ_zero]) | simp [hs2]

theorem gapD_lowCount (M : ℝ) :
    ((Finset.univ.filter fun i => gapD.a i ≤ M).card : ℝ) ≤ 1 := by
  have h : (Finset.univ.filter fun i : Fin 0 => gapD.a i ≤ M).card = 0 := by
    first | simp | exact Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _)
  rw [h, Nat.cast_zero]
  exact zero_le_one

/-- The constant rate `1` is `o(L)` (take `L₀ = 1 / η`). -/
theorem gapRate_vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    ((fun _ _ _ => (1 : ℝ)) : ℝ → ℝ → ℝ → ℝ) ε γ L ≤ η * L := by
  intro _ _ _ _ η hη
  refine ⟨1 / η, fun L hL => ?_⟩
  show (1 : ℝ) ≤ η * L
  have h1 : η * (1 / η) = 1 := by
    first | exact mul_one_div_cancel hη.ne' | field_simp
  calc (1 : ℝ) = η * (1 / η) := h1.symm
    _ ≤ η * L := mul_le_mul_of_nonneg_left hL hη.le

/-- **G48.** A non-square `H5bRowNormInputs`: `nA = 0`, `nB = 1`, gap rate `1`. -/
noncomputable def rowNormWitness : H5bRowNormInputs where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 1
  D := fun _ _ _ => gapD
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  rowNorm := fun _ _ _ i => by first | exact i.elim0 | exact absurd i.2 (Nat.not_lt_zero _)
  colBessel := fun _ _ _ j => gapD_colBessel j
  m2 := fun _ _ _ => 1
  cardGap := fun _ _ _ => show ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) ≤ 1 by norm_num
  m2Vanish := gapRate_vanish
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  count := fun _ _ L => gapD_count L
  defect := fun _ _ L => gapD_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ => gapD_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ => gapD_lowCount M

/-- **G48.** One-sided normalization admits truncations of different sizes. -/
theorem rowNormWitness_nonsquare :
    ∃ W : H5bRowNormInputs, ∀ ε γ L, W.nA ε γ L < W.nB ε γ L :=
  ⟨rowNormWitness, fun _ _ _ => by first | exact (show (0 : ℕ) < 1 from Nat.zero_lt_one) | simp [rowNormWitness]⟩

/-- **G48.** The non-square witness gives (7.29) for its smoothed counts. -/
theorem rowNormWitness_target :
    H5bTarget (smoothedOfRowNorm rowNormWitness).Esm (smoothedOfRowNorm rowNormWitness).Emodsm :=
  h5b_of_rowNorm rowNormWitness

end SteklovAudit.H5RowNormWitness
