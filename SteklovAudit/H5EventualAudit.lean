import Mathlib
import SteklovAudit.H5EventualTarget
import SteklovAudit.H5RowNormWitness

/-!
# G53: the eventual-row form is strictly weaker than G40 and not vacuous

Roadmap item G53.

* `smoothed_count_neg_one`: for every `H5bSmoothedInputs` (G40) the count row at `L = -1` reads
  `card ≤ Cm · 0`, so the true truncation is empty there (as G48's `rowNorm_count_neg_one`).
* `evOneD`: one true and one model eigenvalue, both at `0`, coupling `J = 1` (so `K = 0`).
* `evWitness`: an `H5bSmoothedEvInputs` (G51) with `nA = nB = 1` at every `(ε, γ, L)`, rates
  `m1 = m2 = 0`, `Cm = 1`, `Ck = 0`, `τ = 0`, `c = 1`, profile `arctanProfile`, `Φ = 2`. Every guarded
  row is exercised on nonempty data (the count row uses `1 ≤ L`).
* `evWitness_not_smoothed`: no `H5bSmoothedInputs` has the same truncation sizes, so the G51 form is
  strictly weaker than G40 (with G51's `ofSmoothed` for the other direction).
* `evWitness_target`: its smoothed counts satisfy `H5bTarget` (from G52's `h5b_of_smoothedEv`).

What this file does NOT prove: the witness is a test family, not a model of the Steklov spectrum; no
row (count, defect, tail, low count, missing mass, Bessel) is proved for the Steklov operator of the
tetrahedron or for any actual coupling; that the paper's `E`, `Emod` are smoothed counts is not
proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5EventualAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5DiffCount SteklovAudit.H5DiffAudit
open SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval SteklovAudit.H5ColCount
open SteklovAudit.H5EventualRows SteklovAudit.H5EventualTarget

/-- **G53.** On the G40 form the count row forces an empty true truncation at `L = -1`. -/
theorem smoothed_count_neg_one (W : H5bSmoothedInputs) (ε γ : ℝ) : W.nA ε γ (-1) = 0 := by
  have h := W.count ε γ (-1)
  have h0 : W.Cm ε γ * (1 + (-1 : ℝ)) ^ 2 = 0 := by norm_num
  have h1 : (Fintype.card (Fin (W.nA ε γ (-1))) : ℝ) ≤ 0 := h.trans h0.le
  rw [Fintype.card_fin] at h1
  exact_mod_cast le_antisymm h1 (Nat.cast_nonneg _)

/-- One true and one model eigenvalue at `0`, coupling `J = 1`. -/
def evOneD : Data (Fin 1) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 1

theorem evOneD_rowSq (i : Fin 1) : ∑ j, evOneD.J i j ^ 2 = 1 := by
  first | simp [evOneD] | (rw [Fin.sum_univ_one]; norm_num [evOneD])

theorem evOneD_colSq (j : Fin 1) : ∑ i, evOneD.J i j ^ 2 = 1 := by
  first | simp [evOneD] | (rw [Fin.sum_univ_one]; norm_num [evOneD])

theorem evOneD_K (i j : Fin 1) : evOneD.K i j = 0 := by
  first | simp [Data.K, evOneD] | (unfold Data.K; norm_num [evOneD])

theorem evOneD_hs2K : hs2 evOneD.K = 0 := by
  first | simp [hs2, evOneD_K] | (unfold hs2; simp [evOneD_K]) | simp [hs2, Data.K, evOneD]

theorem evOneD_count (L : ℝ) (h : 1 ≤ L) :
    (Fintype.card (Fin 1) : ℝ) ≤ 1 * (1 + L) ^ 2 := by
  rw [Fintype.card_fin, Nat.cast_one, one_mul]
  nlinarith

theorem evOneD_defect (L : ℝ) : hs2 evOneD.K ≤ (0 : ℝ) ^ 2 * (1 + L) ^ 2 := by
  rw [evOneD_hs2K]
  norm_num

theorem evOneD_tail (M : ℝ) : hs2 (mask (hiE evOneD M) evOneD.K) ≤ 0 :=
  (hs2_mask_le _ _).trans evOneD_hs2K.le

theorem evOneD_lowCount (M : ℝ) :
    ((Finset.univ.filter fun i => evOneD.a i ≤ M).card : ℝ) ≤ 1 := by
  have h1 : (Finset.univ.filter fun i => evOneD.a i ≤ M).card ≤
      (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
  have h3 : (Finset.univ.filter fun i => evOneD.a i ≤ M).card ≤ 1 := by omega
  exact_mod_cast h3

/-- **G53.** An `H5bSmoothedEvInputs` with a nonempty true truncation at every `L`. -/
noncomputable def evWitness : H5bSmoothedEvInputs where
  nA := fun _ _ _ => 1
  nB := fun _ _ _ => 1
  D := fun _ _ _ => evOneD
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  m1 := fun _ _ _ => 0
  rowMiss := fun _ _ _ _ => rowMiss_of_rowNorm evOneD evOneD_rowSq
  m1Vanish := zero_vanish
  m2 := fun _ _ _ => 0
  colMiss := fun _ _ _ _ => colMiss_of_colNorm evOneD evOneD_colSq
  m2Vanish := zero_vanish
  colBessel := fun _ _ _ _ j => (evOneD_colSq j).le
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ _ _ i => (evOneD_rowSq i).le
  count := fun _ _ L h => evOneD_count L h
  defect := fun _ _ L _ => evOneD_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ _ => evOneD_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ _ => evOneD_lowCount M

/-- **G53.** The witness has a nonempty true truncation at every `(ε, γ, L)`. -/
theorem evWitness_nonempty (ε γ L : ℝ) : 0 < evWitness.nA ε γ L := by
  first | exact Nat.one_pos | simp [evWitness]

/-- **G53.** Strictness: no G40 input set has the witness's truncation sizes. -/
theorem evWitness_not_smoothed : ¬ ∃ V : H5bSmoothedInputs, V.nA = evWitness.nA := by
  rintro ⟨V, hV⟩
  have h0 := smoothed_count_neg_one V 0 0
  have h1 : evWitness.nA 0 0 (-1) = 1 := by first | rfl | simp [evWitness]
  have h2 : evWitness.nA 0 0 (-1) = 0 := by rw [← hV]; exact h0
  rw [h1] at h2
  exact absurd h2 one_ne_zero

/-- **G53.** The witness gives (7.29) for its smoothed counts (from `h5b_of_smoothedEv`). -/
theorem evWitness_target :
    H5bTarget (fun ε γ L => ∑ i, evWitness.P.φ ((evWitness.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, evWitness.P.φ ((evWitness.D ε γ L).b j - L)) :=
  h5b_of_smoothedEv evWitness

end SteklovAudit.H5EventualAudit
