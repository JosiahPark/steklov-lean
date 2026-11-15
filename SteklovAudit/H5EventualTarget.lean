import Mathlib
import SteklovAudit.H5EventualRows

/-!
# G52: (7.29) for the smoothed counts when the E-free rows hold only for `1 ≤ L`

Roadmap item G52. From `W : H5bSmoothedEvInputs` (G51) we build `toSmoothed W : H5bSmoothedInputs`
(G40) on the glued family `evN`, `evNB`, `evD` of G51, with rates `evM1 W L := if 1 ≤ L then m1 L
else 0` (same for `m2`). For `L < 1` every row holds for the empty data (using `hCm`, `tau_nonneg`,
`c_nonneg`); for `1 ≤ L` each row is transported from `W` by the G50 reindexing lemmas.

* `ev_Esm_eq`, `ev_Emodsm_eq`: for `1 ≤ L` the glued smoothed counts are the original ones;
* `h5b_of_smoothedEv`: `H5bTarget` for the original smoothed counts `∑ i, W.P.φ ((W.D ε γ L).a i - L)`
  and `∑ j, W.P.φ ((W.D ε γ L).b j - L)`.

F table text: on the smoothed route the E-free rows need only hold for `L ≥ 1`.

What this file does NOT prove: no row (count, defect, tail, low count, missing mass, Bessel) is
proved for the Steklov operator of the tetrahedron or for any actual coupling; that the paper's
`E`, `Emod` are these smoothed counts is not proved; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5EventualTarget

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WindowProfile SteklovAudit.H5SmoothedIdent
open SteklovAudit.H5Reindex SteklovAudit.H5EventualRows

variable (W : H5bSmoothedEvInputs)

/-- Glued row missing-mass rate. -/
noncomputable def evM1 (ε γ L : ℝ) : ℝ := if 1 ≤ L then W.m1 ε γ L else 0

/-- Glued column missing-mass rate. -/
noncomputable def evM2 (ε γ L : ℝ) : ℝ := if 1 ≤ L then W.m2 ε γ L else 0

theorem evM1_pos {ε γ L : ℝ} (h : 1 ≤ L) : evM1 W ε γ L = W.m1 ε γ L := by
  unfold evM1; rw [if_pos h]

theorem evM1_neg {ε γ L : ℝ} (h : ¬ 1 ≤ L) : evM1 W ε γ L = 0 := by
  unfold evM1; rw [if_neg h]

theorem evM2_pos {ε γ L : ℝ} (h : 1 ≤ L) : evM2 W ε γ L = W.m2 ε γ L := by
  unfold evM2; rw [if_pos h]

theorem evM2_neg {ε γ L : ℝ} (h : ¬ 1 ≤ L) : evM2 W ε γ L = 0 := by
  unfold evM2; rw [if_neg h]

/-- For `L < 1` the glued data are the empty `zData` reindexed. -/
theorem evD_neg {ε γ L : ℝ} (h : ¬ 1 ≤ L) :
    evD W ε γ L = Data.reindex SteklovAudit.H5CountAudit.zData
      (finCongr (evN_neg W h)) (finCongr (evNB_neg W h)) := by
  first
    | (unfold evD; rw [dif_neg h])
    | simp only [evD, dif_neg h]

theorem hs2_fin0 (M : Fin 0 → Fin 0 → ℝ) : hs2 M = 0 := by
  first
    | (unfold hs2; exact Fin.sum_univ_zero _)
    | simp [hs2]

theorem card_filter_zData (M : ℝ) :
    (Finset.univ.filter fun i => SteklovAudit.H5CountAudit.zData.a i ≤ M).card = 0 := by
  first
    | simp
    | rfl
    | exact Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_not_mem (fun i _ => i.elim0))

/-- **G52.** The guarded rows give the unguarded G40 rows on the glued family. -/
noncomputable def toSmoothed : H5bSmoothedInputs where
  nA := evN W
  nB := evNB W
  D := evD W
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := evM1 W
  rowMiss := fun ε γ L => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_rowMass, evM1_pos W h] <;> exact W.rowMiss ε γ L h
    · rw [evD_neg W h, reindex_rowMass, Fin.sum_univ_zero, evM1_neg W h] <;> exact le_rfl
  m1Vanish := fun ε γ hε hγ η hη => by
    obtain ⟨L₀, hL₀⟩ := W.m1Vanish ε γ hε hγ η hη
    exact ⟨max L₀ 1, fun L hL => by
      rw [evM1_pos W (le_trans (le_max_right _ _) hL)] <;>
        exact hL₀ L (le_trans (le_max_left _ _) hL)⟩
  m2 := evM2 W
  colMiss := fun ε γ L => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_colMass, evM2_pos W h] <;> exact W.colMiss ε γ L h
    · rw [evD_neg W h, reindex_colMass, Fin.sum_univ_zero, evM2_neg W h] <;> exact le_rfl
  m2Vanish := fun ε γ hε hγ η hη => by
    obtain ⟨L₀, hL₀⟩ := W.m2Vanish ε γ hε hγ η hη
    exact ⟨max L₀ 1, fun L hL => by
      rw [evM2_pos W (le_trans (le_max_right _ _) hL)] <;>
        exact hL₀ L (le_trans (le_max_left _ _) hL)⟩
  colBessel := fun ε γ L j => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_colSq] <;> exact W.colBessel ε γ L h _
    · exact absurd (finCongr (evNB_neg W h).symm j).isLt (Nat.not_lt_zero _)
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := fun ε γ L i => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_rowSq] <;> exact W.bessel ε γ L h _
    · exact absurd (finCongr (evN_neg W h).symm i).isLt (Nat.not_lt_zero _)
  count := fun ε γ L => by
    rw [Fintype.card_fin]
    by_cases h : 1 ≤ L
    · have hc := W.count ε γ L h
      rw [Fintype.card_fin] at hc
      rw [← evN_pos W h] <;> exact hc
    · rw [← evN_neg W h, Nat.cast_zero] <;> exact mul_nonneg (W.hCm ε γ) (sq_nonneg _)
  defect := fun ε γ L => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_hs2K] <;> exact W.defect ε γ L h
    · rw [evD_neg W h, reindex_hs2K, hs2_fin0] <;>
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  τ := W.τ
  tail := fun ε γ M L => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_tail] <;> exact W.tail ε γ M L h
    · rw [evD_neg W h, reindex_tail, hs2_fin0] <;> exact tau_nonneg W ε γ M
  Cτ := W.Cτ
  tailRate := W.tailRate
  ha := fun ε γ L i => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_a] <;> exact W.ha ε γ L h _
    · exact absurd (finCongr (evN_neg W h).symm i).isLt (Nat.not_lt_zero _)
  hb := fun ε γ L j => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_b] <;> exact W.hb ε γ L h _
    · exact absurd (finCongr (evNB_neg W h).symm j).isLt (Nat.not_lt_zero _)
  c := W.c
  lowCount := fun ε γ M L => by
    by_cases h : 1 ≤ L
    · rw [evD_pos W h, reindex_lowCount] <;> exact W.lowCount ε γ M L h
    · rw [evD_neg W h, reindex_lowCount, card_filter_zData, Nat.cast_zero] <;>
        exact c_nonneg W ε γ M

/-- **G52.** For `1 ≤ L` the glued true smoothed count is the original one. -/
theorem ev_Esm_eq {ε γ L : ℝ} (h : 1 ≤ L) :
    (toSmoothed W).Esm ε γ L = ∑ i, W.P.φ ((W.D ε γ L).a i - L) := by
  unfold H5bSmoothedInputs.Esm
  show ∑ i, W.P.φ ((evD W ε γ L).a i - L) = _
  rw [evD_pos W h, reindex_smoothedA]

/-- **G52.** For `1 ≤ L` the glued model smoothed count is the original one. -/
theorem ev_Emodsm_eq {ε γ L : ℝ} (h : 1 ≤ L) :
    (toSmoothed W).Emodsm ε γ L = ∑ j, W.P.φ ((W.D ε γ L).b j - L) := by
  unfold H5bSmoothedInputs.Emodsm
  show ∑ j, W.P.φ ((evD W ε γ L).b j - L) = _
  rw [evD_pos W h, reindex_smoothedB]

/-- **G52.** (7.29) for the original smoothed counts, with the E-free rows only for `1 ≤ L`. -/
theorem h5b_of_smoothedEv :
    H5bTarget (fun ε γ L => ∑ i, W.P.φ ((W.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, W.P.φ ((W.D ε γ L).b j - L)) := by
  have hT := h5b_of_smoothed (toSmoothed W)
  unfold H5bTarget at hT ⊢
  intro ε γ hε hγ η hη
  obtain ⟨L₀, hL₀⟩ := hT ε γ hε hγ η hη
  refine ⟨max L₀ 1, fun L hL => ?_⟩
  have h1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hc := hL₀ L (le_trans (le_max_left _ _) hL)
  rw [ev_Esm_eq W h1, ev_Emodsm_eq W h1] at hc
  exact hc

end SteklovAudit.H5EventualTarget
