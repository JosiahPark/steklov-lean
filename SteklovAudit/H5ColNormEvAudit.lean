import Mathlib
import SteklovAudit.H5ColNormEv
import SteklovAudit.H5RowNormEvAudit

/-!
# G57: the guarded column-normalization form (G56) is non-vacuous and strictly weaker than G49

Roadmap item G57 (mirror of G55 for G56).

* `cnD`: two true eigenvalues and one model eigenvalue, all at `0`, coupling `J 0 0 = 1`, `J 1 0 = 0`.
  Column normalization holds on nonempty data (`cnD_colNorm`), the rows satisfy Bessel, and `K = 0`.
* `colNormEvWitness`: an `H5bColNormEvInputs` (G56) with `nA = 2`, `nB = 1` at every `(ε, γ, L)`,
  gap rate `m1 = 1` (vanishing with `L₀ = 1 / η`, G48's `gapRate_vanish`), `Cm = 1`, `Ck = 0`, `τ = 0`,
  `c = 2`, profile `arctanProfile`, `Φ = 2`.
* `colNormEvWitness_genuine`: `colNorm` is exercised with `nB = 1 > 0`, the truncations are
  non-square and the row gap `nA - nB` is `1`.
* `colNorm_count_neg_one`, `colNormEv_not_colNorm`: the count row of `H5bColNormInputs` (G49) at
  `L = -1` forces `nA = 0`, so no G49 input set has the witness's true truncation sizes; with G56's
  `ofColNorm` the G56 form is strictly weaker.
* `colNormEvWitness_target`: its smoothed counts satisfy `H5bTarget` (from `h5b_of_colNormEv`).

What this file does NOT prove: the witness is a test family, not a model of the Steklov spectrum;
column normalization, the gap row and the count, defect, tail and low-count rows are not proved for
any actual coupling or for the Steklov operator of the tetrahedron; that the paper's `E`, `Emod` are
the smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every
[H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5ColNormEvAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5DiffCount SteklovAudit.H5DiffAudit
open SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval SteklovAudit.H5ColCount
open SteklovAudit.H5EventualRows SteklovAudit.H5EventualTarget

/-- Two true eigenvalues, one model eigenvalue, all at `0`; `J 0 0 = 1`, `J 1 0 = 0`. -/
def cnD : Data (Fin 2) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun i _ => if i.val = 0 then (1 : ℝ) else 0

theorem cnD_colNorm (j : Fin 1) : ∑ i, cnD.J i j ^ 2 = 1 := by
  first
    | (rw [Fin.sum_univ_two]; simp [cnD])
    | (simp [cnD, Fin.sum_univ_two])
    | (rw [Fin.sum_univ_two]; norm_num [cnD])
    | (rw [Fin.sum_univ_two]
       show (if (0 : Fin 2).val = 0 then (1 : ℝ) else 0) ^ 2 +
         (if (1 : Fin 2).val = 0 then (1 : ℝ) else 0) ^ 2 = 1
       rw [if_pos rfl, if_neg (by decide)]; norm_num)

theorem cnD_bessel (i : Fin 2) : ∑ j, cnD.J i j ^ 2 ≤ 1 := by
  rw [Fin.sum_univ_one]
  show (if i.val = 0 then (1 : ℝ) else 0) ^ 2 ≤ 1
  split_ifs <;> norm_num

theorem cnD_K (i : Fin 2) (j : Fin 1) : cnD.K i j = 0 := by
  first | simp [Data.K, cnD] | (unfold Data.K; norm_num [cnD])

theorem cnD_hs2K : hs2 cnD.K = 0 := by
  first | simp [hs2, cnD_K] | (unfold hs2; simp [cnD_K])

theorem cnD_defect (L : ℝ) : hs2 cnD.K ≤ (0 : ℝ) ^ 2 * (1 + L) ^ 2 := by
  rw [cnD_hs2K]
  norm_num

theorem cnD_tail (M : ℝ) : hs2 (mask (hiE cnD M) cnD.K) ≤ 0 :=
  (hs2_mask_le _ _).trans cnD_hs2K.le

theorem cnD_count (L : ℝ) (h : 1 ≤ L) : (Fintype.card (Fin 2) : ℝ) ≤ 1 * (1 + L) ^ 2 := by
  rw [Fintype.card_fin, one_mul]
  first | (push_cast; nlinarith [h]) | (norm_num; nlinarith [h]) | nlinarith [h]

theorem cnD_lowCount (M : ℝ) :
    ((Finset.univ.filter fun i => cnD.a i ≤ M).card : ℝ) ≤ 2 := by
  have h1 : (Finset.univ.filter fun i => cnD.a i ≤ M).card ≤
      (Finset.univ : Finset (Fin 2)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
  have h3 : (Finset.univ.filter fun i => cnD.a i ≤ M).card ≤ 2 := by omega
  exact_mod_cast h3

/-- **G57.** A G56 input set with genuine column normalization (`nB = 1`) and `nA = 2`. -/
noncomputable def colNormEvWitness : SteklovAudit.H5ColNormEv.H5bColNormEvInputs where
  nA := fun _ _ _ => 2
  nB := fun _ _ _ => 1
  D := fun _ _ _ => cnD
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  colNorm := fun _ _ _ _ j => cnD_colNorm j
  bessel := fun _ _ _ _ i => cnD_bessel i
  m1 := fun _ _ _ => 1
  rowGap := fun _ _ _ _ => show ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) ≤ 1 by norm_num
  m1Vanish := SteklovAudit.H5RowNormWitness.gapRate_vanish
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  count := fun _ _ L h => cnD_count L h
  defect := fun _ _ L _ => cnD_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ _ => cnD_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 2
  lowCount := fun _ _ M _ _ => cnD_lowCount M

/-- **G57.** Column normalization is exercised on a nonempty model truncation, the truncations are
non-square, and the row gap is `1`. -/
theorem colNormEvWitness_genuine :
    (∀ ε γ L, 0 < colNormEvWitness.nB ε γ L) ∧
    (∀ ε γ L, colNormEvWitness.nB ε γ L < colNormEvWitness.nA ε γ L) ∧
    (∀ ε γ L, (colNormEvWitness.nA ε γ L : ℝ) - colNormEvWitness.nB ε γ L = 1) ∧
    (∀ ε γ L, 1 ≤ L → ∀ j, ∑ i, (colNormEvWitness.D ε γ L).J i j ^ 2 = 1) :=
  ⟨fun _ _ _ => by first | exact Nat.one_pos | simp [colNormEvWitness],
   fun _ _ _ => by first | exact (show (1 : ℕ) < 2 by norm_num) | simp [colNormEvWitness],
   fun _ _ _ => by
     first
       | exact (show ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) = 1 by norm_num)
       | norm_num [colNormEvWitness],
   colNormEvWitness.colNorm⟩

/-- **G57.** The count row of G49 forces an empty true truncation at `L = -1`. -/
theorem colNorm_count_neg_one (W : SteklovAudit.H5ColNorm.H5bColNormInputs) (ε γ : ℝ) :
    W.nA ε γ (-1) = 0 := by
  have h := W.count ε γ (-1)
  have h0 : W.Cm ε γ * (1 + (-1 : ℝ)) ^ 2 = 0 := by norm_num
  have h1 : (Fintype.card (Fin (W.nA ε γ (-1))) : ℝ) ≤ 0 := h.trans h0.le
  rw [Fintype.card_fin] at h1
  exact_mod_cast le_antisymm h1 (Nat.cast_nonneg _)

/-- **G57.** Strictness: no G49 input set has the witness's true truncation sizes. -/
theorem colNormEv_not_colNorm :
    ¬ ∃ V : SteklovAudit.H5ColNorm.H5bColNormInputs, V.nA = colNormEvWitness.nA := by
  rintro ⟨V, hV⟩
  have h0 := colNorm_count_neg_one V 0 0
  have h1 : colNormEvWitness.nA 0 0 (-1) = 2 := by first | rfl | simp [colNormEvWitness]
  have h2 : colNormEvWitness.nA 0 0 (-1) = 0 := by rw [← hV]; exact h0
  rw [h1] at h2
  omega

/-- **G57.** The witness gives (7.29) for its smoothed counts (from `h5b_of_colNormEv`). -/
theorem colNormEvWitness_target :
    H5bTarget (fun ε γ L => ∑ i, colNormEvWitness.P.φ ((colNormEvWitness.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, colNormEvWitness.P.φ ((colNormEvWitness.D ε γ L).b j - L)) :=
  SteklovAudit.H5ColNormEv.h5b_of_colNormEv colNormEvWitness

end SteklovAudit.H5ColNormEvAudit
