import Mathlib
import SteklovAudit.H5RowNormEv
import SteklovAudit.H5EventualAudit

/-!
# G55: the guarded row-normalization form (G54) is non-vacuous and strictly weaker than G46

Roadmap item G55.

* `rnD`: one true eigenvalue and two model eigenvalues, all at `0`, coupling `J 0 0 = 1`, `J 0 1 = 0`.
  Row normalization holds on nonempty data (`rnD_rowNorm`), the columns satisfy Bessel, and `K = 0`.
* `rowNormEvWitness`: an `H5bRowNormEvInputs` (G54) with `nA = 1`, `nB = 2` at every `(ε, γ, L)`,
  gap rate `m2 = 1` (vanishing with `L₀ = 1 / η`, G48's `gapRate_vanish`), `Cm = 1`, `Ck = 0`, `τ = 0`,
  `c = 1`, profile `arctanProfile`, `Φ = 2`.
* `rowNormEvWitness_genuine`: `rowNorm` is exercised with `nA = 1 > 0` (not vacuous, unlike G48's
  witness) and the truncations are non-square.
* `rowNormEv_not_rowNorm`: no `H5bRowNormInputs` (G46) has the same true truncation sizes (G48's
  `rowNorm_count_neg_one`), so with G54's `ofRowNorm` the G54 form is strictly weaker.
* `rowNormEvWitness_target`: its smoothed counts satisfy `H5bTarget` (from `h5b_of_rowNormEv`).

What this file does NOT prove: the witness is a test family, not a model of the Steklov spectrum; row
normalization, the gap row and the count, defect, tail and low-count rows are not proved for any
actual coupling or for the Steklov operator of the tetrahedron; that the paper's `E`, `Emod` are the
smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…]
input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5RowNormEvAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5DiffCount SteklovAudit.H5DiffAudit
open SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval SteklovAudit.H5ColCount
open SteklovAudit.H5EventualRows SteklovAudit.H5EventualTarget

/-- One true eigenvalue, two model eigenvalues, all at `0`; `J 0 0 = 1`, `J 0 1 = 0`. -/
def rnD : Data (Fin 1) (Fin 2) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ j => if j.val = 0 then (1 : ℝ) else 0

theorem rnD_rowNorm (i : Fin 1) : ∑ j, rnD.J i j ^ 2 = 1 := by
  first
    | (rw [Fin.sum_univ_two]; simp [rnD])
    | (simp [rnD, Fin.sum_univ_two])
    | (rw [Fin.sum_univ_two]; norm_num [rnD])
    | (rw [Fin.sum_univ_two]
       show (if (0 : Fin 2).val = 0 then (1 : ℝ) else 0) ^ 2 +
         (if (1 : Fin 2).val = 0 then (1 : ℝ) else 0) ^ 2 = 1
       rw [if_pos rfl, if_neg (by decide)]; norm_num)

theorem rnD_colBessel (j : Fin 2) : ∑ i, rnD.J i j ^ 2 ≤ 1 := by
  rw [Fin.sum_univ_one]
  show (if j.val = 0 then (1 : ℝ) else 0) ^ 2 ≤ 1
  split_ifs <;> norm_num

theorem rnD_K (i : Fin 1) (j : Fin 2) : rnD.K i j = 0 := by
  first | simp [Data.K, rnD] | (unfold Data.K; norm_num [rnD])

theorem rnD_hs2K : hs2 rnD.K = 0 := by
  first | simp [hs2, rnD_K] | (unfold hs2; simp [rnD_K])

theorem rnD_defect (L : ℝ) : hs2 rnD.K ≤ (0 : ℝ) ^ 2 * (1 + L) ^ 2 := by
  rw [rnD_hs2K]
  norm_num

theorem rnD_tail (M : ℝ) : hs2 (mask (hiE rnD M) rnD.K) ≤ 0 :=
  (hs2_mask_le _ _).trans rnD_hs2K.le

theorem rnD_lowCount (M : ℝ) :
    ((Finset.univ.filter fun i => rnD.a i ≤ M).card : ℝ) ≤ 1 := by
  have h1 : (Finset.univ.filter fun i => rnD.a i ≤ M).card ≤
      (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
  have h3 : (Finset.univ.filter fun i => rnD.a i ≤ M).card ≤ 1 := by omega
  exact_mod_cast h3

/-- **G55.** A G54 input set with genuine row normalization (`nA = 1`) and `nB = 2`. -/
noncomputable def rowNormEvWitness : SteklovAudit.H5RowNormEv.H5bRowNormEvInputs where
  nA := fun _ _ _ => 1
  nB := fun _ _ _ => 2
  D := fun _ _ _ => rnD
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  rowNorm := fun _ _ _ _ i => rnD_rowNorm i
  colBessel := fun _ _ _ _ j => rnD_colBessel j
  m2 := fun _ _ _ => 1
  cardGap := fun _ _ _ _ => show ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) ≤ 1 by norm_num
  m2Vanish := SteklovAudit.H5RowNormWitness.gapRate_vanish
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  count := fun _ _ L h => SteklovAudit.H5EventualAudit.evOneD_count L h
  defect := fun _ _ L _ => rnD_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ _ => rnD_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ _ => rnD_lowCount M

/-- **G55.** Row normalization is exercised on a nonempty true truncation, and the truncations are
non-square, at every `(ε, γ, L)` with `1 ≤ L`. -/
theorem rowNormEvWitness_genuine :
    (∀ ε γ L, 0 < rowNormEvWitness.nA ε γ L) ∧
    (∀ ε γ L, rowNormEvWitness.nA ε γ L < rowNormEvWitness.nB ε γ L) ∧
    (∀ ε γ L, 1 ≤ L → ∀ i, ∑ j, (rowNormEvWitness.D ε γ L).J i j ^ 2 = 1) :=
  ⟨fun _ _ _ => by first | exact Nat.one_pos | simp [rowNormEvWitness],
   fun _ _ _ => by first | exact (show (1 : ℕ) < 2 by norm_num) | simp [rowNormEvWitness],
   rowNormEvWitness.rowNorm⟩

/-- **G55.** Strictness: no G46 input set has the witness's true truncation sizes. -/
theorem rowNormEv_not_rowNorm :
    ¬ ∃ V : H5bRowNormInputs, V.nA = rowNormEvWitness.nA := by
  rintro ⟨V, hV⟩
  have h0 := SteklovAudit.H5RowNormWitness.rowNorm_count_neg_one V 0 0
  have h1 : rowNormEvWitness.nA 0 0 (-1) = 1 := by first | rfl | simp [rowNormEvWitness]
  have h2 : rowNormEvWitness.nA 0 0 (-1) = 0 := by rw [← hV]; exact h0
  rw [h1] at h2
  exact absurd h2 one_ne_zero

/-- **G55.** The witness gives (7.29) for its smoothed counts (from `h5b_of_rowNormEv`). -/
theorem rowNormEvWitness_target :
    H5bTarget (fun ε γ L => ∑ i, rowNormEvWitness.P.φ ((rowNormEvWitness.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, rowNormEvWitness.P.φ ((rowNormEvWitness.D ε γ L).b j - L)) :=
  SteklovAudit.H5RowNormEv.h5b_of_rowNormEv rowNormEvWitness

end SteklovAudit.H5RowNormEvAudit
