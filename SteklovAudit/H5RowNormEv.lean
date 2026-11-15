import Mathlib
import SteklovAudit.H5EventualTarget
import SteklovAudit.H5ColCount

/-!
# G54: one-sided row normalization with every row required only for `1 ≤ L`

Roadmap item G54. `H5bRowNormEvInputs` is `H5bRowNormInputs` (G46) with every row (`rowNorm`,
`colBessel`, `cardGap`, `count`, `defect`, `tail`, `ha`, `hb`, `lowCount`) guarded by `1 ≤ L →`;
the rates and their vanishing conditions are unchanged.

* `ofRowNorm`: the old form implies the new one (forget the guards);
* `toSmoothedEv`: the G51 inputs, with `m1 = 0` (row normalization), `bessel` from `rowNorm`, and
  the column missing mass from `colMass_eq_of_rowNorm` and the gap row (`rowNormEv_colMiss`);
* `h5b_of_rowNormEv`: `H5bTarget` for the original smoothed counts, via `h5b_of_smoothedEv` (G52).

What this file does NOT prove: row normalization (completeness of the model basis for each true
eigenvector) and the gap row `cardGap` are not proved for any actual coupling or pair of
truncations; no count, defect, tail or low-count row is proved for the Steklov operator of the
tetrahedron; that the paper's `E`, `Emod` equal the smoothed counts is not proved; no
Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1
remain conditional on named inputs.
-/

namespace SteklovAudit.H5RowNormEv

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WindowProfile SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval
open SteklovAudit.H5ColCount SteklovAudit.H5EventualRows SteklovAudit.H5EventualTarget

/-- **G54.** `H5bRowNormInputs` with every row required only for `1 ≤ L` (named hypotheses). -/
structure H5bRowNormEvInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  rowNorm : ∀ ε γ L, 1 ≤ L → ∀ i, ∑ j, (D ε γ L).J i j ^ 2 = 1
  colBessel : ∀ ε γ L, 1 ≤ L → ∀ j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  m2 : ℝ → ℝ → ℝ → ℝ
  cardGap : ∀ ε γ L : ℝ, 1 ≤ L → (nB ε γ L : ℝ) - nA ε γ L ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  count : ∀ ε γ L : ℝ, 1 ≤ L → (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * (1 + L) ^ 2
  defect : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * (1 + L) ^ 2
  τ : ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, 1 ≤ L → hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  ha : ∀ ε γ L, 1 ≤ L → ∀ i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L, 1 ≤ L → ∀ j, 0 ≤ (D ε γ L).b j
  c : ℝ → ℝ → ℝ → ℝ
  lowCount : ∀ ε γ M L : ℝ, 1 ≤ L →
    ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M

/-- **G54.** The old form implies the new one (forget the guards). -/
noncomputable def ofRowNorm (V : H5bRowNormInputs) : H5bRowNormEvInputs where
  nA := V.nA
  nB := V.nB
  D := V.D
  P := V.P
  Φ := V.Φ
  hΦ := V.hΦ
  profBound := V.profBound
  rowNorm := fun ε γ L _ => V.rowNorm ε γ L
  colBessel := fun ε γ L _ => V.colBessel ε γ L
  m2 := V.m2
  cardGap := fun ε γ L _ => V.cardGap ε γ L
  m2Vanish := V.m2Vanish
  Cm := V.Cm
  Ck := V.Ck
  hCm := V.hCm
  count := fun ε γ L _ => V.count ε γ L
  defect := fun ε γ L _ => V.defect ε γ L
  τ := V.τ
  tail := fun ε γ M L _ => V.tail ε γ M L
  Cτ := V.Cτ
  tailRate := V.tailRate
  ha := fun ε γ L _ => V.ha ε γ L
  hb := fun ε γ L _ => V.hb ε γ L
  c := V.c
  lowCount := fun ε γ M L _ => V.lowCount ε γ M L

variable (W : H5bRowNormEvInputs)

/-- **G54.** For `1 ≤ L`, the column missing mass from row normalization and the gap row. -/
theorem rowNormEv_colMiss (ε γ L : ℝ) (h : 1 ≤ L) :
    ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2) ≤ W.m2 ε γ L := by
  rw [colMass_eq_of_rowNorm (W.D ε γ L) (W.rowNorm ε γ L h)]
  first
    | (simp only [Fintype.card_fin]; exact W.cardGap ε γ L h)
    | simpa using W.cardGap ε γ L h

/-- **G54.** The eventual-row smoothed inputs (G51), with `m1 = 0`. -/
noncomputable def toSmoothedEv : H5bSmoothedEvInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := fun _ _ _ => 0
  rowMiss := fun ε γ L h => rowMiss_of_rowNorm (W.D ε γ L) (W.rowNorm ε γ L h)
  m1Vanish := zero_vanish
  m2 := W.m2
  colMiss := fun ε γ L h => rowNormEv_colMiss W ε γ L h
  m2Vanish := W.m2Vanish
  colBessel := W.colBessel
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := fun ε γ L h i => (W.rowNorm ε γ L h i).le
  count := W.count
  defect := W.defect
  τ := W.τ
  tail := W.tail
  Cτ := W.Cτ
  tailRate := W.tailRate
  ha := W.ha
  hb := W.hb
  c := W.c
  lowCount := W.lowCount

theorem toSmoothedEv_nA : (toSmoothedEv W).nA = W.nA := rfl

/-- **G54.** Row normalization and the gap row for `L ≥ 1`, with the other rows for `L ≥ 1`, give
(7.29) for the original smoothed counts. -/
theorem h5b_of_rowNormEv :
    H5bTarget (fun ε γ L => ∑ i, W.P.φ ((W.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, W.P.φ ((W.D ε γ L).b j - L)) :=
  h5b_of_smoothedEv (toSmoothedEv W)

end SteklovAudit.H5RowNormEv
