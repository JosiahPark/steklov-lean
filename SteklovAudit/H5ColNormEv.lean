import Mathlib
import SteklovAudit.H5EventualTarget
import SteklovAudit.H5ColNorm

/-!
# G56: one-sided column normalization with every row required only for `1 ≤ L`

Roadmap item G56 (mirror of G54 for G49). `H5bColNormEvInputs` is `H5bColNormInputs` (G49) with
every row (`colNorm`, `bessel`, `rowGap`, `count`, `defect`, `tail`, `ha`, `hb`, `lowCount`) guarded
by `1 ≤ L →`; the rates and their vanishing conditions are unchanged.

* `ofColNorm`: the old form implies the new one (forget the guards);
* `toSmoothedEv`: the G51 inputs, with `m2 = 0` (column normalization), `colBessel` from `colNorm`,
  and the row missing mass from `rowMass_eq_of_colNorm` and the gap row (`colNormEv_rowMiss`);
* `h5b_of_colNormEv`: `H5bTarget` for the original smoothed counts, via `h5b_of_smoothedEv` (G52).

F table text: on the smoothed route with one-sided completeness, normalization and the gap row need
only hold for `L ≥ 1`.

What this file does NOT prove: column normalization (completeness of the true basis for each model
eigenvector) and the gap row `rowGap` are not proved for any actual coupling or pair of
truncations; no count, defect, tail or low-count row is proved for the Steklov operator of the
tetrahedron; that the paper's `E`, `Emod` equal the smoothed counts is not proved; no
Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1
remain conditional on named inputs.
-/

namespace SteklovAudit.H5ColNormEv

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WindowProfile SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval
open SteklovAudit.H5ColCount SteklovAudit.H5ColNorm SteklovAudit.H5EventualRows
open SteklovAudit.H5EventualTarget

/-- **G56.** `H5bColNormInputs` with every row required only for `1 ≤ L` (named hypotheses). -/
structure H5bColNormEvInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  colNorm : ∀ ε γ L, 1 ≤ L → ∀ j, ∑ i, (D ε γ L).J i j ^ 2 = 1
  bessel : ∀ ε γ L, 1 ≤ L → ∀ i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
  m1 : ℝ → ℝ → ℝ → ℝ
  rowGap : ∀ ε γ L : ℝ, 1 ≤ L → (nA ε γ L : ℝ) - nB ε γ L ≤ m1 ε γ L
  m1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m1 ε γ L ≤ η * L
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

/-- **G56.** The old form implies the new one (forget the guards). -/
noncomputable def ofColNorm (V : H5bColNormInputs) : H5bColNormEvInputs where
  nA := V.nA
  nB := V.nB
  D := V.D
  P := V.P
  Φ := V.Φ
  hΦ := V.hΦ
  profBound := V.profBound
  colNorm := fun ε γ L _ => V.colNorm ε γ L
  bessel := fun ε γ L _ => V.bessel ε γ L
  m1 := V.m1
  rowGap := fun ε γ L _ => V.rowGap ε γ L
  m1Vanish := V.m1Vanish
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

variable (W : H5bColNormEvInputs)

/-- **G56.** For `1 ≤ L`, the row missing mass from column normalization and the gap row. -/
theorem colNormEv_rowMiss (ε γ L : ℝ) (h : 1 ≤ L) :
    ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2) ≤ W.m1 ε γ L := by
  rw [rowMass_eq_of_colNorm (W.D ε γ L) (W.colNorm ε γ L h)]
  first
    | (simp only [Fintype.card_fin]; exact W.rowGap ε γ L h)
    | simpa using W.rowGap ε γ L h

/-- **G56.** The eventual-row smoothed inputs (G51), with `m2 = 0`. -/
noncomputable def toSmoothedEv : H5bSmoothedEvInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := W.m1
  rowMiss := fun ε γ L h => colNormEv_rowMiss W ε γ L h
  m1Vanish := W.m1Vanish
  m2 := fun _ _ _ => 0
  colMiss := fun ε γ L h => colMiss_of_colNorm (W.D ε γ L) (W.colNorm ε γ L h)
  m2Vanish := zero_vanish
  colBessel := fun ε γ L h j => (W.colNorm ε γ L h j).le
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := W.bessel
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

theorem toSmoothedEv_nB : (toSmoothedEv W).nB = W.nB := rfl

/-- **G56.** Column normalization and the gap row for `L ≥ 1`, with the other rows for `L ≥ 1`,
give (7.29) for the original smoothed counts. -/
theorem h5b_of_colNormEv :
    H5bTarget (fun ε γ L => ∑ i, W.P.φ ((W.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, W.P.φ ((W.D ε γ L).b j - L)) :=
  h5b_of_smoothedEv (toSmoothedEv W)

end SteklovAudit.H5ColNormEv
