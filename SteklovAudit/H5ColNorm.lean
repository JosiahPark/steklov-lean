import Mathlib
import SteklovAudit.H5ColCount

/-!
# G49: column normalization and the truncation-size gap row (mirror of G46)

Roadmap item G49. G46 (`H5ColCount.lean`) kept normalization on the row side and replaced the
column missing-mass row by a gap row `nB - nA ≤ m2`. Here the roles are swapped: column
normalization is kept, and the row missing-mass row of `H5bSmoothedInputs` (G40) is replaced by
the gap row `rowGap : nA - nB ≤ m1` with an `o(L)` rate `m1Vanish`.

* `H5bColNormInputs`: `H5bNormInputs` with `rowNorm` replaced by the row Bessel row `bessel`, a
  rate `m1`, the gap row `rowGap` and `m1Vanish`.
* `colNorm_rowMiss`: the row missing-mass row, from `rowMass_eq_of_colNorm` and `rowGap`.
* `smoothedOfColNorm` gives the G40 structure (`m2 = 0`) and `h5b_of_colNorm` gives (7.29) for the
  smoothed counts.

F table text: on the smoothed route, with completeness on one side, the other missing-mass row may
be replaced by an `o(L)` gap between truncation sizes.

What this file does NOT prove: the gap row `rowGap` is a statement about truncation sizes only and
is not proved for any actual pair of truncations; column normalization (completeness of the true
eigenbasis for each model vector) is not proved for any actual coupling; no count, defect, tail or
low-count row is proved for the Steklov operator of the tetrahedron; that the paper's `E`, `Emod`
equal the smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed; (7.29),
every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5ColNorm

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval
open SteklovAudit.H5ColCount

/-- **G49.** `H5bNormInputs` with row normalization replaced by the row Bessel row and an `o(L)`
gap between the truncation sizes (named hypotheses `bessel`, `rowGap`, `m1Vanish`). -/
structure H5bColNormInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  colNorm : ∀ ε γ L j, ∑ i, (D ε γ L).J i j ^ 2 = 1
  bessel : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
  m1 : ℝ → ℝ → ℝ → ℝ
  rowGap : ∀ ε γ L : ℝ, (nA ε γ L : ℝ) - nB ε γ L ≤ m1 ε γ L
  m1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m1 ε γ L ≤ η * L
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  count : ∀ ε γ L : ℝ, (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * (1 + L) ^ 2
  defect : ∀ ε γ L : ℝ, hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * (1 + L) ^ 2
  τ : ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  ha : ∀ ε γ L i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L j, 0 ≤ (D ε γ L).b j
  c : ℝ → ℝ → ℝ → ℝ
  lowCount : ∀ ε γ M L : ℝ,
    ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M

/-- **G49.** The row missing-mass row of `W`, from column normalization and the gap row. -/
theorem colNorm_rowMiss (W : H5bColNormInputs) (ε γ L : ℝ) :
    ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2) ≤ W.m1 ε γ L := by
  rw [rowMass_eq_of_colNorm (W.D ε γ L) (W.colNorm ε γ L)]
  first
    | (simp only [Fintype.card_fin]; exact W.rowGap ε γ L)
    | simpa using W.rowGap ε γ L

/-- **G49.** One-sided (column) normalization plus the gap row give the G40 inputs (`m2 = 0`). -/
noncomputable def smoothedOfColNorm (W : H5bColNormInputs) : H5bSmoothedInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := W.m1
  rowMiss := colNorm_rowMiss W
  m1Vanish := W.m1Vanish
  m2 := fun _ _ _ => 0
  colMiss := fun ε γ L => colMiss_of_colNorm (W.D ε γ L) (W.colNorm ε γ L)
  m2Vanish := zero_vanish
  colBessel := fun ε γ L j => (W.colNorm ε γ L j).le
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

/-- **G49.** Column normalization, the gap row and the other E-free rows give (7.29) for the
smoothed counts. -/
theorem h5b_of_colNorm (W : H5bColNormInputs) :
    H5bTarget (smoothedOfColNorm W).Esm (smoothedOfColNorm W).Emodsm :=
  h5b_of_smoothed (smoothedOfColNorm W)

/-- **G49.** The smoothed structure built here has zero column rate, as intended. -/
theorem smoothedOfColNorm_m2 (W : H5bColNormInputs) (ε γ L : ℝ) :
    (smoothedOfColNorm W).m2 ε γ L = 0 := rfl

end SteklovAudit.H5ColNorm
