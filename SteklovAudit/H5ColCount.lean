import Mathlib
import SteklovAudit.H5Parseval

/-!
# G46: one-sided normalization and the truncation-size gap row

Roadmap item G46. G44 replaced both missing-mass rows of `H5bSmoothedInputs` (G40) by exact row and
column normalization of the coupling, but `card_eq_of_norms` shows that forces square truncations.
Here normalization is kept on the row side only.

* `colMass_eq_of_rowNorm`: under row normalization the column missing mass equals
  `card κ - card ι` exactly; `rowMass_eq_of_colNorm` is the mirror statement.
* `H5bRowNormInputs`: `H5bNormInputs` with `colNorm` replaced by `colBessel`, a rate `m2`, the gap row
  `cardGap : nB - nA ≤ m2` and `m2Vanish`; `smoothedOfRowNorm` gives the G40 structure and
  `h5b_of_rowNorm` gives (7.29) for the smoothed counts.

What this file does NOT prove: the gap row `cardGap` is a statement about truncation sizes only and
is not proved for any actual pair of truncations; row normalization (completeness of the model basis
for each true eigenvector) is not proved for any actual coupling; no count, defect, tail or low-count
row is proved for the Steklov operator of the tetrahedron; that the paper's `E`, `Emod` equal the
smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…]
input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5ColCount

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval

section Mass

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G46.** Under row normalization the column missing mass is exactly `card κ - card ι`. -/
theorem colMass_eq_of_rowNorm (D : Data ι κ) (rowNorm : ∀ i, ∑ j, D.J i j ^ 2 = 1) :
    ∑ j, (1 - ∑ i, D.J i j ^ 2) = (Fintype.card κ : ℝ) - Fintype.card ι := by
  have h1 : ∑ i, ∑ j, D.J i j ^ 2 = (Fintype.card ι : ℝ) := by
    first
      | simp [rowNorm]
      | (rw [Finset.sum_congr rfl (fun i _ => rowNorm i)]; simp)
  have h2 : ∑ j, ∑ i, D.J i j ^ 2 = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_comm]
    exact h1
  rw [Finset.sum_sub_distrib, h2]
  first
    | simp
    | (rw [Finset.sum_const, Finset.card_univ]; simp)

/-- **G46.** Under column normalization the row missing mass is exactly `card ι - card κ`. -/
theorem rowMass_eq_of_colNorm (D : Data ι κ) (colNorm : ∀ j, ∑ i, D.J i j ^ 2 = 1) :
    ∑ i, (1 - ∑ j, D.J i j ^ 2) = (Fintype.card ι : ℝ) - Fintype.card κ := by
  have h1 : ∑ j, ∑ i, D.J i j ^ 2 = (Fintype.card κ : ℝ) := by
    first
      | simp [colNorm]
      | (rw [Finset.sum_congr rfl (fun j _ => colNorm j)]; simp)
  have h2 : ∑ i, ∑ j, D.J i j ^ 2 = (Fintype.card κ : ℝ) := by
    rw [Finset.sum_comm]
    exact h1
  rw [Finset.sum_sub_distrib, h2]
  first
    | simp
    | (rw [Finset.sum_const, Finset.card_univ]; simp)

end Mass

/-- **G46.** `H5bNormInputs` with column normalization replaced by the column Bessel row and an
`o(L)` gap between the truncation sizes (named hypotheses `colBessel`, `cardGap`, `m2Vanish`). -/
structure H5bRowNormInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  rowNorm : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 = 1
  colBessel : ∀ ε γ L j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  m2 : ℝ → ℝ → ℝ → ℝ
  cardGap : ∀ ε γ L : ℝ, (nB ε γ L : ℝ) - nA ε γ L ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
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

/-- **G46.** The column missing-mass row of `W`, from row normalization and the gap row. -/
theorem rowNorm_colMiss (W : H5bRowNormInputs) (ε γ L : ℝ) :
    ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2) ≤ W.m2 ε γ L := by
  rw [colMass_eq_of_rowNorm (W.D ε γ L) (W.rowNorm ε γ L)]
  first
    | (simp only [Fintype.card_fin]; exact W.cardGap ε γ L)
    | simpa using W.cardGap ε γ L

/-- **G46.** One-sided normalization plus the gap row give the G40 inputs (`m1 = 0`). -/
noncomputable def smoothedOfRowNorm (W : H5bRowNormInputs) : H5bSmoothedInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := fun _ _ _ => 0
  rowMiss := fun ε γ L => rowMiss_of_rowNorm (W.D ε γ L) (W.rowNorm ε γ L)
  m1Vanish := zero_vanish
  m2 := W.m2
  colMiss := rowNorm_colMiss W
  m2Vanish := W.m2Vanish
  colBessel := W.colBessel
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := fun ε γ L i => (W.rowNorm ε γ L i).le
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

/-- **G46.** Row normalization, the gap row and the other E-free rows give (7.29) for the smoothed
counts. -/
theorem h5b_of_rowNorm (W : H5bRowNormInputs) :
    H5bTarget (smoothedOfRowNorm W).Esm (smoothedOfRowNorm W).Emodsm :=
  h5b_of_smoothed (smoothedOfRowNorm W)

end SteklovAudit.H5ColCount
