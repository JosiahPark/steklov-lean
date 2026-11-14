import Mathlib
import SteklovAudit.H5SmoothedIdent

/-!
# G44: the missing-mass rows from row/column normalization of the coupling

Roadmap item G44. In spectral coordinates the missing-mass rows of `H5bSmoothedInputs` (G40) say that
the total defect `∑ i, (1 - ∑ j, J i j ^ 2)` (and its column analogue) is `o(L)`. Here they are
reduced to exact normalization of the coupling.

* `rowMiss_of_rowNorm`: if every row of `J` has squared norm `1` (named hypothesis `rowNorm`), the row
  missing mass is `≤ 0`; `colMiss_of_colNorm` likewise for columns.
* `zero_vanish`: the constant-zero rate meets the `o(L)` condition of `m1Vanish` / `m2Vanish`.
* `card_eq_of_norms`: row and column normalization together force equal truncation sizes
  (`card ι = card κ`), so this reduction only applies to square truncations.
* `H5bNormInputs`: `H5bSmoothedInputs` with `m1`, `rowMiss`, `m1Vanish`, `m2`, `colMiss`, `m2Vanish`,
  `bessel`, `colBessel` replaced by `rowNorm`, `colNorm`; `smoothedOfNorm` gives the G40 structure and
  `h5b_of_norm` gives (7.29) for the smoothed counts.

F table text: the missing-mass rows may be replaced by exact row/column normalization of the coupling
plus the other E-free rows. This is a reduction, not a proof of normalization.

What this file does NOT prove: normalization (completeness of the model basis for the true
eigenvectors, or conversely) is not proved for any actual coupling; no count, defect, tail or low-count
row is proved for the Steklov operator of the tetrahedron; that the paper's `E`, `Emod` equal the
smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…]
input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5Parseval

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5SmoothedIdent

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G44.** Row normalization makes the row missing mass vanish. -/
theorem rowMiss_of_rowNorm (D : Data ι κ) (rowNorm : ∀ i, ∑ j, D.J i j ^ 2 = 1) :
    ∑ i, (1 - ∑ j, D.J i j ^ 2) ≤ 0 := by
  have h : ∑ i, (1 - ∑ j, D.J i j ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => by simp [rowNorm i])
  exact h.le

/-- **G44.** Column normalization makes the column missing mass vanish. -/
theorem colMiss_of_colNorm (D : Data ι κ) (colNorm : ∀ j, ∑ i, D.J i j ^ 2 = 1) :
    ∑ j, (1 - ∑ i, D.J i j ^ 2) ≤ 0 := by
  have h : ∑ j, (1 - ∑ i, D.J i j ^ 2) = 0 :=
    Finset.sum_eq_zero (fun j _ => by simp [colNorm j])
  exact h.le

/-- **G44.** Row and column normalization together force equal truncation sizes. -/
theorem card_eq_of_norms (D : Data ι κ) (rowNorm : ∀ i, ∑ j, D.J i j ^ 2 = 1)
    (colNorm : ∀ j, ∑ i, D.J i j ^ 2 = 1) :
    (Fintype.card ι : ℝ) = Fintype.card κ := by
  have h1 : ∑ i, ∑ j, D.J i j ^ 2 = (Fintype.card ι : ℝ) := by
    first
      | simp [rowNorm]
      | (rw [Finset.sum_congr rfl (fun i _ => rowNorm i)]; simp)
  have h2 : ∑ j, ∑ i, D.J i j ^ 2 = (Fintype.card κ : ℝ) := by
    first
      | simp [colNorm]
      | (rw [Finset.sum_congr rfl (fun j _ => colNorm j)]; simp)
  rw [← h1, ← h2]
  exact Finset.sum_comm

end Norms

/-- **G44.** The constant-zero rate is `o(L)` in the sense of `m1Vanish` / `m2Vanish`. -/
theorem zero_vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    ((fun _ _ _ => (0 : ℝ)) : ℝ → ℝ → ℝ → ℝ) ε γ L ≤ η * L :=
  fun _ _ _ _ η hη => ⟨0, fun L hL => by
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le hL⟩

/-- **G44.** `H5bSmoothedInputs` with the missing-mass and Bessel rows replaced by exact
row/column normalization of the coupling (named hypotheses `rowNorm`, `colNorm`). -/
structure H5bNormInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  rowNorm : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 = 1
  colNorm : ∀ ε γ L j, ∑ i, (D ε γ L).J i j ^ 2 = 1
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

/-- **G44.** Normalized couplings give the G40 inputs, with zero missing-mass rates. -/
noncomputable def smoothedOfNorm (W : H5bNormInputs) : H5bSmoothedInputs where
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
  m2 := fun _ _ _ => 0
  colMiss := fun ε γ L => colMiss_of_colNorm (W.D ε γ L) (W.colNorm ε γ L)
  m2Vanish := zero_vanish
  colBessel := fun ε γ L j => (W.colNorm ε γ L j).le
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

/-- **G44.** Normalization plus the other E-free rows give (7.29) for the smoothed counts. -/
theorem h5b_of_norm (W : H5bNormInputs) :
    H5bTarget (smoothedOfNorm W).Esm (smoothedOfNorm W).Emodsm :=
  h5b_of_smoothed (smoothedOfNorm W)

/-- **G44.** Under normalization the true and model truncations have the same size. -/
theorem norm_card_eq (W : H5bNormInputs) (ε γ L : ℝ) : W.nA ε γ L = W.nB ε γ L := by
  have h := card_eq_of_norms (W.D ε γ L) (W.rowNorm ε γ L) (W.colNorm ε γ L)
  simp only [Fintype.card_fin] at h
  exact_mod_cast h

end SteklovAudit.H5Parseval
