import Mathlib
import SteklovAudit.H5ColCount
import SteklovAudit.H5SmoothedColAudit

/-!
# G47: under row normalization the gap row is the column missing-mass row, no more and no less

Roadmap item G47. G46 (`H5ColCount.lean`) replaced the column missing-mass row of the smoothed route
by row normalization plus a truncation-size gap row `cardGap : nB - nA ≤ m2`. This file checks that
replacement is exact and no stronger than G44.

* `colMiss_iff_cardGap`: under row normalization, for every `m`, column missing mass `≤ m` iff
  `card κ - card ι ≤ m`.
* `smCol_cardGap`: the G45 family `smColD L` is row-normalized (vacuously, `Fin 0`) and its gap is
  `⌈L⌉₊`, equal to its column missing mass (`smCol_colMass`).
* `rowNormOfNorm`: every `H5bNormInputs` (G44) gives an `H5bRowNormInputs` with `m2 = 0`, the gap
  row coming from `norm_card_eq`; so G46's inputs are no stronger than G44's
  (`rowNormOfNorm_target`).

What this file does NOT prove: the gap row, row normalization, and the count, defect, tail and
low-count rows are not proved for the Steklov operator of the tetrahedron or for any actual
coupling; `smColD` is a test family, not a model of the spectrum; that the paper's `E`, `Emod`
equal the smoothed counts is not proved; no Dirichlet-to-Neumann operator is constructed; (7.29),
every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5ColCountAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5SmoothedIdent SteklovAudit.H5Parseval
open SteklovAudit.H5ColCount SteklovAudit.H5SmoothedColAudit

/-- **G47.** Under row normalization the column missing-mass row with rate `m` is exactly the gap
row `card κ - card ι ≤ m`. -/
theorem colMiss_iff_cardGap {ι κ : Type*} [Fintype ι] [Fintype κ] (D : Data ι κ)
    (rowNorm : ∀ i, ∑ j, D.J i j ^ 2 = 1) (m : ℝ) :
    ∑ j, (1 - ∑ i, D.J i j ^ 2) ≤ m ↔ (Fintype.card κ : ℝ) - Fintype.card ι ≤ m := by
  rw [colMass_eq_of_rowNorm D rowNorm]

/-- **G47.** The G45 family is row-normalized (vacuously) and its truncation-size gap is `⌈L⌉₊`,
equal to its column missing mass. -/
theorem smCol_cardGap (L : ℝ) :
    (∀ i, ∑ j, (smColD L).J i j ^ 2 = 1) ∧
    ((Fintype.card (Fin ⌈L⌉₊) : ℝ) - Fintype.card (Fin 0) = (⌈L⌉₊ : ℝ)) ∧
    ((Fintype.card (Fin ⌈L⌉₊) : ℝ) - Fintype.card (Fin 0) =
      ∑ j, (1 - ∑ i, (smColD L).J i j ^ 2)) := by
  refine ⟨fun i => absurd i.isLt (Nat.not_lt_zero _), ?_, ?_⟩
  · simp
  · rw [smCol_colMass]
    simp

/-- **G47.** Two-sided normalization (G44) gives one-sided normalization with a zero gap rate. -/
noncomputable def rowNormOfNorm (W : H5bNormInputs) : H5bRowNormInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  rowNorm := W.rowNorm
  colBessel := fun ε γ L j => (W.colNorm ε γ L j).le
  m2 := fun _ _ _ => 0
  cardGap := fun ε γ L => by
    show (W.nB ε γ L : ℝ) - W.nA ε γ L ≤ 0
    simp [norm_card_eq W ε γ L]
  m2Vanish := zero_vanish
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
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

/-- **G47.** The gap rate of `rowNormOfNorm W` is zero. -/
theorem rowNormOfNorm_m2 (W : H5bNormInputs) (ε γ L : ℝ) : (rowNormOfNorm W).m2 ε γ L = 0 := rfl

/-- **G47.** G44's inputs reach (7.29) through G46 as well, so G46 is no stronger than G44. -/
theorem rowNormOfNorm_target (W : H5bNormInputs) :
    H5bTarget (smoothedOfRowNorm (rowNormOfNorm W)).Esm
      (smoothedOfRowNorm (rowNormOfNorm W)).Emodsm :=
  h5b_of_rowNorm (rowNormOfNorm W)

end SteklovAudit.H5ColCountAudit
