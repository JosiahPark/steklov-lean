import Mathlib
import SteklovAudit.H5EvPaperScale

/-!
# G59: the paper's `C · L²` form of the count and defect rows is an exact restatement

Roadmap item G59, the converse of G58. `ofSmoothedEv` turns G51's inputs (`count`, `defect` with
`(1 + L) ^ 2`) into G58's inputs (`count`, `defect` with `L ^ 2`), changing only the constants:
`Cm' = 4 · Cm` and `Ck' = 2 · Ck`, using `(1 + L) ^ 2 ≤ 4 · L ^ 2` for `1 ≤ L`. Together with G58's
`toSmoothedEv`, this says: the count and defect rows of the smoothed route may be stated in the
paper's `C L²` form for `L ≥ 1`; the two forms are equivalent (constants change by 4 and 2).

* `one_add_sq_le_four_sq`: `(1 + L) ^ 2 ≤ 4 · L ^ 2` for `1 ≤ L`;
* `smoothedEv_count_paper`, `smoothedEv_defect_paper`: the G51 rows in the paper form;
* `ofSmoothedEv`, `ofSmoothedEv_nA` (rfl), `ofSmoothedEv_Cm`, `ofSmoothedEv_Ck` (rfl),
  `ofSmoothedEv_target`.

What this file does NOT prove: neither the count row nor the defect row (nor any other row) is
proved for the Steklov operator of the tetrahedron or for any actual coupling; no
Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1
remain conditional on named inputs. It only shows the two ways of writing two rows are
interchangeable.
-/

namespace SteklovAudit.H5EvPaperScaleAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WindowProfile SteklovAudit.H5SmoothedIdent
open SteklovAudit.H5EventualRows SteklovAudit.H5EventualTarget SteklovAudit.H5EvPaperScale

/-- **G59.** `(1 + L) ^ 2 ≤ 4 · L ^ 2` for `1 ≤ L`. -/
theorem one_add_sq_le_four_sq {L : ℝ} (h : 1 ≤ L) : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 3 * L + 1)]

variable (V : H5bSmoothedEvInputs)

/-- **G59.** G51's count row in the paper's form, with constant `4 · Cm`. -/
theorem smoothedEv_count_paper (ε γ L : ℝ) (h : 1 ≤ L) :
    (Fintype.card (Fin (V.nA ε γ L)) : ℝ) ≤ (4 * V.Cm ε γ) * L ^ 2 := by
  calc (Fintype.card (Fin (V.nA ε γ L)) : ℝ) ≤ V.Cm ε γ * (1 + L) ^ 2 := V.count ε γ L h
    _ ≤ V.Cm ε γ * (4 * L ^ 2) :=
        mul_le_mul_of_nonneg_left (one_add_sq_le_four_sq h) (V.hCm ε γ)
    _ = (4 * V.Cm ε γ) * L ^ 2 := by ring

/-- **G59.** G51's defect row in the paper's form, with constant `2 · Ck`. -/
theorem smoothedEv_defect_paper (ε γ L : ℝ) (h : 1 ≤ L) :
    hs2 (V.D ε γ L).K ≤ (2 * V.Ck ε γ) ^ 2 * L ^ 2 := by
  calc hs2 (V.D ε γ L).K ≤ V.Ck ε γ ^ 2 * (1 + L) ^ 2 := V.defect ε γ L h
    _ ≤ V.Ck ε γ ^ 2 * (4 * L ^ 2) :=
        mul_le_mul_of_nonneg_left (one_add_sq_le_four_sq h) (sq_nonneg _)
    _ = (2 * V.Ck ε γ) ^ 2 * L ^ 2 := by ring

/-- **G59.** G51's inputs give G58's inputs (`Cm' = 4 · Cm`, `Ck' = 2 · Ck`). -/
noncomputable def ofSmoothedEv : H5bPaperScaleInputs where
  nA := V.nA
  nB := V.nB
  D := V.D
  P := V.P
  Φ := V.Φ
  hΦ := V.hΦ
  profBound := V.profBound
  m1 := V.m1
  rowMiss := V.rowMiss
  m1Vanish := V.m1Vanish
  m2 := V.m2
  colMiss := V.colMiss
  m2Vanish := V.m2Vanish
  colBessel := V.colBessel
  Cm := fun ε γ => 4 * V.Cm ε γ
  Ck := fun ε γ => 2 * V.Ck ε γ
  hCm := fun ε γ => mul_nonneg (by norm_num) (V.hCm ε γ)
  bessel := V.bessel
  count := smoothedEv_count_paper V
  defect := smoothedEv_defect_paper V
  τ := V.τ
  tail := V.tail
  Cτ := V.Cτ
  tailRate := V.tailRate
  ha := V.ha
  hb := V.hb
  c := V.c
  lowCount := V.lowCount

theorem ofSmoothedEv_nA : (ofSmoothedEv V).nA = V.nA := rfl

theorem ofSmoothedEv_Cm (ε γ : ℝ) : (ofSmoothedEv V).Cm ε γ = 4 * V.Cm ε γ := rfl

theorem ofSmoothedEv_Ck (ε γ : ℝ) : (ofSmoothedEv V).Ck ε γ = 2 * V.Ck ε γ := rfl

/-- **G59.** Round trip: G51 → G58 → (7.29) for the same smoothed counts. -/
theorem ofSmoothedEv_target :
    H5bTarget (fun ε γ L => ∑ i, V.P.φ ((V.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, V.P.φ ((V.D ε γ L).b j - L)) :=
  h5b_of_paperScale (ofSmoothedEv V)

end SteklovAudit.H5EvPaperScaleAudit
