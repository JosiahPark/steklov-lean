import Mathlib
import SteklovAudit.H5EventualTarget

/-!
# G58: the count and defect rows of the smoothed route in the paper's `C · L²` form

Roadmap item G58. `H5bPaperScaleInputs` is `H5bSmoothedEvInputs` (G51) with the `count` and `defect`
rows stated as `card ≤ Cm · L²` and `hs2 K ≤ Ck² · L²` for `1 ≤ L` (the form of the Weyl count and
of Lemma 7.1′ in the paper), instead of with `(1 + L) ^ 2`. All other rows and rates are unchanged.

* `sq_le_one_add_sq`: `L ^ 2 ≤ (1 + L) ^ 2` for `1 ≤ L`;
* `paperScale_count`, `paperScale_defect`: the paper-scale rows give the G51 rows;
* `toSmoothedEv`: the G51 inputs; `h5b_of_paperScale`: `H5bTarget` for the original smoothed
  counts, via `h5b_of_smoothedEv` (G52).

What this file does NOT prove: neither the count row nor the defect row (nor any other row:
tail, low count, missing mass, Bessel) is proved for the Steklov operator of the tetrahedron or
for any actual coupling; that the paper's `E`, `Emod` are these smoothed counts is not proved; no
Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1
remain conditional on named inputs.
-/

namespace SteklovAudit.H5EvPaperScale

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WindowProfile SteklovAudit.H5SmoothedIdent
open SteklovAudit.H5EventualRows SteklovAudit.H5EventualTarget

/-- **G58.** G51's inputs with the count and defect rows in the paper's `C · L²` form. -/
structure H5bPaperScaleInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  m1 : ℝ → ℝ → ℝ → ℝ
  rowMiss : ∀ ε γ L : ℝ, 1 ≤ L → ∑ i, (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ m1 ε γ L
  m1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m1 ε γ L ≤ η * L
  m2 : ℝ → ℝ → ℝ → ℝ
  colMiss : ∀ ε γ L : ℝ, 1 ≤ L → ∑ j, (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
  colBessel : ∀ ε γ L, 1 ≤ L → ∀ j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  bessel : ∀ ε γ L, 1 ≤ L → ∀ i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
  count : ∀ ε γ L : ℝ, 1 ≤ L → (Fintype.card (Fin (nA ε γ L)) : ℝ) ≤ Cm ε γ * L ^ 2
  defect : ∀ ε γ L : ℝ, 1 ≤ L → hs2 (D ε γ L).K ≤ Ck ε γ ^ 2 * L ^ 2
  τ : ℝ → ℝ → ℝ → ℝ
  tail : ∀ ε γ M L : ℝ, 1 ≤ L → hs2 (mask (hiE (D ε γ L) M) (D ε γ L).K) ≤ τ ε γ M
  Cτ : ℝ → ℝ → ℝ
  tailRate : SteklovAudit.H5TailRate.TailRate τ Cτ
  ha : ∀ ε γ L, 1 ≤ L → ∀ i, 0 ≤ (D ε γ L).a i
  hb : ∀ ε γ L, 1 ≤ L → ∀ j, 0 ≤ (D ε γ L).b j
  c : ℝ → ℝ → ℝ → ℝ
  lowCount : ∀ ε γ M L : ℝ, 1 ≤ L →
    ((Finset.univ.filter fun i => (D ε γ L).a i ≤ M).card : ℝ) ≤ c ε γ M

/-- **G58.** `L ^ 2 ≤ (1 + L) ^ 2` for `1 ≤ L`. -/
theorem sq_le_one_add_sq {L : ℝ} (h : 1 ≤ L) : L ^ 2 ≤ (1 + L) ^ 2 := by
  nlinarith [h]

variable (W : H5bPaperScaleInputs)

/-- **G58.** The paper-scale count row gives the G51 count row. -/
theorem paperScale_count (ε γ L : ℝ) (h : 1 ≤ L) :
    (Fintype.card (Fin (W.nA ε γ L)) : ℝ) ≤ W.Cm ε γ * (1 + L) ^ 2 :=
  le_trans (W.count ε γ L h) (mul_le_mul_of_nonneg_left (sq_le_one_add_sq h) (W.hCm ε γ))

/-- **G58.** The paper-scale defect row gives the G51 defect row. -/
theorem paperScale_defect (ε γ L : ℝ) (h : 1 ≤ L) :
    hs2 (W.D ε γ L).K ≤ W.Ck ε γ ^ 2 * (1 + L) ^ 2 :=
  le_trans (W.defect ε γ L h) (mul_le_mul_of_nonneg_left (sq_le_one_add_sq h) (sq_nonneg _))

/-- **G58.** The G51 inputs. -/
noncomputable def toSmoothedEv : H5bSmoothedEvInputs where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  m1 := W.m1
  rowMiss := W.rowMiss
  m1Vanish := W.m1Vanish
  m2 := W.m2
  colMiss := W.colMiss
  m2Vanish := W.m2Vanish
  colBessel := W.colBessel
  Cm := W.Cm
  Ck := W.Ck
  hCm := W.hCm
  bessel := W.bessel
  count := paperScale_count W
  defect := paperScale_defect W
  τ := W.τ
  tail := W.tail
  Cτ := W.Cτ
  tailRate := W.tailRate
  ha := W.ha
  hb := W.hb
  c := W.c
  lowCount := W.lowCount

theorem toSmoothedEv_nA : (toSmoothedEv W).nA = W.nA := rfl

/-- **G58.** The rows in the paper's `C · L²` form for `L ≥ 1` give (7.29) for the original
smoothed counts. -/
theorem h5b_of_paperScale :
    H5bTarget (fun ε γ L => ∑ i, W.P.φ ((W.D ε γ L).a i - L))
      (fun ε γ L => ∑ j, W.P.φ ((W.D ε γ L).b j - L)) :=
  h5b_of_smoothedEv (toSmoothedEv W)

end SteklovAudit.H5EvPaperScale
