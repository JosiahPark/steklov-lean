import Mathlib
import SteklovAudit.H5DiffCount

/-!
# G40: the difference row is free when `E`, `Emod` are the smoothed counts

Roadmap item G40. `H5bSmoothedInputs` is `H5bDiffInputs` (G35) with the difference row `diffCount`,
its rate `e12` and `e12Vanish` removed, and with no `E`, `Emod` parameters. For such data,
`W.Esm ε γ L = ∑ i, W.P.φ ((W.D ε γ L).a i - L)` and `W.Emodsm` (same with `b`) are the smoothed
counts of the coupled spectra.

* `smoothed_diffCount`: the difference row holds for `W.Esm`, `W.Emodsm` with rate `0`.
* `H5bSmoothedInputs.toDiff`: an `H5bDiffInputs W.Esm W.Emodsm` (`e12 = 0`).
* `h5b_of_smoothed`: `H5bTarget W.Esm W.Emodsm`.
* `diffCount_iff_ident`: for any `E`, `Emod`, the difference row with rate `e` is the same statement
  as `|(E - W.Esm) - (Emod - W.Emodsm)| ≤ e`, i.e. it is exactly the identification of the paper's
  counts with the smoothed counts of the coupled spectra, up to `e`.

So if the paper's `E`, `Emod` are the smoothed counts of the same coupled spectra, (7.29) needs only
the E-free rows (missing mass, Bessel, count, defect, tail, low count).

What this file does NOT prove: none of those E-free rows is proved for the Steklov operator of the
tetrahedron or for any actual coupling; that the paper's `E`, `Emod` equal these smoothed counts is
not proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5SmoothedIdent

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5DiffCount

/-- **G40.** The E-free rows of `H5bDiffInputs` (no difference row, no `E`, `Emod`). -/
structure H5bSmoothedInputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  m1 : ℝ → ℝ → ℝ → ℝ
  rowMiss : ∀ ε γ L : ℝ, ∑ i, (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ m1 ε γ L
  m1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m1 ε γ L ≤ η * L
  m2 : ℝ → ℝ → ℝ → ℝ
  colMiss : ∀ ε γ L : ℝ, ∑ j, (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ m2 ε γ L
  m2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    m2 ε γ L ≤ η * L
  colBessel : ∀ ε γ L j, ∑ i, (D ε γ L).J i j ^ 2 ≤ 1
  Cm : ℝ → ℝ → ℝ
  Ck : ℝ → ℝ → ℝ
  hCm : ∀ ε γ, 0 ≤ Cm ε γ
  bessel : ∀ ε γ L i, ∑ j, (D ε γ L).J i j ^ 2 ≤ 1
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

/-- Smoothed count of the true spectrum. -/
noncomputable def H5bSmoothedInputs.Esm (W : H5bSmoothedInputs) (ε γ L : ℝ) : ℝ :=
  ∑ i, W.P.φ ((W.D ε γ L).a i - L)

/-- Smoothed count of the model spectrum. -/
noncomputable def H5bSmoothedInputs.Emodsm (W : H5bSmoothedInputs) (ε γ L : ℝ) : ℝ :=
  ∑ j, W.P.φ ((W.D ε γ L).b j - L)

/-- **G40.** The difference row holds for the smoothed counts with rate `0`. -/
theorem smoothed_diffCount (W : H5bSmoothedInputs) (ε γ L : ℝ) :
    |(W.Esm ε γ L - W.Emodsm ε γ L) -
      (∑ i, W.P.φ ((W.D ε γ L).a i - L) - ∑ j, W.P.φ ((W.D ε γ L).b j - L))| ≤ 0 := by
  unfold H5bSmoothedInputs.Esm H5bSmoothedInputs.Emodsm
  simp

/-- **G40.** The smoothed-count data give the difference-row inputs with `e12 = 0`. -/
noncomputable def H5bSmoothedInputs.toDiff (W : H5bSmoothedInputs) :
    H5bDiffInputs W.Esm W.Emodsm where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  e12 := fun _ _ _ => 0
  diffCount := fun ε γ L => smoothed_diffCount W ε γ L
  e12Vanish := fun _ _ _ _ η hη => ⟨0, fun L hL => by
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le hL⟩
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

/-- **G40.** The E-free rows give (7.29) for the smoothed counts. -/
theorem h5b_of_smoothed (W : H5bSmoothedInputs) : H5bTarget W.Esm W.Emodsm :=
  h5b_of_diff W.toDiff

/-- **G40.** The difference row is exactly the identification of `E`, `Emod` with the smoothed
counts, up to the rate `e`. -/
theorem diffCount_iff_ident (W : H5bSmoothedInputs) (E Emod : ℝ → ℝ → ℝ → ℝ) (e ε γ L : ℝ) :
    |(E ε γ L - Emod ε γ L) -
      (∑ i, W.P.φ ((W.D ε γ L).a i - L) - ∑ j, W.P.φ ((W.D ε γ L).b j - L))| ≤ e ↔
    |(E ε γ L - W.Esm ε γ L) - (Emod ε γ L - W.Emodsm ε γ L)| ≤ e := by
  have h : (E ε γ L - Emod ε γ L) -
      (∑ i, W.P.φ ((W.D ε γ L).a i - L) - ∑ j, W.P.φ ((W.D ε γ L).b j - L)) =
      (E ε γ L - W.Esm ε γ L) - (Emod ε γ L - W.Emodsm ε γ L) := by
    unfold H5bSmoothedInputs.Esm H5bSmoothedInputs.Emodsm
    ring
  rw [h]

end SteklovAudit.H5SmoothedIdent
