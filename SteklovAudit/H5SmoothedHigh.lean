import Mathlib
import SteklovAudit.H5DiffHighMass
import SteklovAudit.H5SmoothedIdent

/-!
# G43: the smoothed route with the high-energy missing-mass rows

Roadmap item G43. `H5bSmoothedHigh2Inputs` is `H5bDiffHigh2Inputs` (G38) with the difference row
`diffCount`, its rate `e12` and `e12Vanish` removed and no `E`, `Emod` parameters; equivalently,
`H5bSmoothedInputs` (G40) with the full missing-mass rows replaced by the high-energy rows `hm1`,
`rowMissHigh`, `hm1Vanish`, `hm2`, `colMissHigh`, `hm2Vanish` plus the model low count `cB`,
`modelLowCount`.

* `W.Esm`, `W.Emodsm`: the smoothed counts of the coupled spectra (as in G40).
* `smoothedHigh_diffCount`: the difference row holds for `W.Esm`, `W.Emodsm` with rate `0`.
* `H5bSmoothedHigh2Inputs.toDiffHigh2 : H5bDiffHigh2Inputs W.Esm W.Emodsm` (`e12 = 0`).
* `h5b_of_smoothedHigh2 : H5bTarget W.Esm W.Emodsm` via G38's `h5b_of_diffHigh2`.

F table text: on the smoothed route the current strongest form of H5b is `H5bSmoothedHigh2Inputs`.

What this file does NOT prove: no high-energy missing-mass, low-count, Bessel, count, defect or tail
row is proved for the Steklov operator of the tetrahedron or for any actual coupling; that the
paper's `E`, `Emod` equal these smoothed counts is not proved; no Dirichlet-to-Neumann operator is
constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5SmoothedHigh

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass SteklovAudit.H5DiffHighMass

/-- **G43.** The E-free rows of `H5bDiffHigh2Inputs` (high-energy missing mass, no difference row). -/
structure H5bSmoothedHigh2Inputs where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  P : ProfileLipRows
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  hm1 : ℝ → ℝ → ℝ → ℝ → ℝ
  rowMissHigh : ∀ ε γ M L : ℝ,
    ∑ i ∈ Finset.univ.filter fun i => M < (D ε γ L).a i,
      (1 - ∑ j, (D ε γ L).J i j ^ 2) ≤ hm1 ε γ M L
  hm1Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm1 ε γ M L ≤ η * L
  hm2 : ℝ → ℝ → ℝ → ℝ → ℝ
  colMissHigh : ∀ ε γ M L : ℝ,
    ∑ j ∈ Finset.univ.filter fun j => M < (D ε γ L).b j,
      (1 - ∑ i, (D ε γ L).J i j ^ 2) ≤ hm2 ε γ M L
  hm2Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → hm2 ε γ M L ≤ η * L
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
  cB : ℝ → ℝ → ℝ → ℝ
  modelLowCount : ∀ ε γ M L : ℝ,
    ((Finset.univ.filter fun j => (D ε γ L).b j ≤ M).card : ℝ) ≤ cB ε γ M

/-- Smoothed count of the true spectrum. -/
noncomputable def H5bSmoothedHigh2Inputs.Esm (W : H5bSmoothedHigh2Inputs) (ε γ L : ℝ) : ℝ :=
  ∑ i, W.P.φ ((W.D ε γ L).a i - L)

/-- Smoothed count of the model spectrum. -/
noncomputable def H5bSmoothedHigh2Inputs.Emodsm (W : H5bSmoothedHigh2Inputs) (ε γ L : ℝ) : ℝ :=
  ∑ j, W.P.φ ((W.D ε γ L).b j - L)

/-- **G43.** The difference row holds for the smoothed counts with rate `0`. -/
theorem smoothedHigh_diffCount (W : H5bSmoothedHigh2Inputs) (ε γ L : ℝ) :
    |(W.Esm ε γ L - W.Emodsm ε γ L) -
      (∑ i, W.P.φ ((W.D ε γ L).a i - L) - ∑ j, W.P.φ ((W.D ε γ L).b j - L))| ≤ 0 := by
  unfold H5bSmoothedHigh2Inputs.Esm H5bSmoothedHigh2Inputs.Emodsm
  simp

/-- **G43.** The smoothed high-mass data give G38's inputs for the smoothed counts, `e12 = 0`. -/
noncomputable def H5bSmoothedHigh2Inputs.toDiffHigh2 (W : H5bSmoothedHigh2Inputs) :
    H5bDiffHigh2Inputs W.Esm W.Emodsm where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  e12 := fun _ _ _ => 0
  diffCount := fun ε γ L => smoothedHigh_diffCount W ε γ L
  e12Vanish := fun _ _ _ _ η hη => ⟨0, fun L hL => by
    show (0 : ℝ) ≤ η * L
    exact mul_nonneg hη.le hL⟩
  hm1 := W.hm1
  rowMissHigh := W.rowMissHigh
  hm1Vanish := W.hm1Vanish
  hm2 := W.hm2
  colMissHigh := W.colMissHigh
  hm2Vanish := W.hm2Vanish
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
  cB := W.cB
  modelLowCount := W.modelLowCount

/-- **G43.** The smoothed-route high-mass rows give (7.29) for the smoothed counts. -/
theorem h5b_of_smoothedHigh2 (W : H5bSmoothedHigh2Inputs) : H5bTarget W.Esm W.Emodsm :=
  h5b_of_diffHigh2 W.toDiffHigh2

end SteklovAudit.H5SmoothedHigh
