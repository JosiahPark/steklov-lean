import Mathlib
import SteklovAudit.H5CutoffSides
import SteklovAudit.H5Completeness
import SteklovAudit.H5MissingMass

/-!
# G34: the cutoff row from one smoothed-count difference row

Roadmap item G34. Over arbitrary finite index types `ι`, `κ`, with values `f : ι → ℝ`, `g : κ → ℝ`
and a coupling `J : ι → κ → ℝ`:

* `diff_of_counts`: two one-spectrum count bounds `|X1 - S1| ≤ e1`, `|X2 - S2| ≤ e2` give the
  difference bound `|(X1 - X2) - (S1 - S2)| ≤ e1 + e2` (so the pair of count rows implies the single
  difference row).
* `cutoff_of_diff_count`: a single difference row `|X - (∑ f - ∑ g)| ≤ e`, sup bounds `|f|, |g| ≤ Φ`,
  row and column Bessel bounds and missing-mass bounds `m1`, `m2` give the cutoff inequality
  `|X - ∑ i, ∑ j, (f i - g j) * J i j ^ 2| ≤ e + Φ * m1 + Φ * m2`.
* G35: `H5bDiffInputs E Emod` is `H5bMassInputs E Emod` (G26) with the two count rows `trueCount`,
  `modelCount` (and their rates) replaced by ONE row `diffCount` on the difference of the smoothed
  counts. `H5bDiffInputs.toPaper` rebuilds `H5bPaperInputs` (`disc = e12 + Φ * m1 + Φ * m2`),
  `h5b_of_diff` gives `H5bTarget E Emod`, and `H5bMassInputs.toDiff` shows every `H5bMassInputs`
  gives an `H5bDiffInputs` (`e12 = e1 + e2`).

What this file does NOT prove: no count, difference, missing-mass or Bessel row is proved for the
Steklov operator of the tetrahedron or for any actual coupling matrix; no field of `H5bDiffInputs`
is proved for the actual operator; no Dirichlet-to-Neumann operator is constructed; (7.29), every
[H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
The G34 part is pure finite-sum algebra.
-/

namespace SteklovAudit.H5DiffCount

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G34.** Two count bounds give a bound on the difference. -/
theorem diff_of_counts (X1 X2 S1 S2 e1 e2 : ℝ)
    (h1 : |X1 - S1| ≤ e1) (h2 : |X2 - S2| ≤ e2) :
    |(X1 - X2) - (S1 - S2)| ≤ e1 + e2 := by
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- Helper: the completeness defect of a Bessel-weighted sum is at most `Φ * m`. -/
theorem defect_abs_le_mass (f w : ι → ℝ) (Φ m : ℝ) (hΦ : 0 ≤ Φ) (hf : ∀ i, |f i| ≤ Φ)
    (hw : ∀ i, w i ≤ 1) (hm : ∑ i, (1 - w i) ≤ m) :
    |∑ i, f i * (1 - w i)| ≤ Φ * m := by
  have h1 := SteklovAudit.H5Completeness.defect_abs_le f w hw
  have h2 := SteklovAudit.H5Completeness.defect_le_sup f w Φ hf hw
  have h3 : Φ * ∑ i, (1 - w i) ≤ Φ * m := mul_le_mul_of_nonneg_left hm hΦ
  linarith

/-- **G34.** One smoothed-count difference row, sup bounds, Bessel bounds and missing-mass
bounds give the cutoff inequality. -/
theorem cutoff_of_diff_count (f : ι → ℝ) (g : κ → ℝ) (J : ι → κ → ℝ) (X e Φ m1 m2 : ℝ)
    (hdiff : |X - (∑ i, f i - ∑ j, g j)| ≤ e)
    (hf : ∀ i, |f i| ≤ Φ) (hg : ∀ j, |g j| ≤ Φ)
    (hrow : ∀ i, ∑ j, J i j ^ 2 ≤ 1) (hcol : ∀ j, ∑ i, J i j ^ 2 ≤ 1)
    (hm1 : ∑ i, (1 - ∑ j, J i j ^ 2) ≤ m1) (hm2 : ∑ j, (1 - ∑ i, J i j ^ 2) ≤ m2)
    (hΦ : 0 ≤ Φ) :
    |X - ∑ i, ∑ j, (f i - g j) * J i j ^ 2| ≤ e + Φ * m1 + Φ * m2 := by
  have hsplit : ∑ i, ∑ j, (f i - g j) * J i j ^ 2
      = ∑ i, f i * (∑ j, J i j ^ 2) - ∑ j, g j * (∑ i, J i j ^ 2) :=
    SteklovAudit.H5CutoffSides.double_sum_split f g J
  have hwf : ∑ i, f i * (∑ j, J i j ^ 2)
      = ∑ i, f i - ∑ i, f i * (1 - ∑ j, J i j ^ 2) :=
    SteklovAudit.H5Completeness.weighted_sum_split f (fun i => ∑ j, J i j ^ 2)
  have hwg : ∑ j, g j * (∑ i, J i j ^ 2)
      = ∑ j, g j - ∑ j, g j * (1 - ∑ i, J i j ^ 2) :=
    SteklovAudit.H5Completeness.weighted_sum_split g (fun j => ∑ i, J i j ^ 2)
  rw [hsplit, hwf, hwg]
  have hD1 : |∑ i, f i * (1 - ∑ j, J i j ^ 2)| ≤ Φ * m1 :=
    defect_abs_le_mass f (fun i => ∑ j, J i j ^ 2) Φ m1 hΦ hf hrow hm1
  have hD2 : |∑ j, g j * (1 - ∑ i, J i j ^ 2)| ≤ Φ * m2 :=
    defect_abs_le_mass g (fun j => ∑ i, J i j ^ 2) Φ m2 hΦ hg hcol hm2
  obtain ⟨hdl, hdr⟩ := abs_le.mp hdiff
  obtain ⟨h1l, h1r⟩ := abs_le.mp hD1
  obtain ⟨h2l, h2r⟩ := abs_le.mp hD2
  rw [abs_le]
  constructor <;> linarith

/-- Non-vacuity: on `Fin 1 × Fin 1` with `f = 1`, `g = 0`, `J = 0`, `X = 0`, the hypotheses of
`cutoff_of_diff_count` hold with `e = 1`, `Φ = 1`, `m1 = m2 = 1`, and the double sum is `0`. -/
theorem cutoff_of_diff_count_nonvacuous :
    |(0 : ℝ) - (∑ _i : Fin 1, (1 : ℝ) - ∑ _j : Fin 1, (0 : ℝ))| ≤ 1 ∧
    |(0 : ℝ) - ∑ _i : Fin 1, ∑ _j : Fin 1, ((1 : ℝ) - 0) * (0 : ℝ) ^ 2| ≤ 1 + 1 * 1 + 1 * 1 := by
  constructor
  · norm_num [Fin.sum_univ_one]
  · norm_num [Fin.sum_univ_one]

section G35

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5WindowProfile SteklovAudit.H5PaperRows
open SteklovAudit.H5MissingMass

/-- **G35.** The H5b inputs with one smoothed-count difference row in place of the two count rows. -/
structure H5bDiffInputs (E Emod : ℝ → ℝ → ℝ → ℝ) where
  nA : ℝ → ℝ → ℝ → ℕ
  nB : ℝ → ℝ → ℝ → ℕ
  D : ∀ ε γ L : ℝ, Data (Fin (nA ε γ L)) (Fin (nB ε γ L))
  /-- Row: window profile (G7); the test is `F ε γ L x = P.φ (x - L)`. -/
  P : ProfileLipRows
  /-- Row: sup bound on the window profile. -/
  Φ : ℝ
  hΦ : 0 ≤ Φ
  profBound : ∀ x, |P.φ x| ≤ Φ
  e12 : ℝ → ℝ → ℝ → ℝ
  /-- Row: difference of the smoothed counts of the true and model spectra (no `J`). -/
  diffCount : ∀ ε γ L : ℝ, |(E ε γ L - Emod ε γ L) -
    (∑ i, P.φ ((D ε γ L).a i - L) - ∑ j, P.φ ((D ε γ L).b j - L))| ≤ e12 ε γ L
  e12Vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    e12 ε γ L ≤ η * L
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

/-- **G35.** The difference row rebuilds the paper-form inputs of G16. -/
noncomputable def H5bDiffInputs.toPaper {E Emod : ℝ → ℝ → ℝ → ℝ}
    (W : H5bDiffInputs E Emod) : H5bPaperInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  disc := fun ε γ L => W.e12 ε γ L + W.Φ * W.m1 ε γ L + W.Φ * W.m2 ε γ L
  cutoff := fun ε γ L =>
    cutoff_of_diff_count (fun i => W.P.φ ((W.D ε γ L).a i - L))
      (fun j => W.P.φ ((W.D ε γ L).b j - L)) (W.D ε γ L).J (E ε γ L - Emod ε γ L)
      (W.e12 ε γ L) W.Φ (W.m1 ε γ L) (W.m2 ε γ L) (W.diffCount ε γ L)
      (fun i => W.profBound ((W.D ε γ L).a i - L))
      (fun j => W.profBound ((W.D ε γ L).b j - L)) (W.bessel ε γ L) (W.colBessel ε γ L)
      (W.rowMiss ε γ L) (W.colMiss ε γ L) W.hΦ
  discVanish :=
    SteklovAudit.H5CutoffSides.discVanish_of_sides
      (fun ε γ L => W.e12 ε γ L + W.Φ * W.m1 ε γ L) (fun ε γ L => W.Φ * W.m2 ε γ L)
      (SteklovAudit.H5CutoffSides.discVanish_of_sides W.e12 (fun ε γ L => W.Φ * W.m1 ε γ L)
        W.e12Vanish (vanish_const_mul W.m1 W.Φ W.hΦ W.m1Vanish))
      (vanish_const_mul W.m2 W.Φ W.hΦ W.m2Vanish)
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

/-- **G35.** The difference-row named inputs give the H5b comparison (7.29). -/
theorem h5b_of_diff {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bDiffInputs E Emod) :
    H5bTarget E Emod :=
  h5b_of_paper W.toPaper

/-- **G35.** Weakening direction: every `H5bMassInputs` gives an `H5bDiffInputs`, `e12 = e1 + e2`. -/
noncomputable def _root_.SteklovAudit.H5MissingMass.H5bMassInputs.toDiff
    {E Emod : ℝ → ℝ → ℝ → ℝ} (W : SteklovAudit.H5MissingMass.H5bMassInputs E Emod) :
    SteklovAudit.H5DiffCount.H5bDiffInputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  e12 := fun ε γ L => W.e1 ε γ L + W.e2 ε γ L
  diffCount := fun ε γ L => SteklovAudit.H5DiffCount.diff_of_counts _ _ _ _ _ _
    (W.trueCount ε γ L) (W.modelCount ε γ L)
  e12Vanish := SteklovAudit.H5CutoffSides.discVanish_of_sides W.e1 W.e2 W.e1Vanish W.e2Vanish
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

/-- The rebuilt discrepancy is the difference rate plus the two missing-mass terms. -/
theorem toPaper_disc {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bDiffInputs E Emod) :
    W.toPaper.disc = fun ε γ L => W.e12 ε γ L + W.Φ * W.m1 ε γ L + W.Φ * W.m2 ε γ L := rfl

end G35

end SteklovAudit.H5DiffCount
