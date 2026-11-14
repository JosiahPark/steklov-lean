import Mathlib
import SteklovAudit.H5MassAudit
import SteklovAudit.H5HighMass2Audit
import SteklovAudit.H5DiffCount

/-!
# G36: audit of the difference-row H5b inputs `H5bDiffInputs` (G35)

Roadmap item G36.

* `diffOfBounds E Emod e12 …` fills every field of `H5bDiffInputs E Emod` from G24's empty family
  `zData` (profile `arctan`, `Φ = 2`, `m1 = m2 = 0`); only `|E - Emod| ≤ e12` and the vanishing of
  `e12` are inputs.
* `diffWitness : H5bDiffInputs 0 0` (`e12 = 0`), `diffWitness_nonempty`: the structure is not vacuous.
* Strictness, `diff_not_counts`: for the empty family and `E = Emod = 2L`, the single difference row
  holds with `e12 = 0` (`double_diffCount`, and a full `H5bDiffInputs (2L) (2L)` exists), while the
  true count row `trueCount` of G26 fails for every vanishing `e1` (`double_trueCount_fails`, tested
  with `η = 1` at `L = max L₀ 1`). So the one difference row is strictly weaker than the pair of
  count rows it replaces.
* G37, `diff_row_not_target`: for the G25 family (`⌈L⌉₊` true eigenvalues at `0`, empty model,
  `E L = ⌈L⌉₊ * arctan (0 - L)`, `Emod = 0`) the difference row holds with `e12 = 0` while
  `H5bTarget` fails. `diff_rows_E_free`: every other field is filled for any `E`, `Emod` by
  `diffOfBounds`, so all E-dependent content of H5b is the one row `diffCount`, i.e. (7.29) for the
  test `φ (· - L)` with `J` removed. That row is open for the actual operator.

What this file does NOT prove: no count, difference, missing-mass or Bessel row is proved for the
Steklov operator of the tetrahedron (or any concrete operator); the empty family is a consistency
check, not a model of the spectrum; no Dirichlet-to-Neumann operator is constructed; (7.29), every
[H…] input and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5DiffAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5DiffCount

/-- On the empty family both smoothed counts are `0`, so the difference row is `|E - Emod| ≤ e12`. -/
theorem z_diffCount (E Emod e12 : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ ε γ L : ℝ, |E ε γ L - Emod ε γ L| ≤ e12 ε γ L) (ε γ L : ℝ) :
    |(E ε γ L - Emod ε γ L) - (∑ i, arctanProfile.φ (zData.a i - L) -
      ∑ j, arctanProfile.φ (zData.b j - L))| ≤ e12 ε γ L := by
  first
    | (rw [Fin.sum_univ_zero, Fin.sum_univ_zero, sub_zero, sub_zero]; exact h ε γ L)
    | (simpa using h ε γ L)

/-- **G36.** Every field of `H5bDiffInputs E Emod` except the difference row is filled by the
empty family. -/
noncomputable def diffOfBounds (E Emod e12 : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ ε γ L : ℝ, |E ε γ L - Emod ε γ L| ≤ e12 ε γ L)
    (v : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      e12 ε γ L ≤ η * L) : H5bDiffInputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  e12 := e12
  diffCount := z_diffCount E Emod e12 h
  e12Vanish := v
  m1 := fun _ _ _ => 0
  rowMiss := fun _ _ _ => z_rowMiss
  m1Vanish := zeroDisc_vanish
  m2 := fun _ _ _ => 0
  colMiss := fun _ _ _ => z_colMiss
  m2Vanish := zeroDisc_vanish
  colBessel := fun _ _ _ j => z_colBessel j
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ _ i => z_bessel i
  count := fun _ _ L => z_count L
  defect := fun _ _ L => z_defect L
  τ := fun _ _ _ => 0
  tail := fun _ _ M _ => z_tail M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M _ => z_lowCount M

/-- `|E - E| ≤ 0` for any count `E`. -/
theorem self_diff_bound (E : ℝ → ℝ → ℝ → ℝ) :
    ∀ ε γ L : ℝ, |E ε γ L - E ε γ L| ≤ (fun _ _ _ => (0 : ℝ)) ε γ L :=
  fun ε γ L => by simp

/-- **G36.** An explicit witness of the difference-row inputs with `E = Emod = 0`, `e12 = 0`. -/
noncomputable def diffWitness : H5bDiffInputs (fun _ _ _ => 0) (fun _ _ _ => 0) :=
  diffOfBounds _ _ (fun _ _ _ => 0) (self_diff_bound _) zeroDisc_vanish

theorem diffWitness_nonempty :
    Nonempty (H5bDiffInputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨diffWitness⟩

/-- **G36.** A full difference-row witness for `E = Emod = 2L` (empty family, `e12 = 0`). -/
noncomputable def diffDouble : H5bDiffInputs (fun _ _ L => 2 * L) (fun _ _ L => 2 * L) :=
  diffOfBounds _ _ (fun _ _ _ => 0) (self_diff_bound _) zeroDisc_vanish

/-- **G36.** Empty family, `E = Emod = 2L`: the difference row holds with `e12 = 0`. -/
theorem double_diffCount : ∀ ε γ L : ℝ,
    |(2 * L - 2 * L) - (∑ i, arctanProfile.φ (zData.a i - L) -
      ∑ j, arctanProfile.φ (zData.b j - L))| ≤ 0 :=
  fun ε γ L => z_diffCount (fun _ _ L => 2 * L) (fun _ _ L => 2 * L) (fun _ _ _ => 0)
    (self_diff_bound _) ε γ L

/-- **G36.** Empty family, `E = 2L`: no vanishing `e1` meets the true count row of G26. -/
theorem double_trueCount_fails :
    ¬ ∃ e1 : ℝ → ℝ → ℝ → ℝ,
      (∀ ε γ L : ℝ, |2 * L - ∑ i, arctanProfile.φ (zData.a i - L)| ≤ e1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e1 ε γ L ≤ η * L) := by
  rintro ⟨e1, hc, hv⟩
  obtain ⟨L₀, hL₀⟩ := hv 1 1 one_pos one_pos 1 one_pos
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 := hc 1 1 (max L₀ 1)
  have hs : ∑ i, arctanProfile.φ (zData.a i - max L₀ 1) = 0 := by
    first | exact Fin.sum_univ_zero _ | simp
  rw [hs, sub_zero, abs_of_nonneg (by linarith)] at h2
  linarith

/-- **G36.** The single difference row is strictly weaker than the pair of count rows: for the
empty family with `E = Emod = 2L` a full `H5bDiffInputs` exists and the difference row holds with
`e12 = 0`, while the true count row fails for every vanishing `e1`. -/
theorem diff_not_counts :
    Nonempty (H5bDiffInputs (fun _ _ L => 2 * L) (fun _ _ L => 2 * L)) ∧
    (∀ ε γ L : ℝ, |(2 * L - 2 * L) - (∑ i, arctanProfile.φ (zData.a i - L) -
      ∑ j, arctanProfile.φ (zData.b j - L))| ≤ 0) ∧
    ¬ ∃ e1 : ℝ → ℝ → ℝ → ℝ,
      (∀ ε γ L : ℝ, |2 * L - ∑ i, arctanProfile.φ (zData.a i - L)| ≤ e1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e1 ε γ L ≤ η * L) :=
  ⟨⟨diffDouble⟩, double_diffCount, double_trueCount_fails⟩

/-! ## G37: the difference row is not the target in disguise -/

/-- **G37.** The G25 family (`⌈L⌉₊` true eigenvalues at `0`, empty model spectrum, `φ = arctan`,
`E L = ⌈L⌉₊ * arctan (0 - L)`, `Emod = 0`) meets the difference row with `e12 = 0`. -/
theorem ceil_diffCount (L : ℝ) :
    |((⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L) - 0) -
      (∑ i : Fin ⌈L⌉₊, arctanProfile.φ ((fun _ : Fin ⌈L⌉₊ => (0 : ℝ)) i - L) -
        ∑ j : Fin 0, arctanProfile.φ ((fun _ : Fin 0 => (0 : ℝ)) j - L))| ≤ 0 := by
  have h0 : ∑ j : Fin 0, arctanProfile.φ ((fun _ : Fin 0 => (0 : ℝ)) j - L) = 0 := by
    first | exact Fin.sum_univ_zero _ | simp
  first
    | (rw [h0, sub_zero, sub_zero]; exact ceil_trueCount L)
    | (rw [h0]; simpa using ceil_trueCount L)

/-- **G37.** For the G25 counts `E L = ⌈L⌉₊ * arctan (0 - L)`, `Emod = 0`, the H5b target fails:
`|E| ≥ (π/4) L` for `L ≥ 1` (tested with `η = 1/2`). -/
theorem ceil_not_target :
    ¬ H5bTarget (fun _ _ L => (⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L)) (fun _ _ _ => 0) := by
  intro h
  obtain ⟨L₀, hL₀⟩ := h 1 1 one_pos one_pos (1 / 2) (by norm_num)
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h2 : |(⌈max L₀ 1⌉₊ : ℝ) * arctanProfile.φ (0 - max L₀ 1) - 0| ≤ 1 / 2 * max L₀ 1 :=
    hL₀ (max L₀ 1) (le_max_left _ _)
  rw [sub_zero] at h2
  have hφ : arctanProfile.φ (0 - max L₀ 1) = -Real.arctan (max L₀ 1) := by
    show Real.arctan (0 - max L₀ 1) = _
    rw [zero_sub, Real.arctan_neg]
  have ha : Real.pi / 4 ≤ Real.arctan (max L₀ 1) := by
    rw [← Real.arctan_one]
    first
      | exact Real.arctan_strictMono.monotone hL1
      | exact Real.arctan_strictMono.le_iff_le.mpr hL1
      | exact Real.arctan_mono hL1
  have hc : max L₀ 1 ≤ (⌈max L₀ 1⌉₊ : ℝ) := Nat.le_ceil _
  have hpi := Real.pi_gt_three
  have hpi4 : (0 : ℝ) ≤ Real.pi / 4 := by linarith
  have hat : 0 ≤ Real.arctan (max L₀ 1) := le_trans hpi4 ha
  have hcpos : (0 : ℝ) ≤ (⌈max L₀ 1⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [hφ, mul_neg, abs_neg, abs_of_nonneg (mul_nonneg hcpos hat)] at h2
  have h3 : max L₀ 1 * (Real.pi / 4) ≤ (⌈max L₀ 1⌉₊ : ℝ) * Real.arctan (max L₀ 1) :=
    mul_le_mul hc ha hpi4 hcpos
  have h4 : max L₀ 1 * 3 ≤ max L₀ 1 * Real.pi :=
    mul_le_mul_of_nonneg_left hpi.le (by linarith)
  first | linarith | nlinarith

/-- **G37.** The difference row is not `H5bTarget` in disguise: for the G25 family the row holds
with `e12 = 0` while the target fails. -/
theorem diff_row_not_target :
    (∀ L : ℝ, |((⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L) - 0) -
      (∑ i : Fin ⌈L⌉₊, arctanProfile.φ ((fun _ : Fin ⌈L⌉₊ => (0 : ℝ)) i - L) -
        ∑ j : Fin 0, arctanProfile.φ ((fun _ : Fin 0 => (0 : ℝ)) j - L))| ≤ 0) ∧
    ¬ H5bTarget (fun _ _ L => (⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L)) (fun _ _ _ => 0) :=
  ⟨ceil_diffCount, ceil_not_target⟩

/-- **G37.** Every field of `H5bDiffInputs` other than `diffCount` (and the vanishing of its rate)
is free of `E`, `Emod`: for ANY counts, `diffOfBounds` fills them from the empty family, so a full
structure exists as soon as the difference row and `e12Vanish` hold. For `E = 2L`, `Emod = 0` the
target fails, and correspondingly no vanishing `e12` meets the difference row: all E-dependent
content of H5b is the one row `diffCount`. -/
theorem diff_rows_E_free :
    (∀ E Emod e12 : ℝ → ℝ → ℝ → ℝ,
      (∀ ε γ L : ℝ, |E ε γ L - Emod ε γ L| ≤ e12 ε γ L) →
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e12 ε γ L ≤ η * L) →
      ∃ W : H5bDiffInputs E Emod, W.e12 = e12) ∧
    ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) ∧
    ¬ ∃ e12 : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L - 0| ≤ e12 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e12 ε γ L ≤ η * L) := by
  refine ⟨fun E Emod e12 h v => ⟨diffOfBounds E Emod e12 h v, rfl⟩,
    SteklovAudit.H5TailRate.not_target_double, ?_⟩
  rintro ⟨e12, hc, hv⟩
  exact SteklovAudit.H5TailRate.not_target_double
    (h5b_of_diff (diffOfBounds (fun _ _ L => 2 * L) (fun _ _ _ => 0) e12 hc hv))

end SteklovAudit.H5DiffAudit
