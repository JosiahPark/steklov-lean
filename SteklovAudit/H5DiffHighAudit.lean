import Mathlib
import SteklovAudit.H5DiffHighMass
import SteklovAudit.H5DiffAudit
import SteklovAudit.H5HighMass2Audit

/-!
# G39: audit of the difference-row / high-mass H5b inputs `H5bDiffHigh2Inputs` (G38)

Roadmap item G39.

* `H5bHighMass2Inputs.toDiffHigh2` (moved from G38): every `H5bHighMass2Inputs E Emod` (G31) gives
  an `H5bDiffHigh2Inputs E Emod`, with `e12 = e1 + e2` (`diff_of_counts`, `discVanish_of_sides`).
* `diffHigh2OfBounds E Emod e12 h v` fills every field from G24's empty family `zData`
  (`hm1 = hm2 = 0`, `c = cB = 0`); only `|E - Emod| ≤ e12` and the vanishing of `e12` are inputs.
  `diffHigh2Witness_nonempty`: the structure is not vacuous.
* Strictness, `diffHigh2_not_highMass2`: for `E = Emod = 2L` a full `H5bDiffHigh2Inputs` on the
  empty family exists with `e12 = 0`, while no `H5bHighMass2Inputs (2L) (2L)` whose true family is
  empty exists (its `trueCount` row fails, as in G36's `double_trueCount_fails`).
  So the current strongest form of H5b in the F table is `H5bDiffHigh2Inputs`.

What this file does NOT prove: no difference, count, missing-mass, high-energy, low-count, Bessel
or tail row is proved for the Dirichlet-to-Neumann operator of the regular tetrahedron or for the
model operator; the empty family is a consistency check, not a model of the spectrum; (7.29),
every ledger input [H1]–[H6] and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5DiffHighAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5MassSplit SteklovAudit.H5HighMassAudit
open SteklovAudit.H5ColMassSplit SteklovAudit.H5HighMass2Audit SteklovAudit.H5DiffHighMass

/-- **G39 (from G38).** Weakening direction: the two count rows give the one difference row. -/
noncomputable def _root_.SteklovAudit.H5ColMassSplit.H5bHighMass2Inputs.toDiffHigh2
    {E Emod : ℝ → ℝ → ℝ → ℝ} (W : H5bHighMass2Inputs E Emod) : H5bDiffHigh2Inputs E Emod where
  nA := W.nA
  nB := W.nB
  D := W.D
  P := W.P
  Φ := W.Φ
  hΦ := W.hΦ
  profBound := W.profBound
  e12 := fun ε γ L => W.e1 ε γ L + W.e2 ε γ L
  diffCount := fun ε γ L =>
    SteklovAudit.H5DiffCount.diff_of_counts _ _ _ _ _ _ (W.trueCount ε γ L) (W.modelCount ε γ L)
  e12Vanish := SteklovAudit.H5CutoffSides.discVanish_of_sides W.e1 W.e2 W.e1Vanish W.e2Vanish
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

/-- **G39.** Every field of `H5bDiffHigh2Inputs E Emod` except the difference row is filled by
the empty family. -/
noncomputable def diffHigh2OfBounds (E Emod e12 : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ ε γ L : ℝ, |E ε γ L - Emod ε γ L| ≤ e12 ε γ L)
    (v : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      e12 ε γ L ≤ η * L) : H5bDiffHigh2Inputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  e12 := e12
  diffCount := SteklovAudit.H5DiffAudit.z_diffCount E Emod e12 h
  e12Vanish := v
  hm1 := fun _ _ _ _ => 0
  rowMissHigh := fun _ _ M _ => z_rowMissHigh M
  hm1Vanish := fun _ _ _ _ η hη =>
    ⟨0, 0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩
  hm2 := fun _ _ _ _ => 0
  colMissHigh := fun _ _ M _ => zz_colMissHigh M
  hm2Vanish := fun _ _ _ _ η hη =>
    ⟨0, 0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩
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
  c := fun _ _ _ => 0
  lowCount := fun _ _ M _ => zz_lowCount M
  cB := fun _ _ _ => 0
  modelLowCount := fun _ _ M _ => zz_modelLowCount M

/-- **G39.** An explicit witness with `E = Emod = 0`, `e12 = 0`. -/
noncomputable def diffHigh2Witness :
    H5bDiffHigh2Inputs (fun _ _ _ => 0) (fun _ _ _ => 0) :=
  diffHigh2OfBounds _ _ (fun _ _ _ => 0) (SteklovAudit.H5DiffAudit.self_diff_bound _)
    zeroDisc_vanish

theorem diffHigh2Witness_nonempty :
    Nonempty (H5bDiffHigh2Inputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨diffHigh2Witness⟩

/-- **G39.** A full witness for `E = Emod = 2L` on the empty family, `e12 = 0`. -/
noncomputable def diffHigh2Double :
    H5bDiffHigh2Inputs (fun _ _ L => 2 * L) (fun _ _ L => 2 * L) :=
  diffHigh2OfBounds _ _ (fun _ _ _ => 0) (SteklovAudit.H5DiffAudit.self_diff_bound _)
    zeroDisc_vanish

/-- **G39.** No `H5bHighMass2Inputs (2L) (2L)` has an empty true family: `trueCount` would force
`2L ≤ e1`, contradicting `e1Vanish` (tested with `η = 1` at `L = max L₀ 1`). -/
theorem highMass2_double_empty_fails :
    ¬ ∃ W : H5bHighMass2Inputs (fun _ _ L => 2 * L) (fun _ _ L => 2 * L),
      ∀ ε γ L : ℝ, W.nA ε γ L = 0 := by
  rintro ⟨W, hn⟩
  obtain ⟨L₀, hL₀⟩ := W.e1Vanish 1 1 one_pos one_pos 1 one_pos
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h1 : W.e1 1 1 (max L₀ 1) ≤ 1 * max L₀ 1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 : |2 * max L₀ 1 - ∑ i, W.P.φ ((W.D 1 1 (max L₀ 1)).a i - max L₀ 1)| ≤
      W.e1 1 1 (max L₀ 1) := W.trueCount 1 1 (max L₀ 1)
  have hs : ∑ i, W.P.φ ((W.D 1 1 (max L₀ 1)).a i - max L₀ 1) = 0 :=
    Finset.sum_eq_zero fun i _ =>
      absurd (lt_of_lt_of_eq i.isLt (hn 1 1 (max L₀ 1))) (Nat.not_lt_zero _)
  rw [hs, sub_zero, abs_of_nonneg (by linarith)] at h2
  linarith

/-- **G39.** `H5bDiffHigh2Inputs` is strictly weaker than `H5bHighMass2Inputs`: every
`H5bHighMass2Inputs` gives one (`toDiffHigh2`), and for `E = Emod = 2L` a full
`H5bDiffHigh2Inputs` on the empty family exists with `e12 = 0`, while no `H5bHighMass2Inputs`
with an empty true family exists. -/
theorem diffHigh2_not_highMass2 :
    (∀ E Emod : ℝ → ℝ → ℝ → ℝ, H5bHighMass2Inputs E Emod → Nonempty (H5bDiffHigh2Inputs E Emod)) ∧
    (∃ W : H5bDiffHigh2Inputs (fun _ _ L => 2 * L) (fun _ _ L => 2 * L),
      (∀ ε γ L : ℝ, W.nA ε γ L = 0) ∧ W.e12 = fun _ _ _ => 0) ∧
    ¬ ∃ W : H5bHighMass2Inputs (fun _ _ L => 2 * L) (fun _ _ L => 2 * L),
      ∀ ε γ L : ℝ, W.nA ε γ L = 0 :=
  ⟨fun _ _ W => ⟨W.toDiffHigh2⟩, ⟨diffHigh2Double, fun _ _ _ => rfl, rfl⟩,
    highMass2_double_empty_fails⟩

end SteklovAudit.H5DiffHighAudit
