import Mathlib
import SteklovAudit.H5HighMassAudit
import SteklovAudit.H5ColMassSplit

/-!
# G33: audit of the two-sided high-energy H5b inputs `H5bHighMass2Inputs` (G31)

Roadmap item G33.

* `highMass2OfBounds E Emod e1 e2 …` fills every field of `H5bHighMass2Inputs E Emod` from G24's
  empty family `zData` (profile `arctan`, `Φ = 2`, `hm1 = hm2 = 0`, `c = cB = 0`); only `|E| ≤ e1`,
  `|Emod| ≤ e2` and the vanishing of `e1`, `e2` are inputs.
* `highMass2Witness : H5bHighMass2Inputs 0 0`, `highMass2Witness_nonempty`: not vacuous.
* `highMass2_rows_not_target`: the rows `rowMissHigh`, `colMissHigh`, `lowCount`, `modelLowCount`
  and the vanishing of `hm1`, `hm2` mention only `D` and the rates (no `E`, `Emod`); they hold for the
  witness data while `H5bTarget` fails for `E = 2L`, `Emod = 0`.
* `highMass2_count_not_target`: with every non-count row filled by the witness data and `Emod = 0`,
  no vanishing `e1` meets the true count row for `E = 2L`. So after G31 all "target in disguise"
  content of H5b sits in the two one-spectrum count rows `trueCount` and `modelCount`.

What this file does NOT prove: no missing-mass, high-energy, low-count, count or Bessel row is
proved for the Steklov operator of the tetrahedron (or any concrete operator); the empty family is a
consistency check, not a model of the spectrum; no Dirichlet-to-Neumann operator is constructed;
(7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5HighMass2Audit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows SteklovAudit.H5CountAudit SteklovAudit.H5MissingMass
open SteklovAudit.H5MassAudit SteklovAudit.H5MassSplit SteklovAudit.H5HighMassAudit
open SteklovAudit.H5ColMassSplit

theorem zz_colMissHigh (M : ℝ) :
    ∑ j ∈ Finset.univ.filter fun j => M < zData.b j, (1 - ∑ i, zData.J i j ^ 2) ≤ 0 := by
  first
    | exact (Finset.sum_eq_zero fun j _ => Fin.elim0 j).le
    | (simp; done)

theorem zz_lowCount (M : ℝ) :
    ((Finset.univ.filter fun i => zData.a i ≤ M).card : ℝ) ≤ 0 := by
  have h1 : (Finset.univ.filter fun i => zData.a i ≤ M).card ≤
      (Finset.univ : Finset (Fin 0)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
  have h3 : (Finset.univ.filter fun i => zData.a i ≤ M).card = 0 := by omega
  rw [h3, Nat.cast_zero]

theorem zz_modelLowCount (M : ℝ) :
    ((Finset.univ.filter fun j => zData.b j ≤ M).card : ℝ) ≤ 0 := by
  have h1 : (Finset.univ.filter fun j => zData.b j ≤ M).card ≤
      (Finset.univ : Finset (Fin 0)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
  have h3 : (Finset.univ.filter fun j => zData.b j ≤ M).card = 0 := by omega
  rw [h3, Nat.cast_zero]

/-- The zero high-energy rate vanishes (any `M`, here `M = 0`). -/
theorem zz_hmVanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
    ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → (0 : ℝ) ≤ η * L :=
  fun _ _ _ _ η hη => ⟨0, 0, fun L hL => mul_nonneg hη.le hL⟩

/-- **G33.** Every field of `H5bHighMass2Inputs E Emod` except the two count rows is filled by the
empty family. -/
noncomputable def highMass2OfBounds (E Emod e1 e2 : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ ε γ L : ℝ, |E ε γ L| ≤ e1 ε γ L)
    (v1 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      e1 ε γ L ≤ η * L)
    (h2 : ∀ ε γ L : ℝ, |Emod ε γ L| ≤ e2 ε γ L)
    (v2 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      e2 ε γ L ≤ η * L) : H5bHighMass2Inputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  Φ := 2
  hΦ := show (0 : ℝ) ≤ 2 by norm_num
  profBound := arctan_abs_le_two
  e1 := e1
  trueCount := z_trueCount E e1 h1
  e1Vanish := v1
  hm1 := fun _ _ _ _ => 0
  rowMissHigh := fun _ _ M _ => z_rowMissHigh M
  hm1Vanish := fun _ _ _ _ η hη =>
    ⟨0, 0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩
  e2 := e2
  modelCount := z_modelCount Emod e2 h2
  e2Vanish := v2
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

/-- **G33.** An explicit witness of `H5bHighMass2Inputs` with `E = Emod = 0`. -/
noncomputable def highMass2Witness :
    H5bHighMass2Inputs (fun _ _ _ => 0) (fun _ _ _ => 0) :=
  highMass2OfBounds _ _ (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound zeroDisc_vanish zero_bound
    zeroDisc_vanish

theorem highMass2Witness_nonempty :
    Nonempty (H5bHighMass2Inputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨highMass2Witness⟩

/-- **G33.** The four high-energy / low-count rows and the vanishing of `hm1`, `hm2` involve only
`D` and the rates: they hold for the witness data (all rates `0`) while `H5bTarget` fails for
`E = 2L`, `Emod = 0`. -/
theorem highMass2_rows_not_target :
    (∀ M : ℝ, ∑ i ∈ Finset.univ.filter fun i => M < zData.a i,
      (1 - ∑ j, zData.J i j ^ 2) ≤ 0) ∧
    (∀ M : ℝ, ∑ j ∈ Finset.univ.filter fun j => M < zData.b j,
      (1 - ∑ i, zData.J i j ^ 2) ≤ 0) ∧
    (∀ M : ℝ, ((Finset.univ.filter fun i => zData.a i ≤ M).card : ℝ) ≤ 0) ∧
    (∀ M : ℝ, ((Finset.univ.filter fun j => zData.b j ≤ M).card : ℝ) ≤ 0) ∧
    (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η →
      ∃ M L₀ : ℝ, ∀ L, L₀ ≤ L → (0 : ℝ) ≤ η * L) ∧
    ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) :=
  ⟨z_rowMissHigh, zz_colMissHigh, zz_lowCount, zz_modelLowCount, zz_hmVanish,
    SteklovAudit.H5TailRate.not_target_double⟩

/-- **G33.** With every other row filled by the witness data and `Emod = 0`, no vanishing `e1`
meets the true count row for `E = 2L`: the failure of the target sits in the count row. -/
theorem highMass2_count_not_target :
    ¬ ∃ e1 : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L| ≤ e1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e1 ε γ L ≤ η * L) := by
  rintro ⟨e1, hc, hv⟩
  exact SteklovAudit.H5TailRate.not_target_double (h5b_of_high_mass2
    (highMass2OfBounds (fun _ _ L => 2 * L) (fun _ _ _ => 0) e1 (fun _ _ _ => 0)
      hc hv zero_bound zeroDisc_vanish))

end SteklovAudit.H5HighMass2Audit
