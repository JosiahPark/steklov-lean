import Mathlib
import SteklovAudit.H5SideRows
import SteklovAudit.H5PaperAudit

/-!
# G20: audit of the side-form H5b inputs `H5bSideInputs` (G19)

Roadmap item G20.

* `sideOfBounds E Emod d1 d2 …`: every field of `H5bSideInputs E Emod` other than the two side rows
  is filled by G17's fixed family (`wData (wN L)`, zero coupling `J = 0`, profile `arctan`), which does
  not depend on `E` or `Emod`. Since `J = 0`, both weighted traces vanish, so the side rows reduce to
  `|E| ≤ d1` and `|Emod| ≤ d2`.
* `sideWitness`, `sideWitness_nonempty`: an explicit `H5bSideInputs 0 0` (`d1 = d2 = 0`): the structure
  is not vacuous.
* `model_side_not_target`: for `E = 2L`, `Emod = 0` the model-side row (with `d2 = 0`, which vanishes)
  and all non-cutoff rows hold, while `H5bTarget` fails; hence no `d1` satisfies the true-side row
  with `d1Vanish`. `true_side_not_target` is the mirror (`E = 0`, `Emod = 2L`, via
  `not_target_mirror`). So neither side row alone is the target in disguise.

What this file does NOT prove: no field of `H5bSideInputs` (in particular neither side row) is proved
for the Steklov operator of the tetrahedron; no Dirichlet-to-Neumann operator is constructed; (7.29),
every [H…] input and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5SideAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows

/-- With zero coupling the row-weighted trace of the true eigenvalues vanishes. -/
theorem wData_rowTrace (φ : ℝ → ℝ) (n : ℕ) (L : ℝ) :
    ∑ i, φ ((wData n).a i - L) * (∑ j, (wData n).J i j ^ 2) = 0 := by
  simp [wData]

/-- With zero coupling the column-weighted trace of the model eigenvalues vanishes. -/
theorem wData_colTrace (φ : ℝ → ℝ) (n : ℕ) (L : ℝ) :
    ∑ j, φ ((wData n).b j - L) * (∑ i, (wData n).J i j ^ 2) = 0 := by
  simp [wData]

theorem w_trueSide (E d1 : ℝ → ℝ → ℝ → ℝ) (h : ∀ ε γ L : ℝ, |E ε γ L| ≤ d1 ε γ L)
    (ε γ L : ℝ) :
    |E ε γ L - ∑ i, arctanProfile.φ ((wData (wN L)).a i - L) *
      (∑ j, (wData (wN L)).J i j ^ 2)| ≤ d1 ε γ L := by
  rw [wData_rowTrace, sub_zero]
  exact h ε γ L

theorem w_modelSide (Emod d2 : ℝ → ℝ → ℝ → ℝ) (h : ∀ ε γ L : ℝ, |Emod ε γ L| ≤ d2 ε γ L)
    (ε γ L : ℝ) :
    |Emod ε γ L - ∑ j, arctanProfile.φ ((wData (wN L)).b j - L) *
      (∑ i, (wData (wN L)).J i j ^ 2)| ≤ d2 ε γ L := by
  rw [wData_colTrace, sub_zero]
  exact h ε γ L

/-- **G20.** All rows except the two side rows come from G17's fixed family; only `|E| ≤ d1`,
`|Emod| ≤ d2` and the vanishing of `d1`, `d2` are inputs. -/
noncomputable def sideOfBounds (E Emod d1 d2 : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ ε γ L : ℝ, |E ε γ L| ≤ d1 ε γ L)
    (v1 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      d1 ε γ L ≤ η * L)
    (h2 : ∀ ε γ L : ℝ, |Emod ε γ L| ≤ d2 ε γ L)
    (v2 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      d2 ε γ L ≤ η * L) : H5bSideInputs E Emod where
  nA := fun _ _ L => wN L
  nB := fun _ _ _ => 1
  D := fun _ _ L => wData (wN L)
  P := arctanProfile
  d1 := d1
  trueSide := w_trueSide E d1 h1
  d1Vanish := v1
  d2 := d2
  modelSide := w_modelSide Emod d2 h2
  d2Vanish := v2
  Cm := fun _ _ => 1
  Ck := fun _ _ => 0
  hCm := fun _ _ => show (0 : ℝ) ≤ 1 from zero_le_one
  bessel := fun _ _ L i => wData_bessel (wN L) i
  count := fun _ _ L => wData_count L
  defect := fun _ _ L => wData_defect (wN L) L
  τ := fun _ _ _ => 0
  tail := fun _ _ M L => wData_tail (wN L) M
  Cτ := fun _ _ => 0
  tailRate := zeroRate
  ha := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  hb := fun _ _ _ _ => show (0 : ℝ) ≤ 0 from le_refl 0
  c := fun _ _ _ => 1
  lowCount := fun _ _ M L => wData_lowCount L M

/-- The zero discrepancy vanishes. -/
theorem zeroDisc_vanish : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
    (fun _ _ _ => (0 : ℝ)) ε γ L ≤ η * L :=
  fun _ _ _ _ η hη => ⟨0, fun L hL => show (0 : ℝ) ≤ η * L from mul_nonneg hη.le hL⟩

theorem zero_bound : ∀ ε γ L : ℝ, |(fun _ _ _ => (0 : ℝ)) ε γ L| ≤ (fun _ _ _ => (0 : ℝ)) ε γ L :=
  fun _ _ _ => by simp

/-- **G20.** An explicit witness of the side-form inputs with zero counts and `d1 = d2 = 0`. -/
noncomputable def sideWitness : H5bSideInputs (fun _ _ _ => 0) (fun _ _ _ => 0) :=
  sideOfBounds _ _ (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound zeroDisc_vanish zero_bound zeroDisc_vanish

theorem sideWitness_nonempty : Nonempty (H5bSideInputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨sideWitness⟩

/-- Mirror of G9's `not_target_double`: `E = 0`, `Emod = 2L` violate the H5b target. -/
theorem not_target_mirror : ¬ H5bTarget (fun _ _ _ => 0) (fun _ _ L => 2 * L) := by
  intro h
  apply SteklovAudit.H5TailRate.not_target_double
  unfold H5bTarget at h ⊢
  intro ε γ hε hγ η hη
  obtain ⟨L₀, hL⟩ := h ε γ hε hγ η hη
  exact ⟨L₀, fun L hL' => (abs_sub_comm _ _).trans_le (hL L hL')⟩

/-- **G20 audit.** For `E = 2L`, `Emod = 0` the model-side row holds with `d2 = 0` on the fixed
family (whose non-cutoff rows hold whatever `E`, `Emod` are), yet `H5bTarget` fails; so no `d1`
meets the true-side row together with `d1Vanish`. The model side alone is not the target. -/
theorem model_side_not_target :
    (∀ ε γ L : ℝ, |(fun _ _ _ => (0 : ℝ)) ε γ L - ∑ j, arctanProfile.φ ((wData (wN L)).b j - L) *
      (∑ i, (wData (wN L)).J i j ^ 2)| ≤ (fun _ _ _ => (0 : ℝ)) ε γ L) ∧
    ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) ∧
    ¬ ∃ d1 : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L| ≤ d1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        d1 ε γ L ≤ η * L) := by
  refine ⟨w_modelSide (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound, SteklovAudit.H5TailRate.not_target_double, ?_⟩
  rintro ⟨d1, hc, hv⟩
  exact SteklovAudit.H5TailRate.not_target_double (h5b_of_sides
    (sideOfBounds (fun _ _ L => 2 * L) (fun _ _ _ => 0) d1 (fun _ _ _ => 0) hc hv
      zero_bound zeroDisc_vanish))

/-- **G20 audit (mirror).** For `E = 0`, `Emod = 2L` the true-side row holds with `d1 = 0`, yet
`H5bTarget` fails; so no `d2` meets the model-side row together with `d2Vanish`. -/
theorem true_side_not_target :
    (∀ ε γ L : ℝ, |(fun _ _ _ => (0 : ℝ)) ε γ L - ∑ i, arctanProfile.φ ((wData (wN L)).a i - L) *
      (∑ j, (wData (wN L)).J i j ^ 2)| ≤ (fun _ _ _ => (0 : ℝ)) ε γ L) ∧
    ¬ H5bTarget (fun _ _ _ => 0) (fun _ _ L => 2 * L) ∧
    ¬ ∃ d2 : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L| ≤ d2 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        d2 ε γ L ≤ η * L) := by
  refine ⟨w_trueSide (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound, not_target_mirror, ?_⟩
  rintro ⟨d2, hc, hv⟩
  exact not_target_mirror (h5b_of_sides
    (sideOfBounds (fun _ _ _ => 0) (fun _ _ L => 2 * L) (fun _ _ _ => 0) d2
      zero_bound zeroDisc_vanish hc hv))

end SteklovAudit.H5SideAudit
