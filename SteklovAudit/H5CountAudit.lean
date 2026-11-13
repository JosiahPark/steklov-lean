import Mathlib
import SteklovAudit.H5CountRows
import SteklovAudit.H5SideAudit

/-!
# G24: audit of the count-form H5b inputs `H5bCountInputs` (G23)

Roadmap item G24.

* `zData`: the empty family (`nA = nB = 0`), so every sum over eigenvalues is empty.
  `countOfBounds E Emod e1 e2 …` fills every field of `H5bCountInputs E Emod` from it (profile
  `arctan`, `k1 = k2 = 0`); only `|E| ≤ e1`, `|Emod| ≤ e2` and the vanishing of `e1`, `e2` are inputs.
* `countWitness : H5bCountInputs 0 0`, `countWitness_nonempty`: the structure is not vacuous.
* `true_count_not_target`: for `E = 0`, `Emod = 2L` the true count row holds with `e1 = 0`, yet
  `H5bTarget` fails, so no vanishing `e2` meets the model count row. `model_count_not_target` is the
  mirror (`E = 2L`, `Emod = 0`). Neither count row alone is the target in disguise.
* `defect_rows_not_target`: the two completeness rows and `colBessel` mention neither `E` nor `Emod`;
  they hold (with `k1 = k2 = 0`) for the witness data while `H5bTarget` fails for `E = 2L`, `Emod = 0`.

What this file does NOT prove: no count, completeness or Bessel row is proved for the Steklov
operator of the tetrahedron (or any concrete operator); the empty family is a consistency check, not
a model of the spectrum; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input
and Theorem 1.3 / 11.1 remain conditional on the named inputs.
-/

namespace SteklovAudit.H5CountAudit

open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5PaperAudit SteklovAudit.H5SideRows SteklovAudit.H5SideAudit
open SteklovAudit.H5CountRows

/-- The empty family: no true and no model eigenvalues. -/
noncomputable def zData : Data (Fin 0) (Fin 0) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 0

theorem z_trueCount (E e1 : ℝ → ℝ → ℝ → ℝ) (h : ∀ ε γ L : ℝ, |E ε γ L| ≤ e1 ε γ L)
    (ε γ L : ℝ) : |E ε γ L - ∑ i, arctanProfile.φ (zData.a i - L)| ≤ e1 ε γ L := by
  first
    | (rw [Fin.sum_univ_zero, sub_zero]; exact h ε γ L)
    | (simpa using h ε γ L)

theorem z_modelCount (Emod e2 : ℝ → ℝ → ℝ → ℝ) (h : ∀ ε γ L : ℝ, |Emod ε γ L| ≤ e2 ε γ L)
    (ε γ L : ℝ) : |Emod ε γ L - ∑ j, arctanProfile.φ (zData.b j - L)| ≤ e2 ε γ L := by
  first
    | (rw [Fin.sum_univ_zero, sub_zero]; exact h ε γ L)
    | (simpa using h ε γ L)

theorem z_rowDefect (L : ℝ) :
    ∑ i, |arctanProfile.φ (zData.a i - L)| * (1 - ∑ j, zData.J i j ^ 2) ≤ 0 := by
  first | exact (Fin.sum_univ_zero _).le | simp

theorem z_colDefect (L : ℝ) :
    ∑ j, |arctanProfile.φ (zData.b j - L)| * (1 - ∑ i, zData.J i j ^ 2) ≤ 0 := by
  first | exact (Fin.sum_univ_zero _).le | simp

theorem z_colBessel (j : Fin 0) : ∑ i, zData.J i j ^ 2 ≤ 1 := Fin.elim0 j

theorem z_bessel (i : Fin 0) : ∑ j, zData.J i j ^ 2 ≤ 1 := Fin.elim0 i

theorem z_count (L : ℝ) : (Fintype.card (Fin 0) : ℝ) ≤ 1 * (1 + L) ^ 2 := by
  simp only [Fintype.card_fin, Nat.cast_zero, one_mul]
  positivity

theorem z_defect (L : ℝ) : hs2 zData.K ≤ (0 : ℝ) ^ 2 * (1 + L) ^ 2 := by
  first | (simp [hs2]; done) | (unfold hs2; simp)

theorem z_tail (M : ℝ) : hs2 (mask (hiE zData M) zData.K) ≤ 0 := by
  first | (simp [hs2]; done) | (unfold hs2; simp)

theorem z_lowCount (M : ℝ) :
    ((Finset.univ.filter fun i => zData.a i ≤ M).card : ℝ) ≤ 1 := by
  have h1 : (Finset.univ.filter fun i => zData.a i ≤ M).card ≤
      (Finset.univ : Finset (Fin 0)).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
  have h3 : (Finset.univ.filter fun i => zData.a i ≤ M).card ≤ 1 := by omega
  exact_mod_cast h3

/-- **G24.** Every field of `H5bCountInputs E Emod` is filled by the empty family; only
`|E| ≤ e1`, `|Emod| ≤ e2` and the vanishing of `e1`, `e2` are inputs. -/
noncomputable def countOfBounds (E Emod e1 e2 : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ ε γ L : ℝ, |E ε γ L| ≤ e1 ε γ L)
    (v1 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      e1 ε γ L ≤ η * L)
    (h2 : ∀ ε γ L : ℝ, |Emod ε γ L| ≤ e2 ε γ L)
    (v2 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      e2 ε γ L ≤ η * L) : H5bCountInputs E Emod where
  nA := fun _ _ _ => 0
  nB := fun _ _ _ => 0
  D := fun _ _ _ => zData
  P := arctanProfile
  e1 := e1
  trueCount := z_trueCount E e1 h1
  e1Vanish := v1
  k1 := fun _ _ _ => 0
  rowDefect := fun _ _ L => z_rowDefect L
  k1Vanish := zeroDisc_vanish
  e2 := e2
  modelCount := z_modelCount Emod e2 h2
  e2Vanish := v2
  k2 := fun _ _ _ => 0
  colDefect := fun _ _ L => z_colDefect L
  k2Vanish := zeroDisc_vanish
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

/-- **G24.** An explicit witness of the count-form inputs with `E = Emod = 0`. -/
noncomputable def countWitness : H5bCountInputs (fun _ _ _ => 0) (fun _ _ _ => 0) :=
  countOfBounds _ _ (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound zeroDisc_vanish zero_bound
    zeroDisc_vanish

theorem countWitness_nonempty :
    Nonempty (H5bCountInputs (fun _ _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨countWitness⟩

/-- **G24 audit.** For `E = 0`, `Emod = 2L` the true count row holds with `e1 = 0`, yet `H5bTarget`
fails; so no vanishing `e2` meets the model count row. The true count row alone is not the target. -/
theorem true_count_not_target :
    (∀ ε γ L : ℝ, |(fun _ _ _ => (0 : ℝ)) ε γ L - ∑ i, arctanProfile.φ (zData.a i - L)| ≤
      (fun _ _ _ => (0 : ℝ)) ε γ L) ∧
    ¬ H5bTarget (fun _ _ _ => 0) (fun _ _ L => 2 * L) ∧
    ¬ ∃ e2 : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L| ≤ e2 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e2 ε γ L ≤ η * L) := by
  refine ⟨z_trueCount (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound, not_target_mirror, ?_⟩
  rintro ⟨e2, hc, hv⟩
  exact not_target_mirror (h5b_of_counts
    (countOfBounds (fun _ _ _ => 0) (fun _ _ L => 2 * L) (fun _ _ _ => 0) e2
      zero_bound zeroDisc_vanish hc hv))

/-- **G24 audit (mirror).** For `E = 2L`, `Emod = 0` the model count row holds with `e2 = 0`, yet
`H5bTarget` fails; so no vanishing `e1` meets the true count row. -/
theorem model_count_not_target :
    (∀ ε γ L : ℝ, |(fun _ _ _ => (0 : ℝ)) ε γ L - ∑ j, arctanProfile.φ (zData.b j - L)| ≤
      (fun _ _ _ => (0 : ℝ)) ε γ L) ∧
    ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) ∧
    ¬ ∃ e1 : ℝ → ℝ → ℝ → ℝ, (∀ ε γ L : ℝ, |2 * L| ≤ e1 ε γ L) ∧
      (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
        e1 ε γ L ≤ η * L) := by
  refine ⟨z_modelCount (fun _ _ _ => 0) (fun _ _ _ => 0) zero_bound,
    SteklovAudit.H5TailRate.not_target_double, ?_⟩
  rintro ⟨e1, hc, hv⟩
  exact SteklovAudit.H5TailRate.not_target_double (h5b_of_counts
    (countOfBounds (fun _ _ L => 2 * L) (fun _ _ _ => 0) e1 (fun _ _ _ => 0)
      hc hv zero_bound zeroDisc_vanish))

/-- **G24 audit.** The completeness rows and `colBessel` mention only `D`, `P`, `k1`, `k2`: they hold
for the witness data (with `k1 = k2 = 0`) while `H5bTarget` fails for `E = 2L`, `Emod = 0`. -/
theorem defect_rows_not_target :
    (∀ L : ℝ, ∑ i, |arctanProfile.φ (zData.a i - L)| * (1 - ∑ j, zData.J i j ^ 2) ≤ 0) ∧
    (∀ L : ℝ, ∑ j, |arctanProfile.φ (zData.b j - L)| * (1 - ∑ i, zData.J i j ^ 2) ≤ 0) ∧
    (∀ j, ∑ i, zData.J i j ^ 2 ≤ 1) ∧
    ¬ H5bTarget (fun _ _ L => 2 * L) (fun _ _ _ => 0) :=
  ⟨z_rowDefect, z_colDefect, z_colBessel, SteklovAudit.H5TailRate.not_target_double⟩

end SteklovAudit.H5CountAudit
