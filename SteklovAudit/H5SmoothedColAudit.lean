import Mathlib
import SteklovAudit.H5SmoothedIdent
import SteklovAudit.H5CountAudit
import SteklovAudit.H5DiffAudit

/-!
# G45: on the smoothed-identification route the column missing-mass row carries content of its own

Roadmap item G45. G41 showed the row missing-mass row of `H5bSmoothedInputs` (G40) is not free.
This file checks the column row separately, with a family for which every row-side row holds.

* `smColD L`: no true eigenvalues, `⌈L⌉₊` model eigenvalues at `0`, `J = 0`.
* `smCol_rowMass_zero`: its row missing mass is `0`, so `rowMiss` holds with `m1 = 0`
  (`smCol_rowMiss_zero`), and `m1 = 0` meets the `o(L)` condition.
* `smCol_colMass`: its column missing mass is `⌈L⌉₊`.
* `smoothed_colMiss_forces`: any `m2` meeting `colMiss` for this family has `m2 ≥ ⌈L⌉₊`, so
  `m2Vanish` fails.
* `smCol_not_target`: the smoothed counts `0` and `⌈L⌉₊ · φ (0 - L)` (`φ = arctan`) violate
  `H5bTarget` (G37's `ceil_not_target` with `abs_sub_comm`).
* `smoothed_needs_colMass`: no `H5bSmoothedInputs` has the column missing mass of this family.

F table text: the column (model-side completeness) row is independent content; the row-side rows
alone do not give (7.29) on the smoothed route.

What this file does NOT prove: no missing-mass, Bessel, count, defect, tail or low-count row is proved
for the Steklov operator of the tetrahedron or for any actual coupling; the family is a test case,
not a model of the spectrum; that the paper's `E`, `Emod` equal the smoothed counts is not proved;
no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and Theorem 1.3 / 11.1
remain conditional on named inputs.
-/

namespace SteklovAudit.H5SmoothedColAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5MissingMass SteklovAudit.H5DiffCount SteklovAudit.H5SmoothedIdent

/-- At cutoff `L`: empty true spectrum, `⌈L⌉₊` model eigenvalues at `0`, `J = 0`. -/
noncomputable def smColD (L : ℝ) : Data (Fin 0) (Fin ⌈L⌉₊) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 0

/-- **G45.** The row missing mass of `smColD L` is `0`. -/
theorem smCol_rowMass_zero (L : ℝ) :
    ∑ i, (1 - ∑ j, (smColD L).J i j ^ 2) = 0 := by
  first | exact Fin.sum_univ_zero _ | simp

/-- **G45.** The row-side rows hold for `smColD` with `m1 = 0`, and `m1 = 0` is `o(L)`. -/
theorem smCol_rowMiss_zero :
    (∀ ε γ L : ℝ, ∑ i, (1 - ∑ j, (smColD L).J i j ^ 2) ≤ ((fun _ _ _ => (0 : ℝ)) : ℝ → ℝ → ℝ → ℝ) ε γ L) ∧
    (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      ((fun _ _ _ => (0 : ℝ)) : ℝ → ℝ → ℝ → ℝ) ε γ L ≤ η * L) := by
  refine ⟨fun ε γ L => (smCol_rowMass_zero L).le, fun _ _ _ _ η hη => ⟨0, fun L hL => ?_⟩⟩
  show (0 : ℝ) ≤ η * L
  exact mul_nonneg hη.le hL

/-- **G45.** The column missing mass of `smColD L` is `⌈L⌉₊`. -/
theorem smCol_colMass (L : ℝ) :
    ∑ j, (1 - ∑ i, (smColD L).J i j ^ 2) = (⌈L⌉₊ : ℝ) := by
  have h0 : ∀ j : Fin ⌈L⌉₊, (1 - ∑ i : Fin 0, (smColD L).J i j ^ 2) = 1 := fun j => by
    first | rw [Fin.sum_univ_zero, sub_zero] | simp
  first
    | rw [Finset.sum_congr rfl (fun j _ => h0 j), SteklovAudit.H5CountAudit.const_sum_fin, mul_one]
    | simp [h0]

/-- **G45.** For `smColD` the column missing-mass row forces `m2 ≥ ⌈L⌉₊`, so `m2Vanish` fails. -/
theorem smoothed_colMiss_forces (m2 : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ ε γ L : ℝ, ∑ j, (1 - ∑ i, (smColD L).J i j ^ 2) ≤ m2 ε γ L) :
    (∀ ε γ L : ℝ, (⌈L⌉₊ : ℝ) ≤ m2 ε γ L) ∧
    ¬ (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      m2 ε γ L ≤ η * L) := by
  have hge : ∀ ε γ L : ℝ, (⌈L⌉₊ : ℝ) ≤ m2 ε γ L := fun ε γ L => by
    have h1 := h ε γ L
    rw [smCol_colMass] at h1
    exact h1
  refine ⟨hge, fun hv => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hv 1 1 one_pos one_pos (1 / 2) (by norm_num)
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 := hge 1 1 (max L₀ 1)
  have hc : max L₀ 1 ≤ (⌈max L₀ 1⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- The smoothed true count of `smColD` is `0`. -/
theorem smCol_E (L : ℝ) : ∑ i, arctanProfile.φ ((smColD L).a i - L) = 0 := by
  first | exact Fin.sum_univ_zero _ | simp

/-- The smoothed model count of `smColD`. -/
theorem smCol_Emod (L : ℝ) :
    ∑ j, arctanProfile.φ ((smColD L).b j - L) = (⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L) := by
  show ∑ _j : Fin ⌈L⌉₊, arctanProfile.φ (0 - L) = _
  exact SteklovAudit.H5CountAudit.const_sum_fin _ _

/-- **G45.** The smoothed counts of `smColD` violate the H5b target. -/
theorem smCol_not_target :
    ¬ H5bTarget (fun _ _ L => ∑ i, arctanProfile.φ ((smColD L).a i - L))
      (fun _ _ L => ∑ j, arctanProfile.φ ((smColD L).b j - L)) := by
  intro h
  apply SteklovAudit.H5DiffAudit.ceil_not_target
  intro ε γ hε hγ η hη
  obtain ⟨L₀, hL₀⟩ := h ε γ hε hγ η hη
  refine ⟨L₀, fun L hL => ?_⟩
  have h1 : |∑ i, arctanProfile.φ ((smColD L).a i - L) -
      ∑ j, arctanProfile.φ ((smColD L).b j - L)| ≤ η * L := hL₀ L hL
  rw [smCol_E, smCol_Emod, abs_sub_comm] at h1
  show |(⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L) - 0| ≤ η * L
  exact h1

/-- **G45.** No `H5bSmoothedInputs` has the column missing mass of `smColD`, although that family
meets the row-side missing-mass rows with `m1 = 0`. -/
theorem smoothed_needs_colMass :
    ¬ ∃ W : H5bSmoothedInputs, ∀ ε γ L : ℝ,
      ∑ j, (1 - ∑ i, (W.D ε γ L).J i j ^ 2) = ∑ j, (1 - ∑ i, (smColD L).J i j ^ 2) := by
  rintro ⟨W, hW⟩
  exact (smoothed_colMiss_forces W.m2
    (fun ε γ L => (hW ε γ L).symm.le.trans (W.colMiss ε γ L))).2 W.m2Vanish

end SteklovAudit.H5SmoothedColAudit
