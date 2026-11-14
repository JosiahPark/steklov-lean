import Mathlib
import SteklovAudit.H5SmoothedIdent
import SteklovAudit.H5CountAudit
import SteklovAudit.H5DiffAudit

/-!
# G41: on the smoothed-identification route the missing-mass rows carry the content

Roadmap item G41. G40 showed that if the paper's `E`, `Emod` are the smoothed counts of the coupled
spectra, the difference row is free and (7.29) needs only the E-free rows of `H5bSmoothedInputs`.
This file checks that those rows are not free: the row missing-mass row carries real content.

* `smCeilD L`: the G25 family (`⌈L⌉₊` true eigenvalues at `0`, no model eigenvalues, `J = 0`).
  `smCeil_rowMass`: its total missing row mass is exactly `⌈L⌉₊`.
* `smoothed_rowMiss_forces`: any `m1` meeting `rowMiss` for this family has `m1 ε γ L ≥ ⌈L⌉₊`,
  so `m1Vanish` fails (tested with `η = 1/2` at `L = max L₀ 1`, `Nat.le_ceil`).
* `smCeil_not_target`: the smoothed counts of this family (`φ = arctan`) violate `H5bTarget`
  (G37's `ceil_not_target`).
* `smoothed_needs_mass`: the above, and no `H5bSmoothedInputs` has the missing row mass of this
  family (in particular none has its data).

F table text: on the smoothed-identification route the open content of (7.29) is the missing-mass
(completeness) rows `rowMiss`/`m1Vanish` and `colMiss`/`m2Vanish`.

What this file does NOT prove: no missing-mass, Bessel, count, defect, tail or low-count row is proved
for the Steklov operator of the tetrahedron or for any actual coupling; the G25 family is a test
case, not a model of the spectrum; that the paper's `E`, `Emod` equal the smoothed counts is not
proved; no Dirichlet-to-Neumann operator is constructed; (7.29), every [H…] input and
Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5SmoothedAudit

open Finset
open SteklovAudit SteklovAudit.AbstractTransfer SteklovAudit.H5Compare
open SteklovAudit.H5WeakRows SteklovAudit.H5PaperRows SteklovAudit.H5WeakAudit
open SteklovAudit.H5WindowProfile SteklovAudit.H5WindowWitness
open SteklovAudit.H5MissingMass SteklovAudit.H5DiffCount SteklovAudit.H5SmoothedIdent

/-- The G25 family at cutoff `L`: `⌈L⌉₊` true eigenvalues at `0`, empty model spectrum, `J = 0`. -/
noncomputable def smCeilD (L : ℝ) : Data (Fin ⌈L⌉₊) (Fin 0) where
  a := fun _ => 0
  b := fun _ => 0
  J := fun _ _ => 0

/-- **G41.** The total missing row mass of the G25 family is `⌈L⌉₊`. -/
theorem smCeil_rowMass (L : ℝ) :
    ∑ i, (1 - ∑ j, (smCeilD L).J i j ^ 2) = (⌈L⌉₊ : ℝ) := by
  have h0 : ∀ i : Fin ⌈L⌉₊, (1 - ∑ j : Fin 0, (smCeilD L).J i j ^ 2) = 1 := fun i => by
    first | rw [Fin.sum_univ_zero, sub_zero] | simp
  first
    | rw [Finset.sum_congr rfl (fun i _ => h0 i), SteklovAudit.H5CountAudit.const_sum_fin, mul_one]
    | simp [h0]

/-- **G41.** For the G25 family the row missing-mass row forces `m1 ≥ ⌈L⌉₊`, so `m1Vanish` fails. -/
theorem smoothed_rowMiss_forces (m1 : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ ε γ L : ℝ, ∑ i, (1 - ∑ j, (smCeilD L).J i j ^ 2) ≤ m1 ε γ L) :
    (∀ ε γ L : ℝ, (⌈L⌉₊ : ℝ) ≤ m1 ε γ L) ∧
    ¬ (∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      m1 ε γ L ≤ η * L) := by
  have hge : ∀ ε γ L : ℝ, (⌈L⌉₊ : ℝ) ≤ m1 ε γ L := fun ε γ L => by
    have h1 := h ε γ L
    rw [smCeil_rowMass] at h1
    exact h1
  refine ⟨hge, fun hv => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hv 1 1 one_pos one_pos (1 / 2) (by norm_num)
  have hL1 : (1 : ℝ) ≤ max L₀ 1 := le_max_right _ _
  have h1 := hL₀ (max L₀ 1) (le_max_left _ _)
  have h2 := hge 1 1 (max L₀ 1)
  have hc : max L₀ 1 ≤ (⌈max L₀ 1⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-- The smoothed true count of the G25 family. -/
theorem smCeil_E (L : ℝ) :
    ∑ i, arctanProfile.φ ((smCeilD L).a i - L) = (⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L) := by
  show ∑ _i : Fin ⌈L⌉₊, arctanProfile.φ (0 - L) = _
  exact SteklovAudit.H5CountAudit.const_sum_fin _ _

/-- The smoothed model count of the G25 family is `0`. -/
theorem smCeil_Emod (L : ℝ) : ∑ j, arctanProfile.φ ((smCeilD L).b j - L) = 0 := by
  first | exact Fin.sum_univ_zero _ | simp

/-- **G41.** The smoothed counts of the G25 family violate the H5b target. -/
theorem smCeil_not_target :
    ¬ H5bTarget (fun _ _ L => ∑ i, arctanProfile.φ ((smCeilD L).a i - L))
      (fun _ _ L => ∑ j, arctanProfile.φ ((smCeilD L).b j - L)) := by
  intro h
  apply SteklovAudit.H5DiffAudit.ceil_not_target
  intro ε γ hε hγ η hη
  obtain ⟨L₀, hL₀⟩ := h ε γ hε hγ η hη
  refine ⟨L₀, fun L hL => ?_⟩
  have h1 : |∑ i, arctanProfile.φ ((smCeilD L).a i - L) -
      ∑ j, arctanProfile.φ ((smCeilD L).b j - L)| ≤ η * L := hL₀ L hL
  rw [smCeil_E, smCeil_Emod] at h1
  show |(⌈L⌉₊ : ℝ) * arctanProfile.φ (0 - L) - 0| ≤ η * L
  exact h1

/-- **G41.** On the smoothed-identification route the missing-mass rows carry real content: for the
G25 family the smoothed counts violate `H5bTarget`, and no `H5bSmoothedInputs` has the missing row
mass of that family (so none has its data): `rowMiss` forces `m1 ≥ ⌈L⌉₊` and `m1Vanish` fails. -/
theorem smoothed_needs_mass :
    ¬ H5bTarget (fun _ _ L => ∑ i, arctanProfile.φ ((smCeilD L).a i - L))
      (fun _ _ L => ∑ j, arctanProfile.φ ((smCeilD L).b j - L)) ∧
    ¬ ∃ W : H5bSmoothedInputs, ∀ ε γ L : ℝ,
      ∑ i, (1 - ∑ j, (W.D ε γ L).J i j ^ 2) = ∑ i, (1 - ∑ j, (smCeilD L).J i j ^ 2) := by
  refine ⟨smCeil_not_target, ?_⟩
  rintro ⟨W, hW⟩
  exact (smoothed_rowMiss_forces W.m1
    (fun ε γ L => (hW ε γ L).symm.le.trans (W.rowMiss ε γ L))).2 W.m1Vanish

end SteklovAudit.H5SmoothedAudit
