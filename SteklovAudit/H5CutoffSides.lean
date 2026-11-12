import Mathlib

/-!
# G18: the cutoff row split into a true side and a model side

Roadmap item G18. The cutoff row of `H5bPaperInputs` (G16) compares `E - Emod` with the double sum
`∑ i, ∑ j, (φ (a i - L) - φ (b j - L)) * J i j ^ 2`. With row masses `r i = ∑ j, J i j ^ 2` and
column masses `c j = ∑ i, J i j ^ 2`, the double sum splits (`double_sum_split`) into a trace over
the true eigenvalues `a` weighted by `r` minus a trace over the model eigenvalues `b` weighted by `c`.
Hence (`cutoff_of_sides`) a true-side bound `|E - ∑ i, φ (a i - L) * r i| ≤ d1` and a model-side bound
`|Emod - ∑ j, φ (b j - L) * c j| ≤ d2` give the cutoff inequality with `disc = d1 + d2`, and
(`discVanish_of_sides`) the `discVanish` condition passes to `d1 + d2`.

The statements are over arbitrary finite index types, so they apply verbatim to the
`Data (Fin nA) (Fin nB)` of G16.

What this file does NOT prove: neither side bound is proved for the Steklov operator of the
tetrahedron (or for any concrete operator); no Dirichlet-to-Neumann operator is constructed; the
cutoff row, (7.29), every [H…] input and Theorem 1.3 / 11.1 remain conditional on named inputs.
-/

namespace SteklovAudit.H5CutoffSides

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **G18.** The double sum of the cutoff row splits into a row-weighted trace minus a
column-weighted trace. -/
theorem double_sum_split (f : ι → ℝ) (g : κ → ℝ) (J : ι → κ → ℝ) :
    ∑ i, ∑ j, (f i - g j) * J i j ^ 2
      = ∑ i, f i * (∑ j, J i j ^ 2) - ∑ j, g j * (∑ i, J i j ^ 2) := by
  have h1 : ∑ i, ∑ j, f i * J i j ^ 2 = ∑ i, f i * (∑ j, J i j ^ 2) := by
    simp only [Finset.mul_sum]
  have h2 : ∑ i, ∑ j, g j * J i j ^ 2 = ∑ j, g j * (∑ i, J i j ^ 2) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  calc ∑ i, ∑ j, (f i - g j) * J i j ^ 2
      = ∑ i, ∑ j, (f i * J i j ^ 2 - g j * J i j ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, f i * J i j ^ 2 - ∑ i, ∑ j, g j * J i j ^ 2 := by
        simp only [Finset.sum_sub_distrib]
    _ = ∑ i, f i * (∑ j, J i j ^ 2) - ∑ j, g j * (∑ i, J i j ^ 2) := by
        rw [h1, h2]

/-- **G18.** A true-side bound and a model-side bound give the G16 cutoff inequality with
`disc = d1 + d2`. -/
theorem cutoff_of_sides (φ : ℝ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (J : ι → κ → ℝ)
    (L E Emod d1 d2 : ℝ)
    (h1 : |E - ∑ i, φ (a i - L) * (∑ j, J i j ^ 2)| ≤ d1)
    (h2 : |Emod - ∑ j, φ (b j - L) * (∑ i, J i j ^ 2)| ≤ d2) :
    |(E - Emod) - ∑ i, ∑ j, (φ (a i - L) - φ (b j - L)) * J i j ^ 2| ≤ d1 + d2 := by
  have key : ∑ i, ∑ j, (φ (a i - L) - φ (b j - L)) * J i j ^ 2
      = ∑ i, φ (a i - L) * (∑ j, J i j ^ 2) - ∑ j, φ (b j - L) * (∑ i, J i j ^ 2) :=
    double_sum_split (fun i => φ (a i - L)) (fun j => φ (b j - L)) J
  rw [key]
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- **G18.** If `d1` and `d2` each vanish relative to `L` (the `discVanish` form of G16), so does
`d1 + d2`. -/
theorem discVanish_of_sides (d1 d2 : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      d1 ε γ L ≤ η * L)
    (h2 : ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      d2 ε γ L ≤ η * L) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L, L₀ ≤ L →
      d1 ε γ L + d2 ε γ L ≤ η * L := by
  intro ε γ hε hγ η hη
  obtain ⟨L1, hL1⟩ := h1 ε γ hε hγ (η / 2) (by positivity)
  obtain ⟨L2, hL2⟩ := h2 ε γ hε hγ (η / 2) (by positivity)
  refine ⟨max L1 L2, fun L hL => ?_⟩
  have a1 := hL1 L (le_trans (le_max_left _ _) hL)
  have a2 := hL2 L (le_trans (le_max_right _ _) hL)
  have e : η / 2 * L + η / 2 * L = η * L := by ring
  linarith

end SteklovAudit.H5CutoffSides
