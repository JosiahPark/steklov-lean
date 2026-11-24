import Mathlib
import SteklovAudit.ModelEdgeLawGammaFamily

/-!
# Weighted to unweighted edge count (roadmap item G154)

G152 recorded a finding: with a single `γ`-independent count `N`, the per-`γ` laws force the main terms
for different cutoffs to agree up to `o(L)`, while the paper's localized count is weighted by a
`γ`-dependent angular cutoff. This file states the passage from the weighted counts `Nγ` to the
unweighted count `N` as an explicit named input, `|N L − Nγ L| ≤ C γ L`, and proves the scalar
reductions around it. "`o(L)`" is the `η`-form `∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L`.

* `main_terms_agree`: two main terms for the same count agree up to `o(L)`.
* `unweighted_of_weighted`: weighted laws `Nγ − mγ = o(L)`, the weighting error `|N − Nγ| ≤ C γ L`
  and `|mγ − main| ≤ C' γ L` give `N − main = o(L)` (via `edge_law_of_gamma_main`).
* `weighted_gap_must_shrink`: a weighting error that does not shrink with `γ` (a `γ`-independent `1 · L`)
  fits the hypothesis shape for `N L = L`, `Nγ = mγ = main = 0`, but `N − main` is not `o(L)`.

What this file does NOT prove: the bound `|N − Nγ| ≤ C γ L` for the paper's weighted count, the
weighted laws themselves for the actual wedge or tetrahedron Dirichlet-to-Neumann operator,
(7.29), (7.38)/(7.45), (9.1), (11.3), H5, or Theorem 1.3 / 11.1. Everything here is real analysis of
scalar functions; every analytic input is an explicit hypothesis.
-/

namespace SteklovAudit.WeightedToUnweighted

open Filter

/-- **G154.** Two main terms for the same count agree up to `o(L)`. -/
theorem main_terms_agree (N m₁ m₂ : ℝ → ℝ)
    (h1 : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |N L - m₁ L| ≤ η * L)
    (h2 : ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |N L - m₂ L| ≤ η * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |m₁ L - m₂ L| ≤ η * L := by
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  filter_upwards [h1 (η / 2) hη2, h2 (η / 2) hη2] with L a b
  rw [abs_le] at a b ⊢
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  constructor <;> linarith

/-- **G154.** Weighted to unweighted: if for every `γ > 0` the weighted count `Nγ` satisfies
`Nγ − mγ = o(L)`, the weighting error obeys eventually `|N L − Nγ L| ≤ C γ L` (named input) and the
main terms obey eventually `|mγ L − main L| ≤ C' γ L` (`C, C' ≥ 0` uniform in `γ`), then
`N − main = o(L)`. -/
theorem unweighted_of_weighted (N main : ℝ → ℝ) (C C' : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h : ∀ γ : ℝ, 0 < γ → ∃ Nγ mγ : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Nγ L - mγ L| ≤ η * L) ∧
        (∀ᶠ L in atTop, |N L - Nγ L| ≤ C * γ * L) ∧
          ∀ᶠ L in atTop, |mγ L - main L| ≤ C' * γ * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |N L - main L| ≤ η * L := by
  apply SteklovAudit.ModelEdgeLawGammaFamily.edge_law_of_gamma_main N main C C' hC hC'
  intro γ hγ
  obtain ⟨Nγ, mγ, hr, h1, h2⟩ := h γ hγ
  refine ⟨mγ, fun L => Nγ L - mγ L, hr, ?_, h2⟩
  filter_upwards [h1] with L hL
  show |N L - mγ L - (Nγ L - mγ L)| ≤ C * γ * L
  have e : N L - mγ L - (Nγ L - mγ L) = N L - Nγ L := by ring
  rw [e]
  exact hL

/-- **G154.** The weighting error must shrink with `γ`: with a `γ`-independent gap `1 · L`, the
hypothesis shape holds for `N L = L`, `Nγ = mγ = main = 0`, but `N − main` is not `o(L)`. -/
theorem weighted_gap_must_shrink :
    (∀ γ : ℝ, 0 < γ → ∃ Nγ mγ : ℝ → ℝ,
      (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Nγ L - mγ L| ≤ η * L) ∧
        (∀ᶠ L in atTop, |L - Nγ L| ≤ 1 * L) ∧
          ∀ᶠ L in atTop, |mγ L - 0| ≤ 1 * γ * L) ∧
      ¬ (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |L - 0| ≤ η * L) := by
  refine ⟨fun γ hγ => ⟨fun _ => 0, fun _ => 0, fun η hη => ?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |(0 : ℝ) - 0| ≤ η * L
    rw [sub_zero, abs_zero]
    exact mul_nonneg hη.le hL
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |L - 0| ≤ 1 * L
    rw [sub_zero, one_mul, abs_of_nonneg hL]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    show |(0 : ℝ) - 0| ≤ 1 * γ * L
    rw [sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_one hγ.le) hL
  · intro hcon
    obtain ⟨L, hL, hL0⟩ := ((hcon (1 / 2) (by norm_num)).and (eventually_gt_atTop (0 : ℝ))).exists
    rw [sub_zero, abs_of_pos hL0] at hL
    linarith

end SteklovAudit.WeightedToUnweighted
