import Mathlib
import SteklovAudit.ModelEdgeLawGammaFree
import SteklovAudit.WeightedToUnweighted

/-!
# The unweighted wedge law from per-`γ` decompositions of the weighted counts (roadmap item G162)

G152 (`ModelEdgeLawGammaFree.model_law_gamma_free`) feeds per-`γ` decompositions (7.44) of ONE
`γ`-independent count into the `γ`-free assembly, and recorded the finding that the paper's localized
count is instead weighted by a `γ`-dependent angular cutoff. G154
(`WeightedToUnweighted.unweighted_of_weighted`) states the passage from weighted counts `Nγ` to the
unweighted count `N` via the named input `|N − Nγ| ≤ C γ L`. This file joins the two: the
decomposition (7.44) is applied to each WEIGHTED count `Nγ`, and the weighting error then gives the
unweighted law. "`o(L)`" is the `η`-form `∀ η > 0, ∀ᶠ L in atTop, |r L| ≤ η * L`.

* `weighted_law_of_decomp`: `GammaDecomp ι Nγ main C' γ` gives a main term
  `mγ L = L²/(4π) I + c Q L` with `Nγ − mγ = o(L)` and `|mγ − main| ≤ C' γ L` eventually.
* `unweighted_model_law`: if for every `γ > 0` some weighted count `Nγ` has a decomposition
  (`GammaDecomp`) and `|N − Nγ| ≤ C γ L` eventually (`C, C' ≥ 0` uniform in `γ`), then
  `N − main = o(L)`.

What this file does NOT prove: the weighting error `|N − Nγ| ≤ C γ L` for the paper's weighted count,
any hypothesis of (7.44) (the trace-ideal bound (7.39), the spectral shift formula, (7.41)–(7.44)) for
the actual wedge Dirichlet-to-Neumann operator, the bound `|mγ − main| ≤ C' γ L` for the `θ_γ`
integrals, (7.38)/(7.45), (7.29), H5, or Theorem 1.3 / 11.1. Every analytic input is a named
hypothesis; everything here is real analysis of scalar functions.
-/

namespace SteklovAudit.WeightedModelLaw

open Filter Asymptotics

/-- **G162.** A per-`γ` decomposition (7.44) of a weighted count `Nγ` gives its `o(L)` law against
`mγ L = L²/(4π) I + c Q L`, together with the main-term bound `|mγ − main| ≤ C' γ L`. -/
theorem weighted_law_of_decomp (ι : Type*) (Nγ main : ℝ → ℝ) (C' γ : ℝ)
    (hd : SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp ι Nγ main C' γ) :
    ∃ mγ : ℝ → ℝ, (∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Nγ L - mγ L| ≤ η * L) ∧
      ∀ᶠ L in atTop, |mγ L - main L| ≤ C' * γ * L := by
  first
    | unfold SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp at hd
    | simp only [SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp] at hd
    | delta SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp at hd
  obtain ⟨s, Nf, P, G, A, c, Q, I, hdiff, hflat, hP, hG, hA, hm⟩ := hd
  have hlaw := SteklovAudit.ModelEdgeLawReduction.model_law_of_decomposition s Nγ Nf P G A c Q I
    hdiff hflat hP hG hA
  refine ⟨fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L, ?_, ?_⟩
  · exact SteklovAudit.ModelEdgeLawGammaFree.eta_of_isLittleO _ hlaw
  · first
      | exact hm
      | (filter_upwards [hm] with L hL; exact hL)

/-- **G162.** Unweighted edge law from weighted decompositions: if for every `γ > 0` some weighted
count `Nγ` satisfies `GammaDecomp ι Nγ main C' γ` and the weighting error obeys eventually
`|N L − Nγ L| ≤ C γ L` (named input), with `C, C' ≥ 0` uniform in `γ`, then `N − main = o(L)`. -/
theorem unweighted_model_law (ι : Type*) (N main : ℝ → ℝ) (C C' : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h : ∀ γ : ℝ, 0 < γ → ∃ Nγ : ℝ → ℝ,
      SteklovAudit.ModelEdgeLawGammaFree.GammaDecomp ι Nγ main C' γ ∧
        ∀ᶠ L in atTop, |N L - Nγ L| ≤ C * γ * L) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |N L - main L| ≤ η * L := by
  apply SteklovAudit.WeightedToUnweighted.unweighted_of_weighted N main C C' hC hC'
  intro γ hγ
  obtain ⟨Nγ, hd, hgap⟩ := h γ hγ
  obtain ⟨mγ, hr, hm⟩ := weighted_law_of_decomp ι Nγ main C' γ hd
  exact ⟨Nγ, mγ, hr, hgap, hm⟩

end SteklovAudit.WeightedModelLaw
