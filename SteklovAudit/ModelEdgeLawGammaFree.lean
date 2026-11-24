import Mathlib
import SteklovAudit.ModelEdgeLawReduction
import SteklovAudit.ModelEdgeLawGammaFamily

/-!
# Removing the cutoff `γ` from the (7.38) assembly (roadmap item G152)

`ModelEdgeLawReduction.model_law_of_decomposition` (G134) assembles the fixed-time model law (7.38) for
ONE fixed angular cutoff `γ`: from the decomposition (7.44) it gives
`N_wedge = L²/(4π) I + c Q L + o(L)`, where in the paper `I = ∫ q² θ_γ² dS` depends on `γ`.
This file removes `γ`: if for every `γ > 0` the hypotheses of `model_law_of_decomposition` hold
(with data that may depend on `γ`), and the resulting main term `mγ L = L²/(4π) I + c Q L` is within
`C' γ L` of a fixed limit main term `main` (`C' ≥ 0` uniform in `γ`), then `N_wedge − main = o(L)`
in the `η`-form `∀ η > 0, ∀ᶠ L in atTop, |·| ≤ η * L`.

* `eta_of_isLittleO`: `Asymptotics.IsLittleO` against `L` gives the `η`-form.
* `GammaDecomp`: the per-`γ` hypotheses of `model_law_of_decomposition` plus the `C' γ L` bound.
* `model_law_gamma_free`: the assembly, via `ModelEdgeLawGammaFamily.edge_law_of_gamma_main` with
  `C := 0` and remainder `r := N_wedge − mγ`.
* `model_law_gamma_free_nonvacuous`, `model_law_gamma_free_example`: the hypotheses hold (constant
  in `γ`, reusing the data of `model_law_nonvacuous`) and the theorem applies.

Remark (not proved here): `N_wedge` is a single `γ`-independent function in this statement, so the
per-`γ` laws force the main terms for two cutoffs to agree up to `o(L)`. In the paper the weighted
count `N^S_{qθ_γ,α₀}` itself depends on `γ`; the passage from the `γ`-weighted counts to the
unweighted one is a separate input.

What this file does NOT prove: any hypothesis of `model_law_of_decomposition` for the actual wedge
operator (the trace-ideal bound (7.39), the spectral shift formula, (7.41)–(7.44)), the bound
`|mγ − main| ≤ C' γ L` for the `θ_γ` integrals, (7.38)/(7.45) for the actual operator, (7.29), H5,
or Theorem 1.3 / 11.1. Every analytic input is a named hypothesis.
-/

namespace SteklovAudit.ModelEdgeLawGammaFree

open Filter Asymptotics

/-- **G152.** `f = o(L)` (Landau form) implies the `η`-form `∀ η > 0, ∀ᶠ L, |f L| ≤ η * L`. -/
theorem eta_of_isLittleO (f : ℝ → ℝ) (h : f =o[atTop] (fun L : ℝ => L)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |f L| ≤ η * L := by
  intro η hη
  have h1 : ∀ᶠ L in atTop, ‖f L‖ ≤ η * ‖L‖ := by
    first
      | exact h.def hη
      | exact (h.bound hη).bound
      | exact Asymptotics.IsBigOWith.bound (h.bound hη)
  filter_upwards [h1, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0] at hL
  exact hL

/-- **G152.** The per-`γ` input: the hypotheses of `model_law_of_decomposition` (finite annulus family
`s`, flat count `Nf`, smoothed ramp `P`, far term `G`, annulus terms `A`, constants `c Q I`, all allowed
to depend on `γ`), together with `|mγ − main| ≤ C' γ L` eventually, where
`mγ L = L²/(4π) I + c Q L`. -/
def GammaDecomp (ι : Type*) (Nw main : ℝ → ℝ) (C' γ : ℝ) : Prop :=
  ∃ (s : Finset ι) (Nf P G : ℝ → ℝ) (A : ι → ℝ → ℝ) (c Q I : ℝ),
    (∀ L, Nw L - Nf L = c * Q * P L - G L - ∑ i ∈ s, A i L) ∧
    ((fun L => Nf L - L ^ 2 / (4 * Real.pi) * I) =o[atTop] (fun L : ℝ => L)) ∧
    ((fun L => P L - L) =o[atTop] (fun L : ℝ => L)) ∧
    (G =o[atTop] (fun L : ℝ => L)) ∧
    (∀ i ∈ s, A i =o[atTop] (fun L : ℝ => L)) ∧
    ∀ᶠ L in atTop, |(L ^ 2 / (4 * Real.pi) * I + c * Q * L) - main L| ≤ C' * γ * L

/-- **G152.** `γ`-free (7.38) assembly: if `GammaDecomp` holds for every `γ > 0` with `C' ≥ 0`
uniform in `γ`, then `N_wedge − main = o(L)` in `η`-form. -/
theorem model_law_gamma_free (ι : Type*) (Nw main : ℝ → ℝ) (C' : ℝ) (hC' : 0 ≤ C')
    (h : ∀ γ : ℝ, 0 < γ → GammaDecomp ι Nw main C' γ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop, |Nw L - main L| ≤ η * L := by
  apply SteklovAudit.ModelEdgeLawGammaFamily.edge_law_of_gamma_main Nw main 0 C' le_rfl hC'
  intro γ hγ
  have hd := h γ hγ
  first
    | unfold GammaDecomp at hd
    | simp only [GammaDecomp] at hd
    | delta GammaDecomp at hd
  obtain ⟨s, Nf, P, G, A, c, Q, I, hdiff, hflat, hP, hG, hA, hm⟩ := hd
  have hlaw := SteklovAudit.ModelEdgeLawReduction.model_law_of_decomposition s Nw Nf P G A c Q I
    hdiff hflat hP hG hA
  refine ⟨fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L,
    fun L => Nw L - (L ^ 2 / (4 * Real.pi) * I + c * Q * L), ?_, ?_, hm⟩
  · exact eta_of_isLittleO _ hlaw
  · filter_upwards with L
    first
      | simp
      | (beta_reduce; rw [sub_self, abs_zero]; exact le_of_eq (by ring))

/-- **G152.** Non-vacuity: with `Nw = main = L²/(4π) I + c Q L`, the `γ`-constant data of
`model_law_nonvacuous` (no annuli, exact flat count, exact ramp, no far term) satisfy `GammaDecomp`
for every `γ > 0`, with `C' = 0`. -/
theorem model_law_gamma_free_nonvacuous (c Q I : ℝ) :
    ∀ γ : ℝ, 0 < γ → GammaDecomp Unit (fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L)
      (fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L) 0 γ := by
  intro γ _
  first
    | unfold GammaDecomp
    | simp only [GammaDecomp]
    | delta GammaDecomp
  refine ⟨∅, fun L => L ^ 2 / (4 * Real.pi) * I, fun L => L, fun _ => 0, fun _ _ => 0, c, Q, I,
    fun L => by simp, ?_, ?_, isLittleO_zero _ _, fun i hi => by simp at hi, ?_⟩
  · simpa using (isLittleO_zero (fun L : ℝ => L) atTop)
  · simpa using (isLittleO_zero (fun L : ℝ => L) atTop)
  · filter_upwards with L
    simp

/-- **G152.** `model_law_gamma_free` applies to the non-vacuity instance. -/
theorem model_law_gamma_free_example (c Q I : ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ L in atTop,
      |(L ^ 2 / (4 * Real.pi) * I + c * Q * L) - (L ^ 2 / (4 * Real.pi) * I + c * Q * L)| ≤
        η * L :=
  model_law_gamma_free Unit (fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L)
    (fun L => L ^ 2 / (4 * Real.pi) * I + c * Q * L) 0 le_rfl (model_law_gamma_free_nonvacuous c Q I)

end SteklovAudit.ModelEdgeLawGammaFree
